/**
 * Copyright (c) 2022-2026 Zafer Esen, Philipp Ruemmer. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package lazabs.horn.symex

import ap.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
import ap.basetypes.IdealInt
import ap.terfor.{ConstantTerm, OneTerm, TerForConvenience}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.theories.bitvectors.ModuloArithmetic.ModSort
import ap.types.{Sort, SortedConstantTerm}
import lazabs.horn.bottomup.NormClause

import scala.collection.mutable.{HashMap => MHashMap}

sealed abstract class FeasibilityCheckResult
object FeasibilityCheckResult {
  case object Feasible      extends FeasibilityCheckResult
  case object Infeasible    extends FeasibilityCheckResult
  case object BudgetExpired extends FeasibilityCheckResult
  case class  Undecided(status : ProverStatus.Value)
      extends FeasibilityCheckResult
  case object Skipped       extends FeasibilityCheckResult
}

/**
 * Exponential backoff for fruitless checks: after n fruitless checks in a
 * row with a key, the next 2^n - 1 checks with it are skipped.
 */
class CheckBackoff[K] {
  private val fruitlessChecksOf = new MHashMap[K, Int]
  private val skipsLeftOf       = new MHashMap[K, Int]
  private val maxGapExponent    = 12

  def isSkipped(key : K) : Boolean = {
    val skipsLeft = skipsLeftOf.getOrElse(key, 0)
    if (skipsLeft > 0)
      skipsLeftOf(key) = skipsLeft - 1
    skipsLeft > 0
  }

  def recordCheck(key : K, fruitless : Boolean) : Unit =
    if (fruitless) {
      val fruitlessChecks = fruitlessChecksOf.getOrElse(key, 0) + 1
      fruitlessChecksOf(key) = fruitlessChecks
      skipsLeftOf(key) = (1 << (fruitlessChecks min maxGapExponent)) - 1
    } else {
      fruitlessChecksOf(key) = 0
      skipsLeftOf(key) = 0
    }
}

/**
 * Feasibility checks of constraints: decided without a prover call where
 * possible, otherwise by the prover within a budget.
 */
class FeasibilityChecker(prover     : SimpleAPI,
                         statistics : SymexStatistics)(
    implicit symex_sf : SymexSymbolFactory) {
  import FeasibilityChecker.ImpliedBounds

  val initialBudgetMs  : Long = 2000
  val budgetGrowthRate : Long = 2

  private val collectCheckTimes = lazabs.GlobalParameters.get.log
  private val stateCheckBackoff = new CheckBackoff[NormClause]

  def checkResolvent(
      constraint           : Conjunction,
      endsSearchIfFeasible : Boolean,
      budgetMs             : Long,
      resolvedClause       : NormClause) : FeasibilityCheckResult = {
    import FeasibilityCheckResult._
    val checkStart = if (collectCheckTimes) System.nanoTime else 0L
    val checkResult =
      if (!endsSearchIfFeasible && !constraint.isFalse &&
          (stateCheckBackoff isSkipped resolvedClause)) Skipped
      else check(constraint, Some(budgetMs))
    checkResult match {
      case Feasible | Infeasible if !endsSearchIfFeasible =>
        // nothing is pruned when the state is found feasible
        stateCheckBackoff.recordCheck(resolvedClause,
                                      fruitless = checkResult == Feasible)
      case _ =>
    }
    if (collectCheckTimes)
      statistics.checkNanos += System.nanoTime - checkStart
    statistics.countCheck(checkResult, endsSearchIfFeasible)
    checkResult
  }

  def check(constraint : Conjunction,
            budgetMs   : Option[Long]) : FeasibilityCheckResult = {
    import FeasibilityCheckResult._
    if (constraint.isTrue) {
      Feasible
    } else if (constraint.isFalse) {
      Infeasible
    } else decidedWithoutProver(constraint) match {
      case Some(result) =>
        statistics.checksDecidedWithoutProver += 1
        result
      case None => prover.scope {
        prover.addAssertionPreproc(constraint)
        prover.checkSat(block = false)
        proverStatusWithin(budgetMs) match {
          case ProverStatus.Running =>
            toFeasibilityCheckResult(prover.stop) match {
              case Undecided(_) => BudgetExpired
              case decided      => decided
            }
          case status => toFeasibilityCheckResult(status)
        }
      }
    }
  }

  private def decidedWithoutProver(constraint : Conjunction)
    : Option[FeasibilityCheckResult] =
    if (isTrueAtGuessedPoint(constraint)) Some(FeasibilityCheckResult.Feasible)
    else None

  private val bodyBoundsOf = new MHashMap[NormClause, Seq[ImpliedBounds]]
  private val headBoundsOf = new MHashMap[NormClause, ImpliedBounds]

  /**
   * True if the constraint of the resolvent of a resolution choice is false,
   * for instance due to disjoint bounds.
   * E.g., goal atom p(x) with x >= 6 and clause p(y) :- y <= 5.
   * A state atom is given as a constraint and the arguments of the atom in it. 
   * The state atoms are resolved with the body atoms of the clause, in order, 
   * or with its head.
   */
  def isInfeasibleChoiceOnBody(
      clause     : NormClause,
      stateAtoms : Seq[(Conjunction, Seq[ConstantTerm])]) : Boolean =
    isInfeasibleChoice(
      bodyBoundsOf.getOrElseUpdate(
        clause,
        for (syms <- clause.bodySyms)
          yield ImpliedBounds(clause.constraint, syms)),
      stateAtoms)

  def isInfeasibleChoiceOnHead(
      clause    : NormClause,
      stateAtom : (Conjunction, Seq[ConstantTerm])) : Boolean =
    isInfeasibleChoice(
      Seq(headBoundsOf.getOrElseUpdate(
            clause, ImpliedBounds(clause.constraint, clause.headSyms))),
      Seq(stateAtom))

  private def isInfeasibleChoice(
      clauseAtomBounds : Seq[ImpliedBounds],
      stateAtoms       : Seq[(Conjunction, Seq[ConstantTerm])]) : Boolean = {
    val isInfeasible = (clauseAtomBounds zip stateAtoms) exists {
      case (bounds, (constraint, args)) =>
        bounds disjointFrom ImpliedBounds(constraint, args)
    }
    if (isInfeasible)
      statistics.choicesPrunedWithoutProver += 1
    isInfeasible
  }

  private val proverPollIntervalMs = 100L

  /**
   * Waits for the result of `checkSat(block = false)`, Running if the
   * budget runs out first. The timeout checker is called between polls, so
   * that the run can time out or be stopped during a long check.
   */
  def proverStatusWithin(budgetMs : Option[Long])
    : ProverStatus.Value = {
    val deadline = budgetMs map (System.currentTimeMillis + _)
    def nextPollMs = deadline match {
      case Some(time) => (time - System.currentTimeMillis) min
                           proverPollIntervalMs
      case None       => proverPollIntervalMs
    }
    var status = prover.getStatus(nextPollMs)
    while (status == ProverStatus.Running && nextPollMs > 0) {
      try {
        lazabs.GlobalParameters.get.timeoutChecker()
      } catch {
        case e : Exception =>
          prover.stop
          throw e
      }
      status = prover.getStatus(nextPollMs)
    }
    status
  }

  private def toFeasibilityCheckResult(status : ProverStatus.Value)
    : FeasibilityCheckResult = {
    import FeasibilityCheckResult._
    status match {
      case ProverStatus.Valid | ProverStatus.Sat     => Feasible
      case ProverStatus.Invalid | ProverStatus.Unsat => Infeasible
      case _                                         => Undecided(status)
    }
  }

  /**
   * True if the constraint is already true at a guessed point. 
   * The guess is done by setting each constant to an implied bound, 
   * then the leading constant of each equation is solved for by back-substitution.
   * E.g., for x = y + 1 & y >= 3 & z <= x with x leading: y = 3, z = 0 and x = 4.
   */
  private def isTrueAtGuessedPoint(constraint : Conjunction) : Boolean = {
    val constants = constraint.constants.toIndexedSeq
    val ranges = constants map (c => sortRange(SortedConstantTerm sortOf c))
    if (ranges exists (_.isEmpty)) {
      false
    } else {
      val bounds = ImpliedBounds(constraint, constants)
      val point = new MHashMap[ConstantTerm, IdealInt]
      for (i <- constants.indices)
        point(constants(i)) = clamp(
          bounds.lower(i) orElse bounds.upper(i) getOrElse IdealInt.ZERO,
          ranges(i).get)
      val eqsInOrder = constraint.arithConj.positiveEqs.toSeq.sortWith {
        (a, b) => constraint.order.compare(a.leadingTerm, b.leadingTerm) < 0
      }
      for (lc <- eqsInOrder) lc.leadingTerm match {
        case lead : ConstantTerm =>
          val rest = lc.pairSeq.foldLeft(IdealInt.ZERO) {
            case (sum, (_, `lead`))              => sum
            case (sum, (coeff, OneTerm))         => sum + coeff
            case (sum, (coeff, c : ConstantTerm)) => sum + coeff * point(c)
            case (sum, _)                        => sum
          }
          if ((rest % lc.leadingCoeff).isZero)
            point(lead) = -(rest / lc.leadingCoeff)
        case _ =>
      }
      val inSorts = constants.indices forall { i =>
        point(constants(i)) == clamp(point(constants(i)), ranges(i).get)
      }
      inSorts && isTrueAt(point, constraint)
    }
  }

  private def isTrueAt(point      : collection.Map[ConstantTerm, IdealInt],
                       constraint : Conjunction) : Boolean = {
    import TerForConvenience._
    implicit val order = symex_sf.order
    val pointEqs = Conjunction.conj(
      for ((c, value) <- point.toSeq) yield c === value, order)
    symex_sf.reducer(pointEqs)(constraint).isTrue
  }

  private def sortRange(sort : Sort)
      : Option[(Option[IdealInt], Option[IdealInt])] = sort match {
    case Sort.Integer | Sort.MultipleValueBool => Some((None, None))
    case Sort.Nat              => Some((Some(IdealInt.ZERO), None))
    case Sort.Interval(lo, hi) => Some((lo, hi))
    case ModSort(lo, hi)       => Some((Some(lo), Some(hi)))
    case Sort.Bool             =>
      Some((Some(IdealInt.ZERO), Some(IdealInt.ONE)))
    case _                     => None
  }

  private def clamp(value : IdealInt,
                    range : (Option[IdealInt], Option[IdealInt])) : IdealInt = {
    val floored = range._1.map(_ max value) getOrElse value
    range._2.map(_ min floored) getOrElse floored
  }
}

object FeasibilityChecker {
  /**
   * Lower and upper bounds of symbols, as read off the equations and
   * inequalities of a constraint without a prover call.
   * E.g., for x >= 2 & x <= 7 & x + y >= 0 over x, y, the bounds of x are
   * 2 and 7, and y has none.
   */
  private class ImpliedBounds private (
      val lower : IndexedSeq[Option[IdealInt]],
      val upper : IndexedSeq[Option[IdealInt]]) {
    // no value lies within both at some position
    def disjointFrom(that : ImpliedBounds) : Boolean =
      lower.indices exists { i =>
        lower(i).exists(l => that.upper(i).exists(l > _)) ||
          that.lower(i).exists(l => upper(i).exists(l > _))
      }
  }

  private object ImpliedBounds {
    def apply(constraint : Conjunction,
              symbols    : Seq[ConstantTerm]) : ImpliedBounds = {
      val definingEqs = constraint.arithConj.positiveEqs.toMap
      val inEqs = constraint.arithConj.inEqs
      val bounds = for (c <- symbols.toIndexedSeq) yield
        if (!(constraint.constants contains c)) {
          (None, None)
        } else definingEqs get c match {
          case Some(lc) if lc.constants.size == 1 =>
            (Some(-lc.constant), Some(-lc.constant))
          case _ =>
            val lc = LinearCombination(c, constraint.order)
            (inEqs.findLowerBound(lc), inEqs.findLowerBound(-lc).map(-_))
        }
      new ImpliedBounds(bounds.map(_._1), bounds.map(_._2))
    }
  }
}
