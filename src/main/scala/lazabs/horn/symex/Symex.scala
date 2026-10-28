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

import ap.api.SimpleAPI.ProverStatus
import ap.SimpleAPI
import ap.parser._
import ap.terfor.ConstantTerm
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.theories.{Theory, TheoryCollector}
import lazabs.horn.bottomup.{NormClause, RelationSymbol}
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.Util.Dag
import lazabs.horn.preprocessor.HornPreprocessor.Solution

import collection.mutable.{HashSet => MHashSet, HashMap => MHashMap}

object Symex {
  private[symex] object AC extends ap.util.Debug.ASSERTION_CATEGORY
  class SymexException(msg: String) extends Exception(msg)

  /**
   * The search ended without a verdict (for example a bounded depth
   * is reached). A candidate solution need not satisfy the clauses
   * (e.g., it is a solution up to some depth).
   */
  class InconclusiveException(
      val candidateSolution : Option[() => Solution])
      extends SymexException("search ended without a verdict")

  sealed abstract class FeasibilityCheckResult
  object FeasibilityCheckResult {
    case object Feasible      extends FeasibilityCheckResult
    case object Infeasible    extends FeasibilityCheckResult
    case object BudgetExpired extends FeasibilityCheckResult
    case class  Undecided(status : ProverStatus.Value)
        extends FeasibilityCheckResult
    case object Skipped       extends FeasibilityCheckResult
  }
}

abstract class Symex[CC](iClauses:    Iterable[CC])(
    implicit clause2ConstraintClause: CC => ConstraintClause
) extends ConstraintSimplifier {

  import Symex._

  var printInfo = false
  def printInfo(s : => String, newLine : Boolean = true) : Unit = {
    if (printInfo)
      print(s + (if (newLine) "\n" else ""))
  }

  val theories: Seq[Theory] = {
    val coll = new TheoryCollector
    coll addTheory ap.types.TypeTheory
    for (c <- iClauses)
      c collectTheories coll
    coll.theories
  }

  if (theories.nonEmpty)
    printInfo("Theories: " + (theories mkString ", ") + "\n")

  val preds: Seq[Predicate] =
    (for (c   <- iClauses.iterator;
          lit <- (Iterator single c.head) ++ c.body.iterator;
          p = lit.predicate)
      yield p).toSeq.distinct

  // We keep a prover initialized with all the symbols running, which we will
  // use to check the satisfiability of constraints.
  // Note that the prover must be manually shut down for clean-up.
  implicit val prover: SimpleAPI = SimpleAPI.spawn
  prover.addTheories(theories)
  prover.addRelations(preds)

  // Keeps track of all the terms and adds new symbols to the prover
  // must be initialized after normClauses are generated.
  implicit val symex_sf: SymexSymbolFactory =
    new SymexSymbolFactory(theories, prover)

  val relationSymbols: Map[Predicate, RelationSymbol] =
    (for (p <- preds) yield (p -> RelationSymbol(p))).toMap

  // translate clauses to internal form
  val normClauses: Seq[(NormClause, CC)] = (
    for (c <- iClauses) yield {
      lazabs.GlobalParameters.get.timeoutChecker()
      (NormClause(c, p => relationSymbols(p)), c)
    }
  ).toSeq

  val normClauseToCC: Map[NormClause, CC] = normClauses.toMap

  val clausesWithRelationInBody: Map[RelationSymbol, Seq[NormClause]] =
    (for (rel <- relationSymbols.values) yield {
      (rel,
       normClauses.filter(_._1.body.exists(brel => brel._1 == rel)).map(_._1))
    }).toMap

  val clausesWithRelationInHead: Map[RelationSymbol, Seq[NormClause]] =
    (for (rel <- relationSymbols.values) yield {
      (rel, normClauses.filter(_._1.head._1 == rel).map(_._1))
    }).toMap

  val predicatesAndMaxOccurrences: Map[Predicate, Int] = {
    val maxOccs = new MHashMap[Predicate, Int]
    for (pred <- preds)
      maxOccs += ((pred, 0))
    for ((clause, _) <- normClauses) {
      for ((rs, occ) <- clause.body ++ Seq(clause.head))
        if (occ > maxOccs(rs.pred))
          maxOccs(rs.pred) = occ
    }
    maxOccs.toMap
  }

  // this must be done before we can use the symbol factory during resolution
  symex_sf.initialize(predicatesAndMaxOccurrences.toSet)

  def solve(): Either[() => Solution, Dag[(IAtom, CC)]]

  /**
   * Shut-down the engine.
   */
  def shutdown: Unit = {
    prover.shutDown
  }

  val statistics = new SymexStatistics

  val initialBudgetMs  : Long = 2000
  val budgetGrowthRate : Long = 2
  val cheapBudgetMs    : Long = 5

  private val collectCheckTimes = lazabs.GlobalParameters.get.log

  /**
   * Checks the constraint within budgetMs and counts the result. If the
   * constraint does not end the search when feasible, -symStateChecks
   * decides how it is checked.
   */
  protected def checkFeasibilityWithinBudget(
      constraint           : Conjunction,
      endsSearchIfFeasible : Boolean,
      budgetMs             : Long) : FeasibilityCheckResult = {
    import FeasibilityCheckResult._
    import lazabs.GlobalParameters.SymexStateChecks
    val checkBudgetMs =
      if (endsSearchIfFeasible) Some(budgetMs)
      else lazabs.GlobalParameters.get.symexStateChecks match {
        case SymexStateChecks.Full  => Some(budgetMs)
        case SymexStateChecks.Cheap =>
          // use a cheap budget for the first feasibility check
          if (budgetMs == initialBudgetMs) Some(cheapBudgetMs)
          else Some(budgetMs)
        case SymexStateChecks.None  => None
      }
    val checkStart = if (collectCheckTimes) System.nanoTime else 0L
    val checkResult = checkBudgetMs match {
      case Some(millis) => checkFeasibility(constraint, Some(millis))
      case None => if (constraint.isFalse) Infeasible else Skipped
    }
    if (collectCheckTimes)
      statistics.checkNanos += System.nanoTime - checkStart
    statistics.countCheck(checkResult, endsSearchIfFeasible)
    checkResult
  }

  /**
   * The disjunction of the constraints over the arguments of rs at
   * occurrence 0, with their other symbols existentially quantified.
   */
  protected def disjunctionOverArgs(rs          : RelationSymbol,
                                    constraints : Seq[Conjunction])
  : Conjunction = {
    val disjunction = Conjunction.disj(constraints, symex_sf.order)
    val constants = (disjunction.constants -- rs.arguments(0)).toSeq
    symex_sf.reducer(Conjunction.TRUE)(
      Conjunction.quantify(Quantifier.EX, symex_sf.order.sort(constants),
                           disjunction, symex_sf.order))
  }

  // a constraint over the arguments of rs at occurrence 0 as a solution
  protected def solutionFormula(rs         : RelationSymbol,
                                constraint : Conjunction) : IFormula = {
    val argSubst: Map[ConstantTerm, ITerm] =
      (for ((arg, i) <- rs.arguments(0) zipWithIndex)
        yield
          (arg, ap.parser.IExpression.v(i))).toMap // symex_sf.genConstant("_" + i)
    ConstantSubstVisitor(prover.asIFormula(constraint), argSubst)
  }

  private[symex] def checkFeasibility(constraint : Conjunction,
                                      budgetMs   : Option[Long])
    : FeasibilityCheckResult = {
    import FeasibilityCheckResult._
    if (constraint.isTrue) {
      Feasible
    } else if (constraint.isFalse) {
      Infeasible
    } else prover.scope {
      prover.addAssertionPreproc(constraint)
      budgetMs match {
        case Some(millis) =>
          prover.checkSat(block = false)
          prover.getStatus(millis) match {
            case ProverStatus.Running =>
              toFeasibilityCheckResult(prover.stop) match {
                case Undecided(_) => BudgetExpired
                case decided      => decided
              }
            case status => toFeasibilityCheckResult(status)
          }
        case None => toFeasibilityCheckResult(prover.???)
      }
    }
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
   * If `checkResult` is Feasible, the constraint without the conjuncts that
   * share no symbol with `args`, directly or through other conjuncts;
   * otherwise the constraint itself. In a feasible constraint, such
   * conjuncts can be satisfied independently of the rest, so dropping them
   * keeps the solutions over `args`.
   * E.g., x = 0 & c[0:0] = 1 & c <= 9 with args x becomes x = 0.
   */
  protected def withoutConjunctsUnconnectedToArgs(
      constraint  : Conjunction,
      args        : Set[ConstantTerm],
      checkResult : FeasibilityCheckResult) : Conjunction =
    if (checkResult != FeasibilityCheckResult.Feasible ||
        !constraint.quans.isEmpty || (constraint.constants subsetOf args))
      constraint
    else {
      val conjuncts = constraint.iterator.toList
      var connected = args
      var growing = true
      while (growing) {
        growing = false
        for (conjunct <- conjuncts
             if (conjunct.constants exists connected) &&
                !(conjunct.constants subsetOf connected)) {
          connected = connected ++ conjunct.constants
          growing = true
        }
      }
      if (constraint.constants subsetOf connected) constraint
      else Conjunction.conj(conjuncts filter (_.constants subsetOf connected),
                            constraint.order)
    }
}
