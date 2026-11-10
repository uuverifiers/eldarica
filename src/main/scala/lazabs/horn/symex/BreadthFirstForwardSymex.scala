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

import ap.util.Combinatorics
import ap.parser.IAtom
import ap.terfor.preds.Predicate
import lazabs.GlobalParameters.SymexChoiceOrder
import lazabs.horn.Util.Dag
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.bottomup.NormClause
import lazabs.horn.preprocessor.HornPreprocessor.Solution

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

/**
 * Implements a breadth-first forward symbolic execution using Symex.
 * @param maxDepth : Search will stop after deriving this many unit clauses
 *                   for a given predicate. Note that setting this value to
 *                   something other than None will always terminate (like
 *                   BMC), and a search cut by the bound ends inconclusive.
 * @param keepDerivations : See [[ForwardSymex]].
 * @param choiceOrder : See [[ResolutionChoiceQueue]].
 */
class BreadthFirstForwardSymex[CC](clauses         : Iterable[CC],
                                   maxDepth        : Option[Int] = None,
                                   keepDerivations : Boolean = true,
                                   choiceOrder     : SymexChoiceOrder.Value =
                                     SymexChoiceOrder.Guided)(
    implicit clause2ConstraintClause:       CC => ConstraintClause)
    extends ForwardSymex(clauses, keepDerivations) {

  import Symex._
  import FeasibilityCheckResult._

  printInfo("Starting breadth-first forward symbolic execution (BFS)...\n")

  // Explore the derived cucs breadth-first, or cheapest choice first under
  // guided choice order. A choice is a clause with one stored cuc per body
  // atom; it is enqueued once, when the newest of its cucs is stored.

  private val choicesQueue =
    new ResolutionChoiceQueue[(NormClause, Seq[UnitClause], Long)](
      choiceOrder)

  private val subsumptionChecker = new SubsumptionChecker[UnitClause](
    subsumptionTestFor,
    new UnionSubsumption(singleAtomConstraint, feasibilityChecker.check))

  private val unfoldCountsOf = new MHashMap[UnitClause, UnfoldCounts]

  private def enqueue(clause    : NormClause,
                      electrons : Seq[UnitClause],
                      budgetMs  : Long) : Unit =
    choicesQueue.enqueue((clause, electrons, budgetMs),
                         guidedCost(clause, electrons))

  private def guidedCost(nucleus   : NormClause,
                         electrons : Seq[UnitClause]) : Long = {
    val headPred = nucleus.head._1.pred
    // none for a goal without body atoms
    val unfoldCounts = UnfoldCounts.none +: electrons.map(unfoldCountsOf)
    // earlier unfoldings of the head predicate on the derivation
    val coveringAncestorCount = unfoldCounts.map(_ countOf headPred).max
    ResolutionChoiceQueue.guidedCost(
      endsSearchIfFeasible = headPred == HornClauses.FALSE,
      constraintSize =
        nucleus.constraint.opCount + electrons.map(_.constraint.opCount).sum,
      largestUnfoldCount =
        unfoldCounts.map(_.largestAfterUnfolding(headPred)).max,
      distanceFromStart = heightFromFacts(headPred)) +
      10000L * coveringAncestorCount
  }

  /**
   * The least height of a derivation of each predicate from the facts, 1
   * for the predicate of a fact.
   */
  private lazy val heightFromFacts : Map[Predicate, Int] = {
    var height = Map[Predicate, Int]()
    var changed = true
    while (changed) {
      changed = false
      for ((clause, _) <- normClauses) {
        val bodyHeights = clause.body map (atom => height get atom._1.pred)
        val headPred = clause.head._1.pred
        if (bodyHeights forall (_.isDefined)) {
          val headHeight = (0 +: bodyHeights.map(_.get)).max + 1
          if (height get headPred forall (headHeight < _)) {
            height += (headPred -> headHeight)
            changed = true
          }
        }
      }
    }
    height
  }

  // per clause and body atom, the stored cucs that the body atom can be
  // resolved with, oldest first
  private val resolvableCUCsOf =
    new MHashMap[(NormClause, Int), ArrayBuffer[UnitClause]]

  // a goal without body atoms is a choice without cucs
  for ((clause, _) <- normClauses
       if clause.head._1.pred == HornClauses.FALSE && clause.body.isEmpty)
    enqueue(clause, Nil, feasibilityChecker.initialBudgetMs)

  /*
   * Initialize the search by adding the facts.
   * Each fact corresponds to a source in the search DAG.
   */
  for (fact <- facts) {
    unitClauseDB add (fact, parents = (factToNormClause(fact), Nil))
    unfoldCountsOf(fact) = UnfoldCounts.none.afterUnfolding(fact.rs.pred)
    handleNewUnitClause(fact)
  }

  private def getClausesForResolution
    : Option[(NormClause, Seq[UnitClause], Long)] = {
    if (choicesQueue.isEmpty)
      None
    else {
      maxDepth match {
        case None => Some(choicesQueue.dequeue())
        case Some(depth) =>
          var res : Option[(NormClause, Seq[UnitClause], Long)] = None
          var continue = true
          do {
            val candidate = choicesQueue.dequeue()
            val rs        = candidate._1.head._1
            unitClauseDB.inferred(rs) match {
              // a goal without body atoms is within every depth bound
              case Some(cucs)
                  if cucs.length >= depth && candidate._2.nonEmpty =>
                // this is not a good candidate, continue
                statistics.depthPrunedChoices += 1
              case _ => // this is a good candidate, return
                continue = false
                res = Some(candidate)
            }
          } while (choicesQueue.nonEmpty && continue)
          res
      }
    }
  }

  private val collectStats = lazabs.GlobalParameters.get.log

  override def solve(): Either[() => Solution, () => Dag[(IAtom, CC)]] = {
    val solveStart = System.nanoTime
    var result: Either[() => Solution, () => Dag[(IAtom, CC)]] = null

    // start traversal
    var ind = 0
    try {
      while (result == null) {
        lazabs.GlobalParameters.get.timeoutChecker()
        ind += 1
        printInfo(ind + ".", false)
        getClausesForResolution match {
          case Some((nucleus, electrons, budgetMs)) => {
            val resolutionStart = if (collectStats) System.nanoTime else 0L
            val simplifyBefore  = if (collectStats) simplifier.timeNanos else 0L
            val newElectron = hyperResolve(nucleus, electrons)
            if (collectStats)
              statistics.resolutionNanos +=
                (System.nanoTime - resolutionStart) -
                (simplifier.timeNanos - simplifyBefore)
            printInfo("\t" + nucleus + "\n  +\n\t" + electrons.mkString("\n\t"))
            printInfo("  =\n\t" + newElectron)
            val isGoal =
              (newElectron.rs.pred == HornClauses.FALSE) ||
                (!newElectron.isPositive)
            val isDuplicate = !isGoal && (unitClauseDB isDuplicate newElectron)
            val checkResult =
              if (isDuplicate) Skipped
              else feasibilityChecker.checkResolvent(
                newElectron.constraint, isGoal, budgetMs, nucleus)
            statistics.statesDerived += 1
            val storedElectron =
              if (isGoal) newElectron
              else withoutConjunctsUnconnectedToArgs(newElectron, checkResult)
            if (!(storedElectron eq newElectron))
              statistics.statesWithUnconnectedConjunctsDropped += 1
            if (checkResult == BudgetExpired) {
              // the check gets another turn later with more time, so the
              // rest of the search goes first
              val longerBudgetMs =
                budgetMs * feasibilityChecker.budgetGrowthRate
              printInfo("\n  (Check budget expired, postponed with " +
                        longerBudgetMs + " ms.)")
              enqueue(nucleus, electrons, longerBudgetMs)
            } else if (isGoal && checkResult == Feasible) {
              unitClauseDB.add(newElectron, (nucleus, electrons))
              result = Right(() => buildCounterExample(newElectron))
            } else if (checkResult == Infeasible) {
              printInfo("")
              handleFalseConstraint(nucleus, electrons)
            } else if (isGoal) {
              printInfo("\n  (Check said " + checkResult +
                        ", empty goal left undecided.)")
            } else if (isDuplicate ||
                       (unitClauseDB isDuplicate storedElectron)) {
              printInfo("\n  (Derived clause already exists in the database.)")
              handleForwardSubsumption(nucleus, electrons)
            } else if (subsumptionChecker.isSubsumed(
                         storedElectron,
                         unitClauseDB.inferred(storedElectron.rs).get)) {
              printInfo("subsumed by existing unit clauses.")
              handleForwardSubsumption(nucleus, electrons)
            } else {
              unitClauseDB.add(storedElectron, (nucleus, electrons))
              unfoldCountsOf(storedElectron) =
                electrons.map(unfoldCountsOf).reduce(_ join _)
                  .afterUnfolding(storedElectron.rs.pred)
              printInfo("\n  (Added to database.)\n")
              handleNewUnitClause(storedElectron)
            }
          }
          case None => // nothing left to explore
            printInfo("\t(Search space exhausted.)\n")
            result = resultOfExhaustedSearch
        }
      }
      result
    } finally {
      if (collectStats)
        statistics.printStatistics(
          unitClauseDB.size, unitClauseDB.rejectedDuplicateCount,
          subsumptionChecker, simplifier,
          System.nanoTime - solveStart)
    }
  }


  private def resultOfExhaustedSearch
    : Either[() => Solution, () => Dag[(IAtom, CC)]] =
    if (statistics.undecidedEmptyGoals > 0)
      throw new InconclusiveException(candidateSolution = None)
    else if (statistics.depthPrunedChoices > 0)
      throw new InconclusiveException(Some(buildSolution _))
    else
      Left(buildSolution _)

  override def handleNewUnitClause(electron: UnitClause): Unit = {
    val timeoutChecker = lazabs.GlobalParameters.get.timeoutChecker
    val electronBodyAtoms =
      for (nucleus <- clausesWithRelationInBody(electron.rs);
           electronIndex <- nucleus.body.indices
           if nucleus.body(electronIndex)._1 == electron.rs &&
              !feasibilityChecker.isInfeasibleCUCOnBodyAtom(
                nucleus, electronIndex, electron))
      yield (nucleus, electronIndex)
    for (bodyAtom <- electronBodyAtoms)
      resolvableCUCsOf.getOrElseUpdate(bodyAtom, new ArrayBuffer) += electron
    for ((nucleus, electronIndex) <- electronBodyAtoms) {
      val els = for (bodyIndex <- nucleus.body.indices) yield {
        val cucs : Seq[UnitClause] =
          resolvableCUCsOf.getOrElse((nucleus, bodyIndex), Seq())
        if (bodyIndex == electronIndex) Seq(electron)
        // only older cucs before the electron, so that no choice is
        // enumerated twice
        else if (bodyIndex < electronIndex &&
                 (cucs.lastOption exists (_ eq electron))) cucs.init
        else cucs
      }
      for (choice <- Combinatorics.cartesianProduct(els.toList)) {
        timeoutChecker()
        if (!feasibilityChecker.isInfeasibleChoiceAcrossBodyAtoms(nucleus,
                                                                  choice))
          enqueue(nucleus, choice, feasibilityChecker.initialBudgetMs)
      }
    }

  }

  override def handleForwardSubsumption(nucleus:   NormClause,
                                        electrons: Seq[UnitClause]): Unit = {}

  override def handleFalseConstraint(nucleus:   NormClause,
                                     electrons: Seq[UnitClause]): Unit = {}

}
