/**
 * Copyright (c) 2026 Zafer Esen, Philipp Ruemmer. All rights reserved.
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
import ap.parser.IAtom
import ap.parser.IExpression.i
import ap.terfor.{ConstantTerm, Term}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.substitutions.ConstantSubst
import lazabs.GlobalParameters.SLDAtomSelection
import lazabs.horn.Util.{Dag, DagEmpty, DagNode}
import lazabs.horn.bottomup.{HornClauses, NormClause, RelationSymbol}
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.preprocessor.HornPreprocessor.Solution

import scala.annotation.tailrec
import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap,
                                 Queue => MQueue}

/**
 * Backward symbolic execution by SLD resolution from goals to facts.
 * @param maxDepth      : Resolution steps after which a goal is not
 *                        resolved further. A search cut by the bound is
 *                        inconclusive.
 * @param atomSelection : Which atom of a goal is resolved, see AtomOrigin.
 */
class SLDSymex[CC](clauses       : Iterable[CC],
                   maxDepth      : Option[Int] = None,
                   atomSelection : SLDAtomSelection.Value =
                     SLDAtomSelection.Newest)(
    implicit clause2ConstraintClause : CC => ConstraintClause)
    extends Symex(clauses)
    with ConstraintSimplifierUsingConjunctEliminator {

  import Symex._
  import FeasibilityCheckResult._

  printInfo("Starting backward symbolic execution (SLD)...\n")

  /**
   * The atom first appears in the goal after `depth`
   * resolution steps, copied from `bodyIndex` of a body.
   */
  private case class AtomOrigin(depth : Int, bodyIndex : Int)

  /**
   * E.g., resolving P in 
   * false :- P(x), Q(x) with 
   *  P(x) :- R(x), S(x) gives
   * -------------------------
   * false :- Q(x), R(x), S(x) 
   * with origins Q: (0, 1), R: (1, 0) and S: (1, 1);
   * R, S added by the first resolution step (depth = 1), positions 0 and 1 of
   * the body (R(x), S(x)), Q comes from the goal (depth = 0), position 1.
   * R is selected under Newest, Q under Oldest.
   */
  private val selectionOrder : Ordering[AtomOrigin] = atomSelection match {
    case SLDAtomSelection.Newest =>
      Ordering.by((origin : AtomOrigin) => (-origin.depth, origin.bodyIndex))
    case SLDAtomSelection.Oldest =>
      Ordering.by((origin : AtomOrigin) => (origin.depth, origin.bodyIndex))
  }

  private case class ResolutionChoice(goal        : GoalClause,
                                      atomOrigins : Seq[AtomOrigin],
                                      atomIndex   : Int,
                                      clause      : NormClause,
                                      budgetMs    : Long)

  private val resolutionChoices  = new MQueue[ResolutionChoice]
  private val goalClauseDB       = new GoalClauseDB
  private val subsumptionChecker =
    new SubsumptionChecker[GoalClause](GoalSubsumption.subsumptionTestFor(_))

  private val collectStats = lazabs.GlobalParameters.get.log
  private var atomsDroppedByFactoring = 0L

  override def solve() : Either[() => Solution, Dag[(IAtom, CC)]] = {
    val solveStart = System.nanoTime
    var result : Either[() => Solution, Dag[(IAtom, CC)]] = null
    try {
      for ((inputGoal, _) <- normClauses
           if inputGoal.head._1.pred == HornClauses.FALSE &&
              inputGoal.body.nonEmpty) {
        val (goal, atomOrder) = normalizedGoal(
          simplified(GoalClause(inputGoal.body, inputGoal.constraint)))
        handleNewGoalClause(
          goal, Normalization(FromInputGoal(inputGoal), atomOrder),
          atomOrder.map(AtomOrigin(0, _)))
      }

      var ind = 0
      while (result == null && resolutionChoices.nonEmpty) {
        lazabs.GlobalParameters.get.timeoutChecker()
        ind += 1
        val ResolutionChoice(goal, atomOrigins, atomIndex, clause, budgetMs) =
          resolutionChoices.dequeue
        val resolutionStart = if (collectStats) System.nanoTime else 0L
        val simplifyBefore  = if (collectStats) simplifierTimeNanos else 0L
        val newGoal = resolve(goal, atomIndex, clause)
        if (collectStats)
          statistics.resolutionNanos +=
            (System.nanoTime - resolutionStart) -
            (simplifierTimeNanos - simplifyBefore)
        val derivation =
          Resolution(goalClauseDB.derivation(goal), atomIndex, clause)
        printInfo(ind + ".\t" + goal + "\n  +\n\t" + clause +
                  "\n  =\n\t" + newGoal)

        val endsSearchIfFeasible = newGoal.atoms.isEmpty
        val checkResult = checkFeasibilityWithinBudget(
          newGoal.constraint, endsSearchIfFeasible, budgetMs)
        statistics.statesDerived += 1
        checkResult match {
          case BudgetExpired =>
            val longerBudgetMs = budgetMs * budgetGrowthRate
            printInfo("  (Check budget expired, postponed with " +
                      longerBudgetMs + " ms.)")
            resolutionChoices enqueue ResolutionChoice(
              goal, atomOrigins, atomIndex, clause, longerBudgetMs)
          case Infeasible =>
            printInfo("  (Infeasible.)")
          case Feasible if endsSearchIfFeasible =>
            result = Right(buildCounterExample(derivation))
          case _ if endsSearchIfFeasible =>
            printInfo("  (Check said " + checkResult +
                      ", empty goal left undecided.)")
          case _ =>
            val constraint = withoutConjunctsUnconnectedToArgs(
              newGoal.constraint, newGoal.args.toSet, checkResult)
            if (!(constraint eq newGoal.constraint))
              statistics.statesWithUnconnectedConjunctsDropped += 1
            val newAtomOrigins =
              atomOrigins.patch(atomIndex, Nil, 1) ++
                clause.body.indices.map(AtomOrigin(derivation.depth, _))
            val (normalized, atomOrder) =
              normalizedGoal(GoalClause(newGoal.atoms, constraint))
            handleNewGoalClause(normalized,
                                Normalization(derivation, atomOrder),
                                atomOrder.map(newAtomOrigins))
        }
      }

      if (result == null) {
        printInfo("\t(Search space exhausted.)\n")
        for ((inputGoal, _) <- normClauses
             if result == null &&
                inputGoal.head._1.pred == HornClauses.FALSE &&
                inputGoal.body.isEmpty)
          checkFeasibility(inputGoal.constraint, budgetMs = None) match {
            case Feasible   =>
              result = Right(buildCounterExample(FromInputGoal(inputGoal)))
            case Infeasible =>
            case _          => statistics.undecidedEmptyGoals += 1
          }
        if (result == null)
          result = resultOfExhaustedSearch
      }
      result
    } finally {
      if (collectStats) {
        println(s"factoring: $atomsDroppedByFactoring atoms dropped")
        statistics.printStatistics(
          goalClauseDB.size, goalClauseDB.rejectedDuplicateCount,
          subsumptionChecker, simplifierStats, simplifierTimeNanos,
          System.nanoTime - solveStart)
      }
    }
  }

  private def resultOfExhaustedSearch
    : Either[() => Solution, Dag[(IAtom, CC)]] =
    if (statistics.undecidedEmptyGoals > 0)
      throw new InconclusiveException(candidateSolution = None)
    else if (statistics.depthPrunedChoices > 0)
      throw new InconclusiveException(Some(negatedGoalsSolution _))
    else
      Left(buildSolution _)

  private def handleNewGoalClause(goal        : GoalClause,
                                  derivation  : GoalDerivation,
                                  atomOrigins : Seq[AtomOrigin]) : Unit = {
    lazy val (factoredGoal, factoredDerivation, factoredAtomOrigins) =
      factored(goal, derivation, atomOrigins)
    if ((goalClauseDB isDuplicate goal) ||
        (!(factoredGoal eq goal) &&
           (goalClauseDB isDuplicate factoredGoal))) {
      printInfo("  (Derived goal already exists in the database.)")
    } else if (isSubsumed(factoredGoal)) {
      printInfo("  (Subsumed by existing goals.)")
    } else {
      goalClauseDB.add(factoredGoal, factoredDerivation)
      printInfo("  (Added to database: " + factoredGoal + ")\n")
      val atomIndex =
        factoredAtomOrigins.indices.minBy(factoredAtomOrigins)(selectionOrder)
      val clauses =
        clausesWithRelationInHead(factoredGoal.atoms(atomIndex)._1)
      if (maxDepth exists (factoredDerivation.depth >= _))
        statistics.depthPrunedChoices += clauses.size
      else
        for (clause <- clauses)
          resolutionChoices enqueue ResolutionChoice(
            factoredGoal, factoredAtomOrigins, atomIndex, clause,
            initialBudgetMs)
    }
  }

  private def resolve(goal      : GoalClause,
                      atomIndex : Int,
                      clause    : NormClause) : GoalClause = {
    val (rs, occ) = goal.atoms(atomIndex)
    val nextOccurrence = new MHashMap[RelationSymbol, Int]
    for ((atomRs, atomOcc) <- goal.atoms)
      nextOccurrence(atomRs) =
        nextOccurrence.getOrElse(atomRs, 0) max (atomOcc + 1)
    val bodyAtoms = for ((bodyRs, _) <- clause.body) yield {
      val bodyOcc = nextOccurrence.getOrElse(bodyRs, 0)
      nextOccurrence(bodyRs) = bodyOcc + 1
      (bodyRs, bodyOcc)
    }
    val renaming =
      (clause.headSyms zip rs.arguments(occ)) ++
        (for (((bodyRs, clauseOcc), (_, bodyOcc)) <- clause.body zip bodyAtoms;
              argPair <- bodyRs.arguments(clauseOcc) zip
                           bodyRs.arguments(bodyOcc))
           yield argPair)
    val clauseConstraint =
      ConstantSubst(renaming.toMap, symex_sf.order)(clause.constraint)
    simplified(GoalClause(
      goal.atoms.patch(atomIndex, Nil, 1) ++ bodyAtoms,
      Conjunction.conj(Seq(goal.constraint, clauseConstraint),
                       symex_sf.order)))
  }

  private def simplified(goal : GoalClause) : GoalClause = {
    val locals = goal.constraint.constants -- goal.args
    goal.copy(constraint =
      simplifyConstraint(goal.constraint, locals.map(local => local : Term),
                         reduceBeforeSimplification = true))
  }

  private def normalizedGoal(goal : GoalClause) : (GoalClause, Seq[Int]) =
    ConstraintNormalizer.normalizeGoal(
      goal,
      n => (symex_sf.localSymbolsForPred(HornClauses.FALSE, n, 0),
            symex_sf.order),
      Some(symex_sf.definedSymbolForPred(HornClauses.FALSE, _)))

  /**
   * Repeatedly unifies two atoms with the same relation symbol and drops one
   * of them as long as the result subsumes the goal.
   * The result subsumes the goal if the constraint of the goal implies the
   * result constraint with the kept atom mapped to either of the two.
   * E.g. false :- P(x0), P(x1), x0 = x1 & x0 > 0 becomes
   *      false :- P(x0), x0 > 0.
   */
  @tailrec private def factored(goal        : GoalClause,
                                derivation  : GoalDerivation,
                                atomOrigins : Seq[AtomOrigin])
  : (GoalClause, GoalDerivation, Seq[AtomOrigin]) = {
    val atoms = goal.atoms
    lazy val reduce = symex_sf.reducer(goal.constraint)
    def unification(keptIndex : Int, droppedIndex : Int)
    : Map[ConstantTerm, ConstantTerm] = {
      val (rs, keptOcc) = atoms(keptIndex)
      (rs.arguments(atoms(droppedIndex)._2) zip rs.arguments(keptOcc)).toMap
    }

    def impliedAfter(unification : Map[ConstantTerm, ConstantTerm]) =
      goal.conjuncts forall { conjunct =>
        !(conjunct.constants exists unification.contains) ||
          reduce(ConstantSubst(unification, symex_sf.order)(conjunct)).isTrue
      }
    val factorings =
      for (first <- atoms.indices.iterator;
           second <- (first + 1) until atoms.size
           if atoms(first)._1 == atoms(second)._1;
           (keptIndex, droppedIndex) <- Iterator((first, second),
                                                 (second, first))
           if impliedAfter(unification(keptIndex, droppedIndex)))
        yield (keptIndex, droppedIndex)
    if (factorings.hasNext) {
      val (keptIndex, droppedIndex) = factorings.next
      val constraint =
        ConstantSubst(unification(keptIndex, droppedIndex), symex_sf.order)(
          goal.constraint)
      val (factoredGoal, atomOrder) = normalizedGoal(
        GoalClause(atoms.patch(droppedIndex, Nil, 1), constraint))
      // the kept atom stands for both, so it is selected when the first of
      // the two would be
      val keptAtomOrigins = atomOrigins.updated(
        keptIndex,
        selectionOrder.min(atomOrigins(keptIndex), atomOrigins(droppedIndex))
      ).patch(droppedIndex, Nil, 1)
      atomsDroppedByFactoring += 1
      factored(factoredGoal,
               Normalization(Factoring(derivation, keptIndex, droppedIndex),
                             atomOrder),
               atomOrder.map(keptAtomOrigins))
    } else {
      (goal, derivation, atomOrigins)
    }
  }

  private def isSubsumed(goal : GoalClause) : Boolean =
    goal.atoms.map(_._1).distinct exists { rs =>
      subsumptionChecker.isSubsumed(goal, goalClauseDB.withFirstAtom(rs))
    }

  private def buildSolution() : Solution =
    if (goalClauseDB.goals exists (_.atoms.size > 1))
      throw new SymexException(
        "no solution construction yet for non-linear goals")
    else
      negatedGoalsSolution()

  private def negatedGoalsSolution() : Solution = {
    // the args of the atom are swapped with those at occ 0
    val constraintsOfAtoms =
      for (goal <- goalClauseDB.goals.toSeq; (rs, occ) <- goal.atoms) yield {
        val swap = (rs.arguments(occ) zip rs.arguments(0)) ++
                   (rs.arguments(0) zip rs.arguments(occ))
        (rs, ConstantSubst(swap.toMap, symex_sf.order)(goal.constraint))
      }
    val constraintsOfRs =
      constraintsOfAtoms groupBy (_._1) mapValues (_ map (_._2))
    for ((pred, rs) <- relationSymbols if pred != HornClauses.FALSE)
      yield (pred,
             solutionFormula(rs, disjunctionOverArgs(
               rs, constraintsOfRs.getOrElse(rs, Nil)).negate))
  }

  private class CexNode(val clause     : NormClause,
                        val headArgs   : Seq[ConstantTerm],
                        val bodyArgs   : IndexedSeq[Seq[ConstantTerm]],
                        val constraint : Conjunction) {
    val children = new Array[CexNode](bodyArgs.size)
  }

  // the body slots that an atom of the goal stands for
  // after factoring one atom stands for several
  private class CexLeaf(var targets : List[(CexNode, Int)])

  private def buildCounterExample(derivation : GoalDerivation)
    : Dag[(IAtom, CC)] = {
    @tailrec def stepsUpTo(step  : GoalDerivation,
                           later : List[GoalDerivation])
      : List[GoalDerivation] = step match {
      case FromInputGoal(_)         => step :: later
      case Resolution(parent, _, _) => stepsUpTo(parent, step :: later)
      case Factoring(parent, _, _)  => stepsUpTo(parent, step :: later)
      case Normalization(parent, _) => stepsUpTo(parent, step :: later)
    }

    val nodes = new ArrayBuffer[CexNode]
    def instantiate(clause : NormClause) : CexNode = {
      val (constraint, headArgs, bodyArgs) = clause.freshConstraint(symex_sf)
      val node = new CexNode(clause, headArgs, bodyArgs.toIndexedSeq,
                             constraint)
      nodes += node
      node
    }
    def leavesOf(node : CexNode) : Vector[CexLeaf] =
      node.bodyArgs.indices.map(slot => new CexLeaf(List((node, slot))))
        .toVector

    import prover._
    val groundAtoms = scope {
      var frontier = Vector[CexLeaf]()
      for (step <- stepsUpTo(derivation, Nil)) step match {
        case FromInputGoal(clause) =>
          val root = instantiate(clause)
          !! (asIFormula(root.constraint))
          frontier = leavesOf(root)
        case Resolution(_, atomIndex, clause) =>
          val child = instantiate(clause)
          !! (asIFormula(child.constraint))
          for ((node, slot) <- frontier(atomIndex).targets) {
            node.children(slot) = child
            for ((a, b) <- child.headArgs zip node.bodyArgs(slot))
              !! (i(a) === i(b))
          }
          frontier = frontier.patch(atomIndex, Nil, 1) ++ leavesOf(child)
        case Factoring(_, keptIndex, droppedIndex) =>
          frontier(keptIndex).targets =
            frontier(keptIndex).targets ++ frontier(droppedIndex).targets
          frontier = frontier.patch(droppedIndex, Nil, 1)
        case Normalization(_, atomOrder) =>
          frontier = atomOrder.map(frontier).toVector
      }
      val status = ???
      assert(status == ProverStatus.Sat)
      withCompleteModel { model =>
        for (node <- nodes) yield
          IAtom(node.clause.head._1.pred,
                node.headArgs.map(arg => model.evalToTerm(arg)))
      }
    }

    val nodeIndex = nodes.zipWithIndex.toMap
    var dag : Dag[(IAtom, CC)] = DagEmpty
    for (index <- nodes.indices.reverse) {
      val node = nodes(index)
      dag = DagNode((groundAtoms(index), normClauseToCC(node.clause)),
                    node.children.map(child => nodeIndex(child) - index).toList,
                    dag)
    }
    dag
  }
}
