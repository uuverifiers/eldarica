/**
 * Copyright (c) 2026 Zafer Esen. All rights reserved.
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
import ap.terfor.conjunctions.Conjunction
import lazabs.horn.Util.{Dag, DagEmpty, DagNode}
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.bottomup.NormClause
import lazabs.horn.preprocessor.HornPreprocessor.Solution

import scala.collection.mutable.{HashSet => MHashSet,
                                 Queue   => MQueue}

/**
 * Backward symbolic execution using SLD resolution.
 *
 * Maintains a BFS queue of (possibly non-linear) [[GoalClause]]s.
 * At each step the last atom is selected and resolved
 * against all clauses whose head matches.
 *
 * @param maxDepth search depth bound (None = unbounded)
 */
class SLDSymex[CC](clauses  : Iterable[CC],
                   maxDepth : Option[Int] = None)(
    implicit clause2ConstraintClause : CC => ConstraintClause)
    extends Symex(clauses)
    with SimpleSubsumptionChecker
    with ConstraintSimplifierUsingConjunctEliminator {

  printInfo("Starting SLD symbolic execution...\n")

  private val choicesQueue = new MQueue[(GoalClause, Int, NormClause)]
  private val goalClauseDB = new GoalClauseDB

  private var isUnsat : Option[GoalClause] = None

  // Initial goal clauses from all assertion clauses
  // This also inits the choices queue via handleNewGoalClause
  for ((nc, _) <- normClauses if nc.head._1.pred == HornClauses.FALSE)
    handleNewGoalClause(GoalClause.fromAssertion(nc))

  private def handleNewGoalClause(g : GoalClause) : Unit = {
    if (g.constraint.isFalse) return
    if (!goalClauseDB.add(g)) return

    if (g.atoms.isEmpty) {
      // check if constraint is satisfiable (yes ==> unsat)
      val status = checkFeasibility(g.constraint)
      if (status == ProverStatus.Valid || status == ProverStatus.Sat)
        isUnsat = Some(g)
    } else {
      // TODO: experiment with different selection strategies
      //       currently picking the first atom in the body of the goal
      val rules = clausesWithRelationInHead(g.atoms.head.rs)
      for (nc <- rules)
        choicesQueue.enqueue((g, 0, nc))
    }
  }

  override def solve() : Either[Solution, Dag[(IAtom, CC)]] = {
    var result : Either[Solution, Dag[(IAtom, CC)]] = null

    val touched = new MHashSet[NormClause]
    for ((nc, _) <- normClauses if nc.head._1.pred == HornClauses.FALSE)
      touched += nc

    // initial empty goals (body-less assertions like FALSE :- true)
    // are detected during seeding above
    isUnsat match {
      case Some(g) =>
        // TODO: build proper CEX DAG using parent chain
        result = Right(
          DagNode((IAtom(HornClauses.FALSE, Nil),
                   normClauseToCC(g.origin)),
                  List(), DagEmpty))
      case None =>
    }

    // main loop: dequeue a choice, resolve, handle the result
    var ind : Long = 0
    while (result == null && choicesQueue.nonEmpty) {
      lazabs.GlobalParameters.get.timeoutChecker()
      ind += 1

      val (goal, atomIdx, nc) = choicesQueue.dequeue()
      touched += nc
      printInfo(ind + ". depth=" + goal.depth +
        " atoms=" + goal.atoms.size +
        " queue=" + choicesQueue.size)

      // resolve and handle the resulting goal clause
      val newGoal =
        goal.resolveAtom(atomIdx, nc, simplifyConstraint)(symex_sf)
      val depthOk = maxDepth match {
        case Some(d) => newGoal.depth <= d
        case None    => true
      }
      if (depthOk) handleNewGoalClause(newGoal)

      // handleNewGoalClause sets emptyGoal on contradiction
      isUnsat match {
        case Some(g) =>
          // TODO: build proper CEX DAG using parent chain
          result = Right(
            DagNode((IAtom(HornClauses.FALSE, Nil),
                     normClauseToCC(g.origin)),
                    List(), DagEmpty))
        case None =>
      }
    }

    if (result == null) {
      printInfo("\t(Search space exhausted.)\n")

      // check untouched body-less assertions
      val untouched =
        (normClauses.map(_._1).toSet -- touched).filter(nc =>
          nc.body.isEmpty && nc.head._1.pred == HornClauses.FALSE)
      for (nc <- untouched if result == null) {
        val status = checkFeasibility(nc.constraint)
        if (status == ProverStatus.Valid || status == ProverStatus.Sat)
          result = Right(
            DagNode((IAtom(HornClauses.FALSE, Nil), normClauseToCC(nc)),
                    List(), DagEmpty))
      }
      // TODO: proper solution construction for non-unit goals
      if (result == null)
        result = Left(buildSolution())
    }
    result
  }

  // TODO: this is unused, refactor solve in main Symex
  def getClausesForResolution : Option[(NormClause, Seq[UnitClause])] = None
  def handleNewUnitClause(clause : UnitClause) : Unit = {}
  def handleForwardSubsumption(nucleus   : NormClause,
                               electrons : Seq[UnitClause]) : Unit = {}
  def handleBackwardSubsumption(subsumed : Set[UnitClause]) : Unit = {}
  def handleFalseConstraint(nucleus   : NormClause,
                            electrons : Seq[UnitClause]) : Unit = {}
}
