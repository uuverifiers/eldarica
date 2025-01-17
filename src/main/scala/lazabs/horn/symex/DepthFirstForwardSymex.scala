/**
 * Copyright (c) 2022-2025 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import ap.parser.IAtom
import lazabs.horn.Util.Dag
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.bottomup.{HornClauses, NormClause, RelationSymbol}
import lazabs.horn.preprocessor.HornPreprocessor.Solution

import scala.annotation.tailrec
import scala.collection.mutable.{HashSet => MHashSet, Queue => MQueue, Stack => MStack}

/**
 * Implements a depth-first forward symbolic execution using Symex.
 */
class DepthFirstForwardSymex[CC](clauses : Iterable[CC])(
    implicit clause2ConstraintClause     :     CC => ConstraintClause)
    extends Symex(clauses)
    with SimpleSubsumptionChecker
    with ConstraintSimplifierUsingConjunctEliminator {

  import Symex._

  printInfo("Starting depth-first forward symbolic execution (DFS)...\n")

  // Keeps track of the remaining branches.
  private val choicesStack = new MStack[MQueue[NormClause]]
  /*
   * Initialize the search by adding the facts. Each fact corresponds to a source
   * in the search DAG.
   */
  for (fact <- facts) {
    unitClauseDB.push() // we push regardless if there is a choice or not
    unitClauseDB add (fact, parents = (factToNormClause(fact), Nil)) // add each fact to the stack
    val possibleChoices = clausesWithRelationInBody(fact.rs)
    val choiceQueue     = new MQueue[NormClause]
    choiceQueue.enqueue(possibleChoices : _*)
    choicesStack push choiceQueue
  }

  def getClausesForResolution : Option[(NormClause, Seq[UnitClause])] = {
    if (unitClauseDB isEmpty) { // the search space is exhausted
      None
    } else {
      val electron = unitClauseDB.last // use last cuc to enforce depth-first exploration
      if (choicesStack isEmpty) {
        None
      } else {
        val possibleChoices = choicesStack.top
        possibleChoices.length match {
          case 0 => // no more resolution options for this cuc, backtrack
            backtrack()
            //choicesStack.pop()
            //unitClauseDB.pop()
            getClausesForResolution
          case n =>
            if (n > 1)
              unitClauseDB.push()
            val choice = possibleChoices.dequeue
            Some((choice, Seq(electron)))
        }
      }
    }
  }

  override def handleNewUnitClause(clause : UnitClause) : Unit = {
    val possibleChoices = clausesWithRelationInBody(clause.rs)
    // "possible", because clauses might be nonlinear and we might not have all needed electrons in the DB.

    if (possibleChoices.exists(clause => clause.body.length > 1))
      ??? // todo: support nonlinear clauses, assuming they do not exist for now :-)

    possibleChoices.length match {
      case 0 =>
        println(
          "Warning: new unit clause has no clauses to resolve against " + clause)
      case _ => // a decision point
        val choiceQueue = new MQueue[NormClause]
        choiceQueue.enqueue(possibleChoices : _*)
        choicesStack push choiceQueue
    }
  }

  override def handleForwardSubsumption(nucleus   :   NormClause,
                                        electrons : Seq[UnitClause]) : Unit = {
    printInfo("  (DFS: handling forward subsumption.)\n")
    backtrack()
  }

  override def handleBackwardSubsumption(subsumed : Set[UnitClause]) : Unit = {
    //
  }

  override def handleFalseConstraint(nucleus   :   NormClause,
                                     electrons : Seq[UnitClause]) : Unit = {

    backtrack()
  }

  private def backtrack() : Unit = {
    printInfo("  (DFS: backtracking.)\n")
    unitClauseDB.pop()
    while (choicesStack.nonEmpty && choicesStack.top.isEmpty) choicesStack.pop()
  }

  override def solve() : Either[Solution, Dag[(IAtom, CC)]] = {
    var result : Either[Solution, Dag[(IAtom, CC)]] = null

    val touched = new MHashSet[NormClause]
    facts.foreach(fact => touched += factToNormClause(fact))

    // start traversal
    var ind : Long = 0
    while (result == null) {
      lazabs.GlobalParameters.get.timeoutChecker()
      ind += 1
      printInfo(ind + ".", false)
      getClausesForResolution match {
        case Some((nucleus, electrons)) => {
          touched += nucleus
          val newElectron = hyperResolve(nucleus, electrons)
          printInfo("\t" + nucleus + "\n  +\n\t" + electrons.mkString("\n\t"))
          printInfo("  =\n\t" + newElectron)
          val isGoal = // TODO: do we need both disjuncts?
            (newElectron.rs.pred == HornClauses.FALSE) || (!newElectron.isPositive)

          if (isGoal) {
            val proverStatus =
              checkFeasibility(newElectron.constraint, timeoutMs = None)
            if (hasContradiction(newElectron, proverStatus)) { // false :- true
              unitClauseDB.add(newElectron, (nucleus, electrons))
              result = Right(buildCounterExample(newElectron))
            }
          } else { // not a goal clause, no sat check needed
            if (newElectron.constraint.isFalse) { // only a simple check, replace with a sat check w/ short t/o?
              handleFalseConstraint(nucleus, electrons)
            } else if (checkForwardSubsumption(newElectron, unitClauseDB)) {
              printInfo("subsumed by existing unit clauses.")
              handleForwardSubsumption(nucleus, electrons)
            } else {
              val backSubsumed =
                checkBackwardSubsumption(newElectron, unitClauseDB)
              if (backSubsumed nonEmpty) {
                printInfo(
                  "subsumes " + backSubsumed.size + " existing unit clause(s)_...",
                  newLine = false)
                handleBackwardSubsumption(backSubsumed)
              }
              if (unitClauseDB.add(newElectron, (nucleus, electrons))) {
                printInfo("\n  (Added to database.)\n")
                handleNewUnitClause(newElectron)
              } else {
                printInfo("\n  (Derived clause already exists in the database.)")
                handleForwardSubsumption(nucleus, electrons)
              }
            }
          }
        }
        case None => // nothing left to explore, the clauses are SAT.
          printInfo("\t(Search space exhausted.)\n")

          // Untouched clauses can be either those which were unreachable,
          // or corner cases such as a single assertion which did not need
          // symbolic execution.
          // The only case we need to handle is assertions without body literals,
          // because assertions with uninterpreted body literals are always
          // solveable by interpreting the body literals as false.

          val untouchedClauses =
            (normClauses.map(_._1).toSet -- touched).filter(_.body.isEmpty)
          assert(untouchedClauses.forall(clause =>
            clause.head._1.pred == HornClauses.FALSE))
          if (untouchedClauses nonEmpty) {
            printInfo("\t(Dangling assertions detected, checking those too.)")
            for (clause <- untouchedClauses if result == null) {
              val cuc = // for the purpose of checking feasibility
                if (clause.body.isEmpty) {
                  new UnitClause(RelationSymbol(HornClauses.FALSE),
                    clause.constraint,
                    false)
                } else toUnitClause(clause)
              unitClauseDB.add(cuc, (clause, Nil))
              if (hasContradiction(cuc, checkFeasibility(cuc.constraint, timeoutMs = None))) {
                result = Right(buildCounterExample(cuc))
              }
            }
            if (result == null) { // none of the assertions failed, so this is SAT
              result = Left(buildSolution())
            }
          } else {
            result = Left(buildSolution())
          }
        case other =>
          throw new SymexException(
            "Cannot hyper-resolve clauses: " + other.toString)
      }
    }
    result
  }

}
