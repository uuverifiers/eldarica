/**
 * Copyright (c) 2022 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.acceleration.PrincessFlataWrappers.MHashMap
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.bottomup.NormClause

import scala.annotation.tailrec
import scala.collection.mutable.{Queue => MQueue, Stack => MStack}

/**
 * Implements a breadth-first forward symbolic execution using Symex.
 */
class BreadthFirstForwardSymex[CC](clauses: Iterable[CC])(
    implicit clause2ConstraintClause:       CC => ConstraintClause)
    extends Symex(clauses)
    with SimpleSubsumptionChecker
    with ConstraintSimplifierUsingConjunctEliminator {

  import Symex._

  printInfo("Starting breadth-first forward symbolic execution (BFS)...\n")

  // Explore the state graph (the derived unit clauses) breadth-first. At
  // each depth there can be multiple choices for execution from a state
  // (the clauses to resolve with). Hence, we have a queue of states to resolve
  // with, and for each state a queue of branches to explore.
  //
  // Nonlinear clauses: there might be some paths that are accessible using more
  // than a single state, if other states we use are in the queue, we remove
  // from those states' queue the path that we are about to take.

  private val choicesQueue = new MQueue[(NormClause, Seq[UnitClause])]

  // Depth of the search DAG
  private var depth = 0

  private def increaseDepth(): Unit = {
    depth += 1
    unitClauseDB.push()
    printInfo(" Depth: " + depth)
  }

  /*
   * Initialize the search by adding the facts (the initial states).
   * Each fact corresponds to a source in the search DAG.
   * We use pushes to mark newly derived states (unit clauses) at each depth,
   * beginning at depth 0
   */
  increaseDepth()
  for (fact <- facts)
    unitClauseDB add (fact, parents = (factToNormClause(fact), Nil))

  @tailrec
  final override def getClausesForResolution
    : Option[(NormClause, Seq[UnitClause])] = {
    choicesQueue.foreach(println)
    println
    if (unitClauseDB isEmpty) { // no facts, nothing to resolve with
      None
    } else {
      if (choicesQueue isEmpty) {
        printInfo(" Choice queue is empty")
        val newElectrons = unitClauseDB.clausesSinceLastPush
        newElectrons match {
          case Nil => None // search space exhausted
          case _ =>
            increaseDepth()

            var usedElectrons = new MHashMap[UnitClause, List[NormClause]]
            for (electron <- newElectrons)
              usedElectrons += ((electron, Nil))

            for (electron <- newElectrons) {
              val possibleChoices = clausesWithRelationInBody(electron.rs)
              for (nucleus <- possibleChoices
                   if !usedElectrons(electron).contains(nucleus)) {

                val electronsForAtoms: Seq[Option[UnitClause]] =
                  for ((rs, occ) <- nucleus.body) yield {
                    // see if we have an electron available for every body literal
                    // first look among the new electrons
                    if (electron.rs == rs) // if this is the literal matching this electron
                      // todo: if we have multiple occurrences of a literal,
                      //   which cuc to use, last derived one?
                      Some(electron) // review
                    else {
                      newElectrons.find(_.rs == rs) match {
                        case Some(cuc) => Some(cuc)
                        case None      =>
                          // otherwise try to get one from previously inferred cucs
                          unitClauseDB.inferred(rs) match {
                            case Some(cucs) if cucs.nonEmpty =>
                              Some(cucs.last) // the most recent one
                            case _ =>
                              None
                            // There is no derived state/cuc yet for one of the
                            // body literals. This nucleus will be resolved later
                            // when that state is derived, do nothing.
                          }
                      }
                    }
                  } // todo: optimization opportunity: exit this loop early when no electron is found for the first time

                if (electronsForAtoms.forall(_.nonEmpty)) {
                  val electrons = electronsForAtoms.map(_.get)
                  // found a cuc/electron for all body literals
                  choicesQueue enqueue ((nucleus, electrons))
                  // mark all new electrons as "used" for this nucleus
                  for (electron <- electrons)
                    usedElectrons += ((electron,
                                       nucleus :: usedElectrons(electron)))
                }
              }
            }
            getClausesForResolution
        }
      } else Some(choicesQueue.dequeue())
    }
  }

  override def handleNewUnitClause(clause: UnitClause): Unit = {
    // nothing needed
  }

  override def handleForwardSubsumption(nucleus:   NormClause,
                                        electrons: Seq[UnitClause]): Unit = {
    // nothing needed
  }

  override def handleBackwardSubsumption(subsumed: Set[UnitClause]): Unit = {
    // todo: future work
  }

  override def handleFalseConstraint(nucleus:   NormClause,
                                     electrons: Seq[UnitClause]): Unit = {
    // unlike DFS, nothing needed in this case either
  }
}
