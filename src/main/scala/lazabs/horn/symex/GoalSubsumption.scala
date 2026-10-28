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

import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.substitutions.ConstantSubst
import lazabs.horn.bottomup.HornClauses

/**
 * Subsumption of goals in normal form. Stored subsumes goal if its atoms
 * map to different atoms of goal with the same relation symbols such that
 * the constraint of goal implies the constraint of stored, with the
 * arguments renamed by the atom map and the locals renamed to the locals
 * of goal with the same definition. Atoms are mapped injectively 
 * for completeness.
 * The test is sound but incomplete and currently only pairwise. 
 * (The implication is checked by the reducer rather than a solver call.)
 */
object GoalSubsumption {

  /**
   * The test whether a stored goal subsumes goal.
   * E.g. false :- P(x0),        x0 > 0 subsumes
   *      false :- P(x0), Q(y0), x0 > 1 & y0 = x0.
   */
  def subsumptionTestFor(goal : GoalClause)
                        (implicit symex_sf : SymexSymbolFactory)
  : GoalClause => Boolean = {
    lazy val reduce = symex_sf.reducer(goal.constraint)
    stored => subsumes(stored, goal, reduce)
  }

  private def subsumes(stored : GoalClause,
                       goal   : GoalClause,
                       reduce : ReduceWithConjunction)
                      (implicit symex_sf : SymexSymbolFactory) : Boolean = {
    def impliedByGoal(conjunct : Conjunction,
                      renaming : Map[ConstantTerm, ConstantTerm]) : Boolean =
      reduce(ConstantSubst(renaming, symex_sf.order)(conjunct)).isTrue

    def argConjunctsChecked(lastAtom : Int,
                                 renaming : Map[ConstantTerm, ConstantTerm])
    : Boolean =
      stored.conjunctsByLastAtom.getOrElse(lastAtom, Nil) forall
        (impliedByGoal(_, renaming))

    def mapsAtomsFrom(storedIndex : Int,
                      atomMap     : Vector[Int],
                      renaming    : Map[ConstantTerm, ConstantTerm])
    : Boolean =
      if (storedIndex == stored.atoms.size) {
        stored.conjunctsByLastAtom.get(storedIndex) forall { localConjuncts =>
          val withLocals = renaming ++ localRenaming(stored, goal, atomMap)
          localConjuncts forall (impliedByGoal(_, withLocals))
        }
      } else {
        val (rs, storedOcc) = stored.atoms(storedIndex)
        // the maps through an earlier unmapped interchangeable atom are the
        // same up to swapping the two
        def triedBefore(goalIndex : Int) =
          (0 until goalIndex) exists { other =>
            goal.firstInterchangeableAtom(other) ==
              goal.firstInterchangeableAtom(goalIndex) &&
            !(atomMap contains other)
          }
        goal.atoms.indices exists { goalIndex =>
          val (goalRs, goalOcc) = goal.atoms(goalIndex)
          goalRs == rs && !(atomMap contains goalIndex) &&
          !triedBefore(goalIndex) && {
            lazabs.GlobalParameters.get.timeoutChecker()
            val extended = renaming ++
              (rs.arguments(storedOcc) zip rs.arguments(goalOcc))
            argConjunctsChecked(storedIndex, extended) &&
              mapsAtomsFrom(storedIndex + 1, atomMap :+ goalIndex, extended)
          }
        }
      }

    (stored.atomCounts forall { case (rs, n) =>
       goal.atomCounts.getOrElse(rs, 0) >= n }) &&
      argConjunctsChecked(-1, Map()) &&
      mapsAtomsFrom(0, Vector(), Map())
  }

  /**
   * Renames each local of stored that has a definition to the local of goal
   * with the same definition after the atom map moves its argument indices.
   * E.g. c in false :- Q(y0),        2c = y0 is defined over argument 0.
   * In        false :- P(x0), Q(y0), 2d = y0 the y0 is argument 1 so c becomes d.
   */
  private def localRenaming(stored  : GoalClause,
                            goal    : GoalClause,
                            atomMap : Seq[Int])
                           (implicit symex_sf : SymexSymbolFactory)
  : Map[ConstantTerm, ConstantTerm] = {
    val goalOffsets = goal.atoms.scanLeft(0)(_ + _._1.arity)
    val newIndex =
      (for (((rs, _), goalIndex) <- stored.atoms zip atomMap;
            argIndex <- 0 until rs.arity)
         yield goalOffsets(goalIndex) + argIndex).toArray
    if (newIndex.indices forall (index => newIndex(index) == index))
      Map()
    else
      (for (local <- (stored.constraint.constants -- stored.args).toSeq;
            id <- symex_sf.definitionIdOf(local);
            symbol <- symex_sf.existingDefinedSymbolForPred(
                        HornClauses.FALSE,
                        ConstraintNormalizer.withArgsReordered(id, newIndex)))
         yield (local, symbol)).toMap
  }
}
