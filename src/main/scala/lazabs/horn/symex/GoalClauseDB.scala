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

import lazabs.horn.bottomup.RelationSymbol

import scala.collection.mutable.{ArrayBuffer => MArrayBuffer,
                                 HashMap => MHashMap,
                                 LinkedHashMap => MLinkedHashMap}

/**
 * The goals of a backward search and their derivations. The goals are
 * listed oldest first by the relation symbol of their first atom.
 */
class GoalClauseDB {
  private val derivations = new MLinkedHashMap[GoalClause, GoalDerivation]
  private val goalsWithFirstAtom =
    new MHashMap[RelationSymbol, MArrayBuffer[GoalClause]]

  var rejectedDuplicateCount = 0L

  def size : Int = derivations.size

  def goals : Iterable[GoalClause] = derivations.keys

  def derivation(goal : GoalClause) : GoalDerivation = derivations(goal)

  def withFirstAtom(rs : RelationSymbol) : IndexedSeq[GoalClause] =
    goalsWithFirstAtom.getOrElse(rs, IndexedSeq())

  def isDuplicate(goal : GoalClause) : Boolean = {
    val duplicate = derivations contains goal
    if (duplicate)
      rejectedDuplicateCount += 1
    duplicate
  }

  def add(goal : GoalClause, derivation : GoalDerivation) : Unit = {
    derivations(goal) = derivation
    goalsWithFirstAtom.getOrElseUpdate(goal.atoms.head._1,
                                       new MArrayBuffer) += goal
  }
}
