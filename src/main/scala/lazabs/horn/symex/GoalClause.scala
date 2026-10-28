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
import lazabs.horn.bottomup.{NormClause, RelationSymbol}

import scala.collection.mutable.ArrayBuffer

/**
 * A goal clause false :- A1, ..., An, C. The atom (rs, occ) has the
 * arguments rs.arguments(occ); the other symbols of C are local.
 */
case class GoalClause(atoms      : Seq[(RelationSymbol, Int)],
                      constraint : Conjunction) {
  lazy val args : Seq[ConstantTerm] =
    for ((rs, occ) <- atoms; arg <- rs.arguments(occ)) yield arg

  lazy val atomCounts : Map[RelationSymbol, Int] =
    for ((rs, rsAtoms) <- atoms groupBy (_._1)) yield (rs, rsAtoms.size)

  lazy val conjuncts : IndexedSeq[Conjunction] =
    if (constraint.quans.isEmpty && !constraint.isFalse)
      constraint.iterator.toIndexedSeq
    else
      IndexedSeq(constraint)

  /**
   * The conjuncts by the last atom whose arguments they contain: -1 for
   * conjuncts without symbols and atoms.size for conjuncts with locals.
   * Used in goal subsumption, where the atoms of the stored goal are mapped
   * one at a time and each conjunct is checked as soon as the atoms up to
   * its key are mapped, so that a failing atom map is abandoned early.
   * E.g. in false :- P(x0), Q(y0), x0 > 0 & y0 > x0 & 2c = y0 the keys
   * are 0, 1 and 2.
   */
  lazy val conjunctsByLastAtom : Map[Int, IndexedSeq[Conjunction]] = {
    val atomOfArg =
      (for (((rs, occ), atomIndex) <- atoms.zipWithIndex;
            arg <- rs.arguments(occ))
         yield (arg, atomIndex)).toMap
    conjuncts groupBy { conjunct =>
      if (conjunct.constants subsetOf atomOfArg.keySet)
        (-1 +: conjunct.constants.toSeq.map(atomOfArg)).max
      else
        atoms.size
    }
  }

  /**
   * For each atom, the first atom it can be swapped with such that swapping
   * the arguments of the two does not change the constraint. Used in goal
   * subsumption to skip atom maps that equal a tried one up to such swaps.
   * E.g. in false :- P(x0), P(x1), P(x2), x0 + x1 > 0 & x2 = 1
   * the first atoms are 0, 0 and 2 (i.e., x0 and x1 can be swapped,
   * but not x2 with the others, so last one is itself at ind 2).
   */
  lazy val firstInterchangeableAtom : IndexedSeq[Int] = {
    // a swap can change how equations reduce so compare after reduction
    val reduce = ReduceWithConjunction(Conjunction.TRUE, constraint.order)
    lazy val reducedConstraint = reduce(constraint)
    def interchangeable(first : Int, second : Int) : Boolean = {
      val (rs, firstOcc) = atoms(first)
      val (secondRs, secondOcc) = atoms(second)
      rs == secondRs && {
        val swap = (rs.arguments(firstOcc) zip rs.arguments(secondOcc)) ++
                   (rs.arguments(secondOcc) zip rs.arguments(firstOcc))
        reduce(ConstantSubst(swap.toMap, constraint.order)(constraint)) ==
          reducedConstraint
      }
    }
    val firsts = new ArrayBuffer[Int]
    for (index <- atoms.indices)
      firsts += ((0 until index) find { other =>
        firsts(other) == other && interchangeable(other, index)
      } getOrElse index)
    firsts
  }

  override def toString : String =
    "false :- " + ((for ((rs, occ) <- atoms) yield rs.toString(occ)) :+
                     constraint.toString).mkString(", ")
}

/**
 * The last step of the derivation of a goal from a goal of the input.
 * After a resolution the atoms are the remaining ones of the parent
 * followed by the body atoms of the clause.
 */
sealed abstract class GoalDerivation {
  val depth : Int
}

case class FromInputGoal(clause : NormClause) extends GoalDerivation {
  val depth = 0
}

case class Resolution(parent    : GoalDerivation,
                      atomIndex : Int,
                      clause    : NormClause) extends GoalDerivation {
  val depth = parent.depth + 1
}

// the atom at droppedIndex is unified with the one at keptIndex
case class Factoring(parent       : GoalDerivation,
                     keptIndex    : Int,
                     droppedIndex : Int) extends GoalDerivation {
  val depth = parent.depth
}

// the atom at index i was the one at atomOrder(i) before
case class Normalization(parent    : GoalDerivation,
                         atomOrder : Seq[Int]) extends GoalDerivation {
  val depth = parent.depth
}
