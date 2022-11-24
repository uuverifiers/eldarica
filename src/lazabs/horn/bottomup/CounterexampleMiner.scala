/**
 * Copyright (c) 2021-2022 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.bottomup

import ap.Signature
import ap.parser._
import ap.theories.TheoryCollector
import ap.terfor.ConstantTerm
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction

import Util._
import DisjInterpolator.{AndOrNode, AndNode, OrNode}
import HornClauses.{ConstraintClause, Literal}

import lattopt._

import scala.collection.mutable.ArrayBuffer

class CounterexampleMiner[CC <% HornClauses.ConstraintClause]
(iClauses : Seq[CC],
 predicateGenerator : Dag[AndOrNode[NormClause, Unit]] =>
   Either[Seq[(Predicate, Seq[Conjunction])],
     Dag[(IAtom, NormClause)]]) {

  val clauseFlags =
    for ((_, n) <- iClauses.zipWithIndex) yield new Predicate("f_" + n, 0)

  val clauseFlagsSet =
    clauseFlags.toSet

  val augmentedClauses =
    for ((clause, f) <- iClauses zip clauseFlags) yield new ConstraintClause {
      def head = clause.head
      val flag = new Literal {
        val predicate = f
        val relevantArguments = List()
      }
      def body = clause.body ++ List(flag)
      def localVariableNum = clause.localVariableNum

      def instantiateConstraint(headArguments : Seq[ConstantTerm],
                                bodyArguments: Seq[Seq[ConstantTerm]],
                                localVariables : Seq[ConstantTerm],
                                sig : Signature) : Conjunction =
        clause.instantiateConstraint(headArguments,
          bodyArguments.init,
          localVariables,
          sig)

      override def collectTheories(coll : TheoryCollector) : Unit =
        clause collectTheories coll
    }

  val solver =
    new IncrementalHornPredAbs(augmentedClauses,
      Map(),
      clauseFlags.toSet,
      predicateGenerator)

  private implicit val randomData = new SeededRandomDataSource(123)

  private var checks = 0

  val cexLattice = {
    val baseLattice =
      PowerSetLattice.inverted(clauseFlags)

    baseLattice.filterWithBounds(
      (testedSet, optFeasible, optInfeasible) => {
        checks = checks + 1
        val subst =
          (for (p <- clauseFlags)
            yield (p -> (if (testedSet contains p)
              Conjunction.TRUE
            else
              Conjunction.FALSE))).toMap
        solver.checkWithSubstitution(subst) match {
          case Left(sol) =>
            optInfeasible(_ => false)

          case Right(cex) => {
            val usedFlags =
              (for ((_, clause) <- cex.iterator;
                    p <- clause.predicates.iterator;
                    if clauseFlagsSet contains p)
              yield p).toSet
            optFeasible(set2 => usedFlags subsetOf set2)
          }
        }
      })
  }

  private def flagsToIndexes(flags : Set[Predicate]) : Seq[Int] =
    (for (f <- flags) yield (clauseFlags indexOf f)).toVector.sorted

  println
  println("Clauses contained in every counterexample:")
  val commonCounterexampleIndexs=
  {
    val j = cexLattice.njoin(
      (for (obj <- cexLattice.succ(cexLattice.bottom);
            if !cexLattice.isFeasible(obj))
      yield obj).toList : _*)
    val notNeeded = cexLattice getLabel j
    val needed = (clauseFlags filterNot notNeeded).toSet
    val neededIndexs=flagsToIndexes(needed)
    println(neededIndexs)
    neededIndexs
  }

  println
  println("Union of the minimal counterexample sets:")
  val unionMinimalCounterexampleIndexs=flagsToIndexes(cexLattice.getLabel(Algorithms.maximalFeasibleObjectMeet(cexLattice)(cexLattice.bottom)))
  println(unionMinimalCounterexampleIndexs)

  println
  println("Minimal counterexample sets:")
  for (obj <- Algorithms.maximalFeasibleObjects(cexLattice)(cexLattice.bottom))
    println(flagsToIndexes(cexLattice.getLabel(obj)))

  Console.out.println("Checks: " + checks)

}
