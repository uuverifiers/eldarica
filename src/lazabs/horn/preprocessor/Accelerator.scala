/**
 * Copyright (c) 2011-2022 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.preprocessor

import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.parser._
import ap.terfor.preds.Predicate
import ap.types.Sort

import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.Util.{Dag, DagNode, DagEmpty}
import lazabs.horn.acceleration._

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

/**
 * Split clauses with large bodies into multiple clauses.
 */
object Accelerator extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "acceleration"

  val IntSet : Set[Sort] = Set(Sort.Integer)

  def onlyIntegerArguments(clauses : Clauses) : Boolean =
    allPredicates(clauses) forall {
      p => predArgumentSorts(p).toSet subsetOf IntSet
    }

  def process(clauses : Clauses, hints : VerificationHints,
              frozenPredicates : Set[Predicate])
             : (Clauses, VerificationHints, BackTranslator) = {
    if (!frozenPredicates.isEmpty || !onlyIntegerArguments(clauses))
      return (clauses, hints, IDENTITY_TRANSLATOR)

    val newClauses = HornAccelerate.accelerate(clauses)

    val translator = new BackTranslator {
      val clause2Cycle = newClauses.toMap

      def translate(solution : Solution) = solution

      def translate(cex : CounterExample) =
        cex substitute buildSubst(cex)

      private def buildSubst(cex : CounterExample) : Map[Int, CounterExample] =
        SimpleAPI.withProver { p =>
          implicit val prover = p

          (for ((subCEX@DagNode((a, clause), children, _), i) <-
                  cex.subdagIterator.zipWithIndex;
                cycle = clause2Cycle get clause;
                if cycle.isDefined)
           yield {
             val bodyAtoms = for (c <- children) yield subCEX(c)._1
             assert(bodyAtoms.size == 1)
             i -> expandClause(cycle.get, a, bodyAtoms.head)
           }).toMap
        }

      private def expandClause(cycle : Seq[Clause], head : IAtom, body : IAtom)
                              (implicit p : SimpleAPI) : CounterExample = {
        import p._
        scope {
          assert(cycle.size == 1) // TODO

          val finalState = body.args
          val states = new ArrayBuffer[Seq[ITerm]]
          states += head.args

          def addN(n : Int) : Unit =
            for (_ <- 0 until n) {
              val freshClause = cycle.head.refresh._1
              addConstantsRaw(freshClause.constantsSorted)
              !! (freshClause.head.args === states.last)
              !! (freshClause.constraint)
              states += freshClause.body.head.args
            }

          val counter = createConstant

          def satIterationCount(lb : Int) : Boolean = {
            import IExpression._
            !! (or(for ((s, n) <- states.iterator.zipWithIndex; if n >= lb)
                   yield ((counter === n) & (s === finalState))))
            ??? == ProverStatus.Sat
          }

          push

          var cont = !satIterationCount(0)
          var k = 1

          while (cont) {
            pop
            val oldSize = states.size
            addN(k)
            k = k * 2
            push
            cont = !satIterationCount(oldSize)
          }

          val expandedClause = withCompleteModel { evaluator =>
            val cnt = evaluator.evalToInt(counter).intValueSafe
            var res : CounterExample = DagEmpty
            for (s <- states.take(cnt + 1).reverseIterator) {
              val headAtom = IAtom(cycle.head.head.pred, s map evaluator.apply)
              res = DagNode((headAtom, cycle.head), List(1), res)
            }
            res
          }

          pop

          expandedClause
        }
      }

    }

    (clauses ++ newClauses.map(_._1), hints, translator)
  }
}
