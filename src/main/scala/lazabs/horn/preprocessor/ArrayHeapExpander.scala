/**
 * Copyright (c) 2025 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import ap.theories.heaps.{ArrayHeap, Heap}
import ap.parser._
import ap.types.{MonoSortedIFunction, MonoSortedPredicate}
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts

import scala.collection.mutable.{ArrayBuffer, LinkedHashMap, HashMap => MHashMap}

/**
 * Preprocessor that adds expands arguments of ArrayHeap type.
 */
class ArrayHeapExpander extends ArgumentExpander {

  import IExpression._
  import HornPreprocessor._
  import Heap._

  val name = "adding heap size arguments"

  def expand(pred : Predicate, argNum : Int, sort : Sort)
           : Option[(Seq[(ITerm, Sort, String)], Option[ITerm])] = {
    val HeapRelatedSort(heap : ArrayHeap) = sort
    assert(sort == heap.HeapSort)
    val ctor = heap.heapPair
    val sels = List(heap.heapContents, heap.heapSize)
    Some((for (f <- sels) yield (f(v(0)), f.resSort, f.name),
          Some(ctor((for (n <- 0 until sels.size) yield v(n)) : _*))))
  }

  def isExpandableSort(s : Sort) : Boolean =
    s match {
      case HeapRelatedSort(heap : ArrayHeap) if s == heap.HeapSort => true
      case _ => false
    }

  override def postprocessCEXAtom(atom : IAtom) : IAtom = {
    val sorts = predArgumentSorts(atom.pred)
    val newArgs =
      for ((a, s) <- atom.args zip sorts) yield s match {
        case HeapRelatedSort(heap : ArrayHeap) if s == heap.HeapSort =>
          a match {
            case IFunApp(heap.heapPair, _) =>
              heap.HeapSort.translateArrayTerm(a)
            case _ => a
          }
        case _ => a
      }
    IAtom(atom.pred, newArgs)
  }

}

object ArrayHeapConstraintExpander extends HornPreprocessor {

  import IExpression._
  import HornPreprocessor._

  val name : String = "expanding heap constraints"
  
  override def isApplicable(clauses : Clauses,
                            frozenPredicates : Set[Predicate]) : Boolean =
    frozenPredicates.isEmpty &&
    (clauses exists { clause =>
       clause.theories exists { _.isInstanceOf[ArrayHeap] } })

  def process(clauses : Clauses, hints : VerificationHints,
              frozenPredicates : Set[Predicate])
             : (Clauses, VerificationHints, BackTranslator) = {

    val clausePairs =
      for (clause <- clauses) yield {
        val heaps = clause.theories.filter(_.isInstanceOf[ArrayHeap])
        val Clause(head, body, constraint) = clause
        val constraint2 =
          ~heaps.foldLeft(~constraint) { case (c, h) => h.iPreprocess(c, null)._1 }
        val constraint3 =
          or(for (INamedPart(name, f) <- PartExtractor(constraint2)) yield f)

//        println(s"before: $constraint")
//        println(s"after: $constraint3")

        val newClause =
          Clause(head, body, constraint3)
        clause -> newClause
      }

    val clauseBackMapping =
      (for ((a, b) <- clausePairs.iterator) yield (b, a)).toMap

    val backTranslator = new BackTranslator {
      def translate(solution : Solution) = solution

      def translate(cex : CounterExample) =
        for (p <- cex) yield {
          val (atom, clause) = p
          (atom, clauseBackMapping(clause))
        }
    }

    (clausePairs.unzip._2, hints, backTranslator)
  }

}
