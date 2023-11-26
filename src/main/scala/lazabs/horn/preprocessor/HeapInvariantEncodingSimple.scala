/**
 * Copyright (c) 2023 Zafer Esen. All rights reserved.
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

import ap.parser._
import IExpression._
import ap.theories.{Heap, Theory}
import ap.theories.Heap.HeapSort
import ap.types.MonoSortedPredicate
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

class HeapInvariantEncodingSimple extends HornPreprocessor {
  import HornPreprocessor._

  override val name : String = "Heap invariants encoder (simple)"

  /**
   * HeapInvariantEncodingSimple is only applicable when the input CHCs contain
   * exactly one heap theory.
   */
  override def isApplicable(clauses          : Clauses,
                            frozenPredicates : Set[Predicate]) : Boolean = {
    clauses.flatMap(c => c.theories).toSet.nonEmpty
  }

  override def process(clauses : Clauses,
                       hints : VerificationHints,
                       frozenPredicates : Set[Predicate])
  : (Clauses, VerificationHints, HornPreprocessor.BackTranslator) = {
    val heapTheories = clauses.flatMap(c => c.theories)
                              .filter(theory => theory.isInstanceOf[Heap])
                              .map(theory => theory.asInstanceOf[Heap])
                              .toSet

    clauses.foreach(println)
    var currentClauses = clauses

/**
 * Why normalization is needed: consider the following clause with two heap ops.
 * Each read replaces a clause with two clauses.

  head :- read1 & read2

 * The following translation is weak (num_reads*2 clauses), because each
 * path to "head" only considers one of the reads (i.e., the invariants of
 * other reads are not propagated even when those reads are valid).

  head :- read1 & read2 &  valid1 & Inv1
  head :- read1 & read2 & !valid1
  head :- read1 & read2 &  valid2 & Inv2
  head :- read1 & read2 & !valid2

 * The stronger encoding would be as follows, but grows the number of clauses
 * exponentially in the number of reads (i.e., num_reads^^2 clauses):

  head :- read1 & read2 & valid1  & Inv1 & valid2 & Inv2
  head :- read1 & read2 & valid1  & Inv1 & !valid2
  head :- read1 & read2 & !valid1        & valid2 & Inv2
  head :- read1 & read2 & !valid1        & !valid2

 * Normalization (i.e., one clause per heap operation) would in this case first
 * split the original clause into num_reads, and then transform each clause
 * with a read into two clauses, leading to num_reads*2 clauses.
*/

    // Each heap theory
    for (heap <- heapTheories) {
      val newClauses = new ArrayBuffer[HornClauses.Clause]

      // Define an invariant for this heap
      val inv = new MonoSortedPredicate(s"Inv_${heap.HeapSort.name}",
                                        Seq(heap.AddressSort, heap.ObjectSort))
      for (clause <- currentClauses) {
        val conjuncts =
          LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)
        def appearsInHead(c : ConstantTerm) : Boolean =
          clause.head.args.contains(IConstant(c))
        def appearsInBody(c : ConstantTerm) : Boolean =
          clause.body.exists(a => a.args.contains(IConstant(c)))

        for (conjunct <- conjuncts) {
          conjunct match {
            // allocHeap(h0, o) == h1: push inv(newAddr(h0, o), o)
            case Eq(IFunApp(heap.allocHeap, Seq(IConstant(h0), IConstant(o))),
                    IConstant(h1)) if appearsInBody(h0) && appearsInHead(h1) =>
              val a = heap.allocAddr(h0, o)
              newClauses += Clause(inv(a, o), clause.body, clause.constraint)

            // write(h0, a, o) == h1: push inv(a, o) if valid(h0, a)
            case Eq(IFunApp(heap.write,
                            Seq(IConstant(h0), IConstant(a), IConstant(o))),
                    IConstant(h1)) if appearsInBody(h0) && appearsInHead(h1) =>

              newClauses += Clause(inv(a, o), clause.body,
                                   clause.constraint &&& heap.isAlloc(h0, a))
            case Eq(IFunApp(heap.read,
                            Seq(IConstant(h), IConstant(a))),
                    IConstant(o)) if appearsInBody(h) =>
              newClauses += Clause(inv(a, o), clause.body,
                                   clause.constraint &&& heap.isAlloc(h, a))
            case _ =>
          }
        }
      }
      currentClauses = newClauses
    }

    (currentClauses, hints, ???)
  }
}
