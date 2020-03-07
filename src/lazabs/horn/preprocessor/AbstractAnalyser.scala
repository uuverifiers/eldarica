/**
 * Copyright (c) 2018-2020 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.bottomup.HornClauses
import HornClauses.Clause
import HornPreprocessor.Clauses

import ap.parser._
import IExpression.Predicate

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashMap => MHashMap, LinkedHashSet}

object AbstractAnalyser {

  /**
   * Abstract domains used during propagation
   */
  trait AbstractDomain {
    val name : String

    /** The type of abstract elements in this domain */
    type Element

    /** The abstract bottom element */
    def bottom(p : Predicate) : Element
    
    /** Compute the join (union) of two abstract elements */
    def join(a : Element, b : Element) : Element

    /** Test whether an abstract element is bottom */
    def isBottom(b : Element) : Boolean

    /** Create an abstract transformer for the given clause */
    def transformerFor(clause : Clause) : AbstractTransformer[Element]
  }

  /**
   * Transformer that computes the abstract value of a clause head given
   * the abstract values for the body literals.
   */
  trait AbstractTransformer[Element] {
    def transform(bodyValues : Seq[Element]) : Element
  }
}

class AbstractAnalyser[Domain <: AbstractAnalyser.AbstractDomain]
                      (clauses : Clauses, val domain : Domain) {

  val result : GMap[Predicate, domain.Element] = {
    val allPreds = HornClauses allPredicates clauses

    val clauseSeq = clauses.toVector
    val clausesWithBodyPred =
      (for ((clause, n) <- clauseSeq.zipWithIndex;
            if clause.head.pred != HornClauses.FALSE;
            IAtom(p, _) <- clause.body)
       yield (p, n)) groupBy (_._1)

    val propagators =
      for (clause <- clauseSeq) yield (domain transformerFor clause)

    val abstractValues = new MHashMap[Predicate, domain.Element]
    for (p <- allPreds)
      abstractValues.put(p, domain bottom p)

    val clausesTodo = new LinkedHashSet[Int]

    // start with the clauses with empty body
    for ((Clause(IAtom(p, _), Seq(), _), n) <-
           clauseSeq.iterator.zipWithIndex;
         if p != HornClauses.FALSE)
      clausesTodo += n
      
    while (!clausesTodo.isEmpty) {
      val nextID = clausesTodo.head
      clausesTodo -= nextID
      val Clause(head, body, _) = clauseSeq(nextID)

      val bodyValues =
        for (IAtom(p, _) <- body) yield abstractValues(p)
      val newAbstractEl =
        propagators(nextID) transform bodyValues

      if (!(domain isBottom newAbstractEl)) {
        val headPred = head.pred
        val oldAbstractEl = abstractValues(headPred)
        val jointEl = domain.join(oldAbstractEl, newAbstractEl)

        if (jointEl != oldAbstractEl) {
          abstractValues.put(headPred, jointEl)
          for ((_, n) <- clausesWithBodyPred.getOrElse(headPred, List()))
            clausesTodo += n
        }
      }
    }

    abstractValues
  }

}
