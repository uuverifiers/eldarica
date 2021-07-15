/**
 * Copyright (c) 2021 Philipp Ruemmer. All rights reserved.
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
import ap.basetypes.IdealInt

import lazabs.horn.bottomup.HornClauses
import HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.abstractions.VerificationHints

/**
 * A class for adding initial predicates for all possible values of
 * predicate arguments ranging over finite domains. Such predicates
 * will enable the CEGAR engine to track the values of the arguments
 * precisely.
 */
class FiniteDomainPredicates(domainSizeBound : Int) extends HornPreprocessor {
  import HornPreprocessor._
  import IExpression._

  val name : String = "adding finite domain init. predicates"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val allPreds =
      HornClauses allPredicates clauses
    val newHints =
      (for (p <- allPreds.iterator) yield {
         val argSorts = predArgumentSorts(p)
         val preds =
           (for ((s, n) <- argSorts.iterator.zipWithIndex;
                 f <- (s match {
                         case Sort.MultipleValueBool =>
                           Iterator(eqZero(v(n, s)), !eqZero(v(n, s)))
                         case _ => s.cardinality match {
                           case Some(IdealInt(size)) if size <= domainSizeBound =>
                             for (t <- s.individuals.iterator) yield v(n, s) === t
                           case _ =>
                             Iterator.empty
                         }
                       }))
            yield VerificationHints.VerifHintInitPred(f)).toVector
         p -> preds
       }).toMap

    (clauses, hints ++ VerificationHints(newHints), IDENTITY_TRANSLATOR)
  }

  override def isApplicable(clauses : Clauses) : Boolean =
    (HornClauses allPredicates clauses) exists {
      p => predArgumentSorts(p) exists { s => s.cardinality.isDefined }
    }

}
