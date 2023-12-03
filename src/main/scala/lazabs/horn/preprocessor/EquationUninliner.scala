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

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}
import ap.parser._
import ap.parser.IExpression.{Predicate, and}
import ap.types.{Sort, SortedConstantTerm}
import lazabs.horn.preprocessor.HornPreprocessor._
import lazabs.horn.bottomup.HornClauses._

/**
 * A very simple preprocessor that ensures that the constant term on the RHS of
 * every function application is distinct. E.g.,
 *   f(a) = c, g(b) = c
 * gets tranlated into
 *   f(a) = c, g(b) = c1, c = c1.
 * This introduces n-1 new constants for n such applications.
 * This translator can be useful for obtaining a normal form. For instance when
 * creating a clause graph, it ensures each such constant can have one
 * incoming edge at most.
 * Requires: function applications in the form f(x_bar) = b with b : IConstant.
 * Ensures: distinct IConstant RHS for all function applications in a clause..
 */
class EquationUninliner extends HornPreprocessor {
  override val name : String = "uninlining equations"
  override def process(clauses          : Clauses,
                       hints            : VerificationHints,
                       frozenPredicates : Set[Predicate]) : (Clauses,
    VerificationHints, HornPreprocessor.BackTranslator) = {

    val clauseBackMapping = new MHashMap[Clause, Clause]

    for (clause <- clauses) {
      val conjuncts =
        LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)

      val newConjuncts = new ArrayBuffer[IFormula]

      val constantCountAsRhs = new MHashMap[IConstant, Int]
      clause.constants.foreach(
        constant => constantCountAsRhs += IConstant(constant) -> 0)

      for (conjunct <- conjuncts) conjunct match {
        case eq@IEquation(IFunApp(_, _), c@IConstant(_)) =>
          if (constantCountAsRhs(c) > 0) {
            // Need a new constant.
            val newConstant = IConstant(new SortedConstantTerm(
              s"${c.c.name}_${constantCountAsRhs(c)}", Sort.sortOf(c)))
            newConjuncts += eq.left === newConstant &&& c === newConstant
            constantCountAsRhs(c) += 1
          } else {
            constantCountAsRhs(c) += 1
            // Mo need to introduce a new constant, keep old conjunct.
            newConjuncts += eq
          }
        case _ =>
          newConjuncts += conjunct
      }

      val newClause = Clause(clause.head, clause.body,and(newConjuncts))
      clauseBackMapping += newClause -> clause
    }

    val backTranslator = new BackTranslator {
      override def translate(solution : Solution) : Solution = solution
      override def translate(cex : CounterExample) : CounterExample =
        for (p <- cex) yield {
          val (a, clause) = p
          (a, clauseBackMapping(clause))
        }
    }

    (clauseBackMapping.keys.toSeq, hints, backTranslator)
  }
}
