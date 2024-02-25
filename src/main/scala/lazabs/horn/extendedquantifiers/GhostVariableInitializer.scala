/**
 * Copyright (c) 2023 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
 * All rights reserved.
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

package lazabs.horn.extendedquantifiers

import ap.parser.IExpression._
import ap.parser.IFormula
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.extendedquantifiers.Util.ExtendedQuantifierApp
import lazabs.horn.extendedquantifiers.GhostVariableAdder._
import lazabs.horn.extendedquantifiers.theories.AbstractExtendedQuantifier
import lazabs.horn.preprocessor._
import lazabs.horn.preprocessor.HornPreprocessor._

/**
 * Initializes ghost variables added by [[GhostVariableAdder]] using
 * the initializers [[InstrumentationOperator.ghostVarInitialValues]].
 */
class GhostVariableInitializer(
  predToGhostVarIndsPerExqApp  : Map[ExtendedQuantifierApp, Map[Predicate, GhostVariableInds]],
  exqToInstrumentationOperator : Map[AbstractExtendedQuantifier, InstrumentationOperator])
  extends HornPreprocessor {
  override val name: String = "Initializing ghost variables"

  override def process(clauses: Clauses,
                       hints: VerificationHints,
                       frozenPredicates: Set[Predicate]):
  (Clauses, VerificationHints, HornPreprocessor.BackTranslator) = {
    val entryClauses = clauses.filter(_.body isEmpty)

    val newClauses = for (clause <- clauses) yield {
      if (entryClauses contains clause) {
        val newConjuncts = new collection.mutable.ArrayBuffer[IFormula]
        for ((exqApp, predToGhostVarInds) <- predToGhostVarIndsPerExqApp) {
          val instOp = exqToInstrumentationOperator(exqApp.exTheory)

          for (ghostVarToInd <- predToGhostVarInds(clause.head.pred))
            for ((ghostVar, ghostInd) <- ghostVarToInd)
              instOp.ghostVarInitialValues get ghostVar match {
                case Some(initialValue) =>
                  newConjuncts += clause.head.args(ghostInd) === initialValue
                case None               => // no initialization needed
              }
        }
        val newConstraint = clause.constraint &&&
          newConjuncts.fold(i(true))((c1, c2) => c1 &&& c2)
        Clause(clause.head, clause.body, newConstraint)
      } else {
        clause
      }
    }
    val clauseBackMapping = (newClauses zip clauses).toMap

    val translator = new BackTranslator {
      def translate(solution : Solution) = solution

      def translate(cex : CounterExample) =
        for (p <- cex) yield (p._1, clauseBackMapping(p._2))
    }

    (newClauses, hints, translator)
  }
}
