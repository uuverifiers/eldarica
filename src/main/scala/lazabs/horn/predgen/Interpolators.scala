/**
 * Copyright (c) 2023-2026 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.predgen

import lazabs.GlobalParameters
import lazabs.horn.abstractions.{AbstractionRecord, StaticAbstractionBuilder,
                                 VerificationHints, EmptyVerificationHints}
import AbstractionRecord.AbstractionMap
import StaticAbstractionBuilder.AbstractionType
import lazabs.horn.bottomup.HornClauses

/**
 * Default predicate generators implemented using interpolation.
 */
object Interpolators {
  import PredicateGenerator._

  /**
   * Predicate generator implemented using either standard tree
   * interpolation or disjunctive interpolation. Disjunctive
   * interpolation is used if the given clause DAG contains or-nodes.
   */
  object DagInterpolator extends PredicateGenerator {
    def apply(dag : ClauseDag) : Either[PredicateMap, Counterexample] =
      lazabs.horn.predgen.DagInterpolator.interpolatingPredicateGenCEXAndOr(dag)
  }

  /**
   * Predicate generator implemented using interpolation abstraction.
   */
  class TemplateInterpolator(absMap : AbstractionMap,
                             timeout : Long) extends PredicateGenerator {
    val intObj =
      lazabs.horn.predgen.TemplateInterpolator.
        interpolatingPredicateGenCEXAbsGen(absMap, timeout)
      
    def apply(dag : ClauseDag) : Either[PredicateMap, Counterexample] =
      intObj(dag)
  }

  /**
   * Construct a predicate generator according to the parameters.
   */
  def constructPredGen(params  : GlobalParameters,
                       clauses : Seq[HornClauses.Clause])
                               : PredicateGenerator =
    if (params.templateBasedInterpolation) {
      constructTemplatePredGen(clauses,
                               params.templateBasedInterpolationTimeout,
                               params.templateBasedInterpolationType,
                               EmptyVerificationHints)
    } else {
      DagInterpolator
    }

  /**
   * Construct a predicate generator 
   */
  def constructTemplatePredGen(clauses              : Seq[HornClauses.Clause],
                               interpolationTimeout : Int,
                               autoAbstractionType  : AbstractionType.Value,
                               hints                : VerificationHints)
                                                    : PredicateGenerator = {
    val abstractionBuilder =
      new StaticAbstractionBuilder(clauses, autoAbstractionType)
    val hintsAbstraction : AbstractionMap =
      if (hints.isEmpty)
        Map()
      else
        abstractionBuilder.loopDetector hints2AbstractionRecord hints
    val autoAbstractionMap =
      abstractionBuilder.abstractionRecords
    val fullAbstractionMap =
      AbstractionRecord.mergeMaps(hintsAbstraction, autoAbstractionMap)
    new TemplateInterpolator(fullAbstractionMap, interpolationTimeout)
  }

}
