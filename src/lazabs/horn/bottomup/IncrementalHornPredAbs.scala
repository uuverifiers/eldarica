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

package lazabs.horn.bottomup

import ap.parser._
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction

import Util._
import DisjInterpolator._

/**
 * An incremental version of <code>HornPredAbs</code>. This class is
 * optimised to enable efficient repeated analysis of variants of the
 * same set of clauses. Variants are obtained by substituting some of
 * the relation symbols with concrete formulas.
 */
class IncrementalHornPredAbs
                 [CC <% HornClauses.ConstraintClause]
                 (iClauses : Iterable[CC],
                  initialPredicates : Map[Predicate, Seq[IFormula]],
                  substitutableSyms : Set[Predicate],
                  predicateGenerator : Dag[AndOrNode[NormClause, Unit]] =>
                                       Either[Seq[(Predicate, Seq[Conjunction])],
                                              Dag[(IAtom, NormClause)]],
                  counterexampleMethod : CEGAR.CounterexampleMethod.Value =
                                           CEGAR.CounterexampleMethod.FirstBestShortest) {

  lazabs.GlobalParameters.get.setupApUtilDebug

  private val outStream =
     if (lazabs.GlobalParameters.get.logStat)
       Console.err
     else
       HornWrapper.NullStream

  val baseContext : HornPredAbsContext[CC] =
    Console.withOut(outStream) {
      new HornPredAbsContextImpl(iClauses,
                                 intervalAnalysisIgnoredSyms =
                                   substitutableSyms)
    }

  /**
   * Apply the given substitution to all clauses, and check
   * satisfiability. The formula for given for the substituted
   * predicates can contain free variables <code>v(0), ...,
   * v(n-1)</code>, which are replaced with the predicate arguments.
   */
  def checkWithSubstitution(subst : Map[Predicate, Conjunction])
                          : Either[Map[Predicate, Conjunction],
                                   Dag[(IAtom, CC)]] = {
    assert((subst.keys forall substitutableSyms) &&
           (subst forall { case (p, c) =>
              c.constants.isEmpty &&
              (c.variables forall { v => v.index < p.arity }) }))

    val rsSubst =
      (for ((p, c) <- subst) yield (baseContext.relationSymbols(p), c)).toMap

    val context = new DelegatingHornPredAbsContext(baseContext) {
      override val relationSymbols =
        baseContext.relationSymbols -- subst.keys

      override val normClauses =
        for ((clause, cc) <- baseContext.normClauses;
             newClause = clause substituteRS rsSubst;
             if !newClause.constraint.isFalse)
        yield (newClause, cc)

      if (lazabs.GlobalParameters.get.log)
        println("Testing substitution, remaining clauses: " + normClauses.size)

      override val relationSymbolOccurrences = computeRSOccurrences
      override val hasher                    = createHasher
      override val clauseHashIndexes         = computeClauseHashIndexes

      // TODO: run AI again?
    }

    // TODO: can we sometimes reuse predicates?

    val predStore = new PredicateStore(context)
    import predStore._

    predStore.addIPredicates(initialPredicates)

    val cegar = new CEGAR(context, predStore,
                          predicateGenerator, counterexampleMethod)
    cegar.rawResult
  }

}
