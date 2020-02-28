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

import ap.parser._

import scala.collection.mutable.{HashMap => MHashMap}

object PropagatingPreprocessor {
  import AbstractAnalyser.AbstractDomain

  /**
   * Abstract domain that also offers methods to inline the result
   * of static analysis into clauses.
   */
  trait InliningAbstractDomain extends AbstractDomain {
    /** Inline the abstract value of a clause body literal by possibly
     *  modifying the literal, and adding a further constraint to the clause */
    def inline(a : IAtom, value : Element) : (IAtom, IFormula)

    /** Augment a solution constraint by the information expressed in an
     *  abstract value */
    def augmentSolution(sol : IFormula, value : Element) : IFormula
  }

}

/**
 * A preprocessor that applies some abstract domain to derive
 * information about reachable states, then inlines that information
 * in the clauses.
 */
class PropagatingPreprocessor(
        _domain : PropagatingPreprocessor.InliningAbstractDomain)
      extends HornPreprocessor {
  import HornPreprocessor._
  import HornClauses.Clause
  import IExpression.{Predicate, ConstantTerm}
  import AbstractAnalyser._

  val name : String = _domain.name + " propagation"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val analyser          = new AbstractAnalyser(clauses, _domain)
    val abstractValues    = analyser.result
    val clauseBackMapping = new MHashMap[Clause, Clause]
    import analyser.domain

    var changed = false

    val newClauses =
      for (clause <- clauses) yield {
        val Clause(head, body, constraint) = clause
        var newConstraint = constraint

        var clauseChanged = false

        val newBody =
          for (a <- body) yield {
            val aValue = abstractValues(a.pred)
            val (newA, constr) = domain.inline(a, aValue)
            newConstraint = newConstraint &&& constr
            if (!(newA eq a))
              clauseChanged = true
            newA
          }

        if (!(newConstraint eq constraint))
          clauseChanged = true

        val newClause =
          if (clauseChanged) {
            changed = true
            Clause(head, newBody, newConstraint)
          } else {
            clause
          }
          
        clauseBackMapping.put(newClause, clause)
        newClause
      }

    ////////////////////////////////////////////////////////////////////////////

    val translator =
      if (changed) {
        new BackTranslator {
          import IExpression._

          def translate(solution : Solution) =
            solution transform {
              case (pred, sol) =>
                domain.augmentSolution(sol, abstractValues(pred))
            }
          
          def translate(cex : CounterExample) =
            for (p <- cex) yield (p._1, clauseBackMapping(p._2))
        }
      } else {
        IDENTITY_TRANSLATOR
      }

    (newClauses, hints, translator)
  }

}
