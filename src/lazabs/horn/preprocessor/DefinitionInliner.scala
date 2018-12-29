/**
 * Copyright (c) 2011-2018 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.bottomup.Util.Dag

import ap.theories.ModuloArithmetic
import ap.basetypes.IdealInt
import ap.parser._
import IExpression._
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

/**
 * Inline simple definitions found in the clause constraints
 */
object DefinitionInliner extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "constraint simplification"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val clauseMapping = new MHashMap[Clause, Clause]

    val newClauses =
      for (clause <- clauses;
           newClause = simpClause(clause);
           if newClause != null)
      yield {
        clauseMapping.put(newClause, clause)
        newClause
      }

    val translator = new BackTranslator {
      def translate(solution : Solution) =
        solution
      def translate(cex : CounterExample) =
        for (p <- cex) yield (p._1, clauseMapping(p._2))
    }

    (newClauses, hints, translator)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def simpClause(clause : Clause) : Clause = {
    val Clause(head, oriBody, constraint) = clause
    
    val headSyms = SymbolCollector constants head
    var body = oriBody

    var conjuncts = LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)

    if (conjuncts exists (_.isFalse))
      return null

    val replacement = new MHashMap[ConstantTerm, ITerm]
    val replacedConsts = new MHashSet[ConstantTerm]
    val conjunctsToKeep = new ArrayBuffer[IFormula]

    var changed = false

    var cont = true
    while (cont) {
      val remConjuncts = conjuncts filter {

        // special case of equation between constants
        case eq@Eq(left@IConstant(c), right@IConstant(d)) =>
          if (c == d) {
            // can be dropped
            false

          } else if (!(replacedConsts contains c) &&
                     !(replacedConsts contains d)) {

            if (!(headSyms contains c)) {
              replacement.put(c, right)
            } else if (!(headSyms contains d)) {
              replacement.put(d, left)
            } else {
              conjunctsToKeep += eq
              replacement.put(c, right)
            }

            replacedConsts += c
            replacedConsts += d
            false

          } else {
            // keep this one
            true
          }

        // case of general equations
        case eq@Eq(left, right) =>
          if (left == right) {
            // can be dropped
            false
          } else {
            val leftConsts = SymbolCollector constants left
            val rightConsts = SymbolCollector constants right
            val eqConsts = leftConsts ++ rightConsts

            if (Seqs.disjoint(eqConsts, replacedConsts)) {
              (left, right) match {
                case (IConstant(c), _)
                    if !(rightConsts contains c) && !(headSyms contains c) => {
                  replacement.put(c, right)
                  replacedConsts ++= eqConsts
                  false
                }
                case (_, IConstant(c))
                    if !(leftConsts contains c) && !(headSyms contains c) => {
                  replacement.put(c, left)
                  replacedConsts ++= eqConsts
                  false
                }
                case (IConstant(c), _)
                    if !(rightConsts contains c) => {
                  conjunctsToKeep += eq
                  replacement.put(c, right)
                  replacedConsts ++= eqConsts
                  false
                }
                case (_, IConstant(c))
                    if !(leftConsts contains c) => {
                  conjunctsToKeep += eq
                  replacement.put(c, left)
                  replacedConsts ++= eqConsts
                  false
                }
                case _ =>
                  // then keep this conjunct
                  true
              }
            } else {
              true
            }
          }
        case _ => true
      }

      if (replacement.isEmpty) {
        cont = false
      } else {
        changed = true

        val lastSize = conjuncts.size

        conjuncts =
          (for (f <- remConjuncts;
                newF = SimplifyingConstantSubstVisitor(f, replacement);
                if !newF.isTrue)
           yield newF) ++ conjunctsToKeep

        if (conjuncts exists (_.isFalse))
          return null

        body =
          for (a <- body)
          yield SimplifyingConstantSubstVisitor(a, replacement)
                  .asInstanceOf[IAtom]

        replacement.clear
        replacedConsts.clear
        conjunctsToKeep.clear

        cont = (conjuncts.size < lastSize)
      }
    }

    if (changed)
      Clause(head, body, and(conjuncts))
    else
      clause
  }

}
