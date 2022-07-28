/**
 * Copyright (c) 2022 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import ap.Signature.PredicateMatchConfig
import ap.parser._
import ap.parser.IExpression._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.Formula
import ap.terfor.conjunctions.Conjunction
import ap.theories._
import ap.types.MonoSortedIFunction

/**
 * This theory introduces a theory for the sole purpose of making available
 * an extended quantifier function (fun). fun should be replaced with the
 * correct encoding during the preprocessing of the input clauses.
 * @param name            : name of the aggregation function fun
 * @param arrayObjectSort : array object sort
 * @param reduceOp        : reduce operator, e.g.: def sum(a, b) = a + b
 * @param invReduceUp     : only for cancellative reduce operations
 */
class ExtendedQuantifier(name            : String,
                         arrayObjectSort : Sort,
                         reduceOp        : (ITerm, ITerm) => ITerm,
                         invReduceOp : Option[(ITerm, ITerm) => ITerm])
  extends Theory {

  // currently we fix the index sort to Sort.Integer, object sort is parameterised.
  val arrayIndexSort : Sort = Sort.Integer

  val redOp = reduceOp
  val invRedOp = invReduceOp

  val arrayTheory = ExtArray(Seq(Sort.Integer), arrayObjectSort)

  // this theory depends on the theory of extensional arrays with specified sorts
  override val dependencies: Iterable[Theory] = List(arrayTheory)

  // fun : (a : array, lo : Int, hi : Int) => Obj
  val fun = MonoSortedIFunction(
    name,
    List(arrayTheory.sort, arrayIndexSort, arrayIndexSort),
    arrayObjectSort,
    partial = false, relational = false)

  /**
   * The theory introduces the single extended quantifier function.
   * Since this function will be preprocessed away, the rest of the overrides
   * are not needed.
   */
  override val functions: Seq[IFunction] = Seq(fun)
  override val predicates: Seq[Predicate] = Nil
  override val functionPredicateMapping: Seq[(IFunction, Predicate)] = Nil
  override val functionalPredicates: Set[Predicate] = Set()
  override val predicateMatchConfig: PredicateMatchConfig = Map()
  override val triggerRelevantFunctions: Set[IFunction] = Set()
  override val axioms: Formula = Conjunction.TRUE
  override val totalityAxioms: Formula = Conjunction.TRUE
  override def plugin: Option[Plugin] = None
}

object ExtendedQuantifier {
  /**
   * Extractor recognising the <code>fun</code> function of
   * any ExtendedQuantifier theory.
   */
  object ExtendedQuantifierFun {
    def unapply(f : IFunction) : Option[ExtendedQuantifier] =
      (TheoryRegistry lookupSymbol f) match {
        case Some(t : ExtendedQuantifier) if f == t.fun => Some(t)
        case _ => None
      }
  }
}