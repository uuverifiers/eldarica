/**
 * Copyright (c) 2024 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
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
package lazabs.horn.extendedquantifiers.theories

import ap.parser.IExpression.Sort
import ap.parser._
import ap.terfor.ConstantTerm
import ap.theories.ExtArray
import ap.types.MonoSortedIFunction

/**
 * This theory introduces a theory for the sole purpose of making available
 * an extended quantifier function (fun). fun should be replaced with the
 * correct encoding during the preprocessing of the input clauses.
 *
 * @param name            : name of the aggregation function fun
 * @param arrayTheory     : array theory for this extended quantifier
 * @param identity        : term to return for empty ranges
 * @param reduceOp        : reduce operator, e.g.: def sum(a, b) = a + b
 * @param invReduceOp     : only for cancellative reduce operations
 * @param rangeFormulaLo  : an optional range expression to be used when
 *                          rewriting the extended quantifier assertion. This
 *                          relaxes the requirement that ranges must exactly
 *                          match. Given (lo, i, p_agg),
 *                          default is lo === i, but for
 *                          instance one can specify lo <= i. The first term
 *                          must be ghost variable tracking lo, and the
 *                          second argument must be lo from the assertion.
 * @param rangeFormulaHi  : similar to above, but for hi.
 * @param predicate       : a predicate to apply during aggregation.
 *                          argument terms are (x, i) in a[i] = x
 */
class ExtendedQuantifierWithPredicate(
  name           : String,
  arrayTheory    : ExtArray,
  identity       : ITerm, // todo: see what ACSL does here - we maybe do
                          //       not really consider monoids but semi-groups
  reduceOp       : (ITerm, ITerm) => ITerm,
  invReduceOp    : Option[(ITerm, ITerm) => ITerm],
  rangeFormulaLo : Option[(ITerm, ITerm, ITerm) => IFormula],
  rangeFormulaHi : Option[(ITerm, ITerm, ITerm) => IFormula],
  val predicate  : (ITerm, ITerm) => ITerm,
  val alienConstants : Seq[ConstantTerm]
) extends AbstractExtendedQuantifier(
    name = name, arrayTheory = arrayTheory, identity = identity,
    reduceOp = reduceOp, invReduceOp = invReduceOp,
    rangeFormulaLo = rangeFormulaLo, rangeFormulaHi = rangeFormulaHi) {
  /**
   * ''alien'' terms refer to unbound variables of
   * [[ExtendedQuantifierWithPredicate.predicate]] (when this predicate is provided).
   * This `predicate` is of the form `p(o, i)`, where `o` is the
   * written/read object at index `i`.
   * Example: in `p(o, i): o = i + c`, `c` is an alien term.
   */
  val alienConstantSorts : Seq[Sort] = alienConstants.map(
    c => Sort.sortOf(IConstant(c)))

  // morphism : (a : array, lo : Int, hi : Int) => Obj
  override val morphism = MonoSortedIFunction(
    name,
    List(arrayTheory.sort, arrayIndexSort, arrayIndexSort) ++ alienConstantSorts,
    arrayTheory.objSort,
    partial = false,
    relational = false)

  def applyMorphism(a : ITerm, lo : ITerm, hi : ITerm) =
    IFunApp(morphism, Seq(a, lo, hi) ++ alienConstants.map(IConstant))
    override val theoryAxioms : IFormula = IExpression.i(true)
//  override val theoryAxioms: IFormula = {
//    import ap.parser.IExpression._
//    arrayTheory.sort.all(
//      a =>
//        // TODO
//        //  1. systematic splitting - eliminate overlaps
//        //  2. propagate summation across stores
//        arrayIndexSort.all(
//          lo =>
//            arrayIndexSort.all(hi =>
//              trig((lo < hi) ==> (applyMorphism(a, lo, hi) ===
//                     reduceOp(applyMorphism(a, lo+1, hi), predicate(a, lo))),
//                   applyMorphism(a, lo, hi))))) & // triggers
////    arrayTheory.sort.all(
////      a =>
////        arrayIndexSort.all(
////          lo =>
////            arrayIndexSort.all(
////              hi =>
////                trig((lo < hi) ==> (fun(a, lo, hi) ===
////                                    reduceOp(fun(a, lo, hi-1), select(a,
////                                                                      hi-1))),
////                     fun(a, lo, hi))))) &
//      arrayTheory.sort.all(a => arrayIndexSort.all(lo =>
//        arrayIndexSort.all(hi =>
//          trig((lo >= hi) ==> (applyMorphism(a, lo, hi) === identity),
//               applyMorphism(a, lo, hi)))))
//  }

  //////////////////////////////////////////////////////////////////////////////
  // SMT Lineariser and Parser
  /**
   * Print an SMT-LIB declaration of this theory.
   */
//  override def printSMTDeclaration : Unit = ???

  /**
   * Translate theory morphism applications.
   */
//  override def translateSMTOperatorAST(
//    sym       : SymbolRef,
//    arguments : Seq[(Int) => (IExpression, SMTTypes.SMTType)],
//    polarity  : Int)
//  : Option[(IExpression, SMTTypes.SMTType)] = Some(???)
}