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

import ap.Signature.PredicateMatchConfig
import ap.parser.IExpression.{Predicate, Sort, i}
import ap.parser.{IFormula, IFunction, ITerm, SymbolCollector}
import ap.proof.theoryPlugins.Plugin
import ap.terfor.{ConstantTerm, Formula}
import ap.terfor.conjunctions.Conjunction
import ap.theories.{ExtArray, Theory, TheoryRegistry}
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

 * The following three parameters are typically used with general quantifiers.
 * @param predicate       : a predicate to apply during aggregation, this also
 *                          implies that the ghost variable used in aggregation
 *                          will be a predicate
 * @param rangeFormulaLo  : an optional range expression to be used when
 *                          rewriting the extended quantifier assertion. This
 *                          relaxes the requirement that ranges must exactly
 *                          match. Given (lo, i, p_agg),
 *                          default is lo === i, but for
 *                          instance one can specify lo <= i. The first term
 *                          must be ghost variable tracking lo, and the
 *                          second argument must be lo from the assertion.
 * @param rangeFormulaHi  : similar to above, but for hi.
 */
class ExtendedQuantifier(
    name:               String,
    val arrayTheory:    ExtArray,
    val identity:       ITerm, // todo: see what ACSL does here - we maybe do not really consider monoids but semi-groups
    val reduceOp:       (ITerm, ITerm) => ITerm,
    val invReduceOp:    Option[(ITerm, ITerm) => ITerm],
    val predicate:      Option[(ITerm, ITerm) => ITerm],
    val rangeFormulaLo: Option[(ITerm, ITerm, ITerm) => IFormula],
    val rangeFormulaHi: Option[(ITerm, ITerm, ITerm) => IFormula])
// a predicate in case of general quantifiers, argument terms are (x, i) in a[i] = x
    extends Theory {

  val arrayIndexSort: Sort = arrayTheory.indexSorts.head
  if (arrayTheory.indexSorts.length > 1)
    throw new Exception(
      "Currently only 1-d integer indexed arrays are supported!")

  // this theory depends on the theory of extensional arrays with specified sorts
  override val dependencies: Iterable[Theory] = List(arrayTheory)

  // alien constants (if any) in the predicate (if any)
  val alienConstantsInPredicate: Seq[ConstantTerm] = {
    predicate match {
      case Some(pred) =>
        val t1 = new ConstantTerm("t1")
        val t2 = new ConstantTerm("t2")
        SymbolCollector.constantsSorted(pred(t1, t2)) diff Seq(t1, t2)
      case None => Nil
    }
  }

  // fun : (a : array, lo : Int, hi : Int) => Obj
  val fun = MonoSortedIFunction(
    name,
    List(arrayTheory.sort, arrayIndexSort, arrayIndexSort),
    arrayTheory.objSort,
    partial = false,
    relational = false)

  /**
   * The theory introduces the single extended quantifier function.
   */
  override val functions: Seq[IFunction] = Seq(fun)

  val theoryAxioms: IFormula = {
    import ap.parser.IExpression._
    import arrayTheory._
    arrayTheory.sort.all(
      a =>
        // TODO
        //  1. systematic splitting - eliminate overlaps
        //  2. propagate summation across stores
        arrayIndexSort.all(
          lo =>
            arrayIndexSort.all(hi =>
              trig((lo < hi) ==> (fun(a, lo, hi) ===
                     reduceOp(fun(a, lo + 1, hi), select(a, lo))),
                   fun(a, lo, hi))))) & // triggers
//    arrayTheory.sort.all(
//      a =>
//        arrayIndexSort.all(
//          lo =>
//            arrayIndexSort.all(
//              hi =>
//                trig((lo < hi) ==> (fun(a, lo, hi) ===
//                                    reduceOp(fun(a, lo, hi-1), select(a,
//                                                                      hi-1))),
//                     fun(a, lo, hi))))) &
      arrayTheory.sort.all(
        a =>
          arrayIndexSort.all(
            lo =>
              arrayIndexSort.all(hi =>
                trig((lo >= hi) ==> (fun(a, lo, hi) ===
                       identity),
                     fun(a, lo, hi)))))
  }

  val (funPredicates, axioms1, order, functionTranslation) = Theory.genAxioms(
    theoryFunctions = functions,
    theoryAxioms = theoryAxioms,
    otherTheories = dependencies.toList)

  override val functionalPredicates: Set[Predicate] = funPredicates.toSet
  override val predicates:           Seq[Predicate] = funPredicates
  override val functionPredicateMapping: Seq[(IFunction, Predicate)] =
    functions zip functionalPredicates

  override val predicateMatchConfig:     PredicateMatchConfig = Map()
  override val triggerRelevantFunctions: Set[IFunction]       = functions.toSet
  override val axioms:                   Formula              = axioms1
  override val totalityAxioms:           Formula              = Conjunction.TRUE
  override def plugin:                   Option[Plugin]       = None

  override def isSoundForSat(theories: Seq[Theory],
                             config:   Theory.SatSoundnessConfig.Value): Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary  => true
      case Theory.SatSoundnessConfig.Existential => true
      case _                                     => false
    }
}

object ExtendedQuantifier {

  /**
   * Extractor recognising the <code>fun</code> function of
   * any ExtendedQuantifier theory.
   */
  object ExtendedQuantifierFun {
    def unapply(f: IFunction): Option[ExtendedQuantifier] =
      (TheoryRegistry lookupSymbol f) match {
        case Some(t: ExtendedQuantifier) if f == t.fun => Some(t)
        case _ => None
      }
  }

}
