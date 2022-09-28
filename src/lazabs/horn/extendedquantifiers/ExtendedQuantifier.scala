/**
 * Copyright (c) 2022 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
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
import ap.parser.{IFunction, ITerm}
import ap.proof.theoryPlugins.Plugin
import ap.terfor.Formula
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
 */
class ExtendedQuantifier(name            : String,
                         val arrayTheory : ExtArray,
                         val identity    : ITerm,
                         val reduceOp    : (ITerm, ITerm) => ITerm,
                         val invReduceOp : Option[(ITerm, ITerm) => ITerm])
  extends Theory {

  val arrayIndexSort : Sort = arrayTheory.indexSorts.head
  if (arrayIndexSort != Sort.Integer || arrayTheory.indexSorts.length > 1)
    throw new Exception("Currently only 1-d integer indexed arrays are supported!")

  // this theory depends on the theory of extensional arrays with specified sorts
  override val dependencies: Iterable[Theory] = List(arrayTheory)

  // fun : (a : array, lo : Int, hi : Int) => Obj
  val fun = MonoSortedIFunction(
    name,
    List(arrayTheory.sort, arrayIndexSort, arrayIndexSort), arrayTheory.objSort,
    partial = false, relational = false)

  /**
   * The theory introduces the single extended quantifier function.
   */
  override val functions: Seq[IFunction] = Seq(fun)

  val (funPredicates, axioms1, order, functionTranslation) = Theory.genAxioms(
    theoryFunctions = functions,
    //theoryAxioms = theoryAxioms,
    theoryAxioms = i(true),
    otherTheories = dependencies.toList)

  override val predicates: Seq[Predicate] = funPredicates
  override val functionPredicateMapping: Seq[(IFunction, Predicate)] =
    functions zip funPredicates
  override val functionalPredicates: Set[Predicate] = funPredicates.toSet
  override val predicateMatchConfig: PredicateMatchConfig = Map()
  override val triggerRelevantFunctions: Set[IFunction] = Set()
  override val axioms: Formula = Conjunction.TRUE
  override val totalityAxioms: Formula = Conjunction.TRUE
  override def plugin: Option[Plugin] = None

  override def isSoundForSat( // todo
                              theories : Seq[Theory],
                              config : Theory.SatSoundnessConfig.Value) : Boolean =
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
    def unapply(f : IFunction) : Option[ExtendedQuantifier] =
      (TheoryRegistry lookupSymbol f) match {
        case Some(t : ExtendedQuantifier) if f == t.fun => Some(t)
        case _ => None
      }
  }

//  class Instrumenter (exq : ExtendedQuantifier) {
//    def instrumentStore(bodyAtom         : IAtom,
//                        headAtom         : IAtom,
//                        bodyGhostVarInds : GhostVariableInds,
//                        headGhostVarInds : GhostVariableInds,
//                        storeInfo        : StoreInfo) : Seq[IFormula] = {
//      val GhostVariableInds(iblo, ibhi, ibres, ibarr) = bodyGhostVarInds
//      val (blo, bhi, bres, barr) =
//        (bodyAtom.args(iblo), bodyAtom.args(ibhi),
//          bodyAtom.args(ibres), bodyAtom.args(ibarr))
//
//      val StoreInfo(a1, a2, i, o, arrayTheory) = storeInfo
//
//      val indexSort = arrayTheory.indexSorts.head // todo: assuming 1-d array
//
//      val (hlo, hhi, hres, harr) =
//        (IConstant(new SortedConstantTerm("lo'", indexSort)),
//          IConstant(new SortedConstantTerm("hi'", indexSort)),
//          IConstant(new SortedConstantTerm("res'", arrayTheory.objSort)),
//          IConstant(new SortedConstantTerm("arr'", arrayTheory.sort))
//        )
//
//      val instConstraint =
//        ite(blo === bhi,
//          (hlo === i) & (hhi === i + 1) & (hres === o),
//          ite((blo - 1 === i),
//            (hres === exq.redOp(bres, o)) & (hlo === i) & hhi === bhi,
//            ite(bhi === i,
//              (hres === exq.redOp(bres, o)) & (hhi === i + 1 & hlo === blo),
//              ite(blo <= i & bhi > i,
//                exq.invRedOp match {
//                  case Some(f) => hres === exq.redOp(f(bres, arrayTheory.select(a1, i)), o) & hlo === blo & hhi === bhi
//                  case _ => (hlo === i) & (hhi === i + 1) & (hres === o)//??? //TODO: Implement non-cancellative case
//                },
//                //hres === ifInsideBounds_help(o, arrayTheory.select(a1, i), bres) & hlo === blo & hhi === bhi, //relate to prev val
//                (hlo === i) & (hhi === i + 1) & (hres === o))))) // outside bounds, reset
//
//      var newHead = headAtom
//      val GhostVariableInds(ihlo, ihhi, ihres, iharr) = headGhostVarInds
//      val newHeadArgs : Seq[ITerm] =
//        for ((arg : ITerm, ind : Int) <- newHead.args.zipWithIndex) yield {
//          ind match {
//            case headGhostVarInds.lo  => hlo
//            case headGhostVarInds.hi  => hhi
//            case headGhostVarInds.res => hres
////            case headGhostVarInds.arr => harr // todo: add ghost array?
//            case _ => arg
//          }
//        }
//      newHead = IAtom(headAtom.pred, newHeadArgs)
//
//      ???
//    }
//
//
//
//  }

}

//class SimpleExtendedQuantifier(name            : String,
//                               arrayObjectSort : Sort,
//                               //                       zero            : ITerm,
//                               reduceOp        : (ITerm, ITerm) => ITerm,
//                               invReduceOp     : Option[(ITerm, ITerm) => ITerm],
//                               override val clauseInstrumenter : ClauseInstrumenter)
//extends ExtendedQuantifier(name, arrayObjectSort, reduceOp, invReduceOp, clauseInstrumenter) {
//  override protected
//  def instrumentStore(storeInfo: StoreInfo,
//                      bodyTerms: GhostVariableTerms): Seq[IFormula] = {
//          val instConstraint =
//            ite(blo === bhi,
//              (hlo === i) & (hhi === i + 1) & (hres === o),
//              ite((blo - 1 === i),
//                (hres === exq.redOp(bres, o)) & (hlo === i) & hhi === bhi,
//                ite(bhi === i,
//                  (hres === exq.redOp(bres, o)) & (hhi === i + 1 & hlo === blo),
//                  ite(blo <= i & bhi > i,
//                    exq.invRedOp match {
//                      case Some(f) => hres === exq.redOp(f(bres, arrayTheory.select(a1, i)), o) & hlo === blo & hhi === bhi
//                      case _ => (hlo === i) & (hhi === i + 1) & (hres === o)//??? //TODO: Implement non-cancellative case
//                    },
//                    //hres === ifInsideBounds_help(o, arrayTheory.select(a1, i), bres) & hlo === blo & hhi === bhi, //relate to prev val
//                    (hlo === i) & (hhi === i + 1) & (hres === o))))) // outside bounds, reset
//  }
//
//  override protected
//  def instrumentSelect(selectInfo: SelectInfo,
//                       bodyTerms: GhostVariableTerms): Seq[IFormula] = ???
//
//  override protected
//  def instrumentConst(constInfo: ConstInfo,
//                      bodyTerms: GhostVariableTerms): Seq[IFormula] = ???
//}