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

package lazabs.horn.extendedquantifiers

import ap.parser.IExpression.Predicate
import ap.parser._
import ap.types.SortedConstantTerm
import lazabs.horn.bottomup.HornClauses.Clause
import Util._
import ap.parser.IExpression._
import GhostVariableAdder._
import lazabs.horn.extendedquantifiers.InstrumentationOperator.GhostVar

class ClauseInstrumenter(instrumentationOperator : InstrumentationOperator) {
  case class InstrumentationResult(newConjunct      : IFormula,
                                   rewriteConjuncts : Map[IFormula, IFormula],
                                   assertions       : Seq[IFormula])
  private val instOp = instrumentationOperator

  /**
   * @todo This class should be abstrtacted from theories used. It should only
   *       call the rewrite rules.
   */
  protected val arrayTheory = instOp.exq.arrayTheory
  if (arrayTheory.indexSorts.length > 1)
    throw new UnsupportedOperationException("Only 1-d arrays are supported currently.")

//  protected val indexSort = arrayTheory.indexSorts.head

  // returns all instrumentations of a clause
  def instrument (clause                 : Clause,
                  predToGhostVarInds     : Map[Predicate, GhostVariableInds],
                  extendedQuantifierInfo : ExtendedQuantifierApp) : Seq[Instrumentation] = {

    /** Rewritings of all aggregate function applications. */
    val rewrites : Seq[Instrumentation] = {
      val conjuncts : Seq[IFormula] =
        LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)
      val relevantConjuncts =
        conjuncts filter (c => isAggregateFun(c))

      if (relevantConjuncts nonEmpty) {
        if (relevantConjuncts.length > 1)
          throw new Exception("More than one conjunct found for rewriting," +
            " are the clauses normalized?\n" + clause.toPrologString)

        val ghostVarTerms: GhostVariableTerms =
          for (oldGhostInds <- predToGhostVarInds(clause.body.head.pred)) yield
            for((ghostVar, ind) <- oldGhostInds) yield
              ghostVar -> clause.body.head.args(ind)

        val rewriteResults: Seq[RewriteRules.Result] =
          relevantConjuncts.headOption match {
            case Some(c) if extendedQuantifierInfo ==
              ExtQuantifierFunctionApplicationCollector(c).head =>
              instOp.rewriteAggregate(ghostVarTerms, extendedQuantifierInfo)
            case _ => Nil
          }
        for (result <- rewriteResults) yield
          Instrumentation(result.newConjunct,
            result.assertions, Map(), result.rewriteFormulas)
      } else Nil
    }

    // returns instrumentations for body atom, EXCEPT the identity instrumentations
    /**
     * Each predicate of a body atom might have (sets of) ghost variables for
     * each [[ExtendedQuantifierApp]].
     * We need to collect rewrites for each set of ghost variables for each
     * body atom, and conjoin them.
     */
    def instrForBodyAtom(bAtom : IAtom) : Seq[Instrumentation] = {
      (for ((ghostVarToInd, iGhostVars)
              <- predToGhostVarInds(bAtom.pred).zipWithIndex
            if predToGhostVarInds contains clause.head.pred) yield {

        val bodyGhostTerms =
          for ((ghostVar, bodyInd) <- ghostVarToInd) yield
            ghostVar -> bAtom.args(bodyInd)

        val conjuncts : Seq[IFormula] =
          LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)

        /**
         * @todo These functions should not be hardcoded and extracted from the
         *       instrumentation operator instead!
         */
        val relevantConjuncts =
          conjuncts filter (c => isSelect(c) || isConst(c) || isStore(c))
        if(relevantConjuncts.length > 1)
          throw new Exception("More than one conjunct found for instrumentation," +
            " are the clauses normalized?\n" + clause.toPrologString)

        val headGhostTerms =
          (for (ghostVar <- instOp.ghostVars) yield
            ghostVar -> IConstant(new SortedConstantTerm(
              s"${ghostVar.name}_$iGhostVars\'", ghostVar.sort))).toMap

        val ghostVarSetsInPred = predToGhostVarInds(clause.head.pred)
        val hInds = ghostVarSetsInPred(iGhostVars)

        val headTermMap : Map[Int, ITerm] = for ((ghostVar, ind) <- hInds)
          yield ind -> headGhostTerms(ghostVar)

        val allGhostTerms = (bodyGhostTerms.values ++ headGhostTerms.values).toSet
        val nonGhostConstants = clause.constantsSorted.map(IConstant).filterNot(
          allGhostTerms contains).toSet
        val instrumentationResults : Seq[RewriteRules.Result] =
          relevantConjuncts.headOption match {
            case Some(c) if isSelect(c) => instOp.rewriteSelect(
              bodyGhostTerms, headGhostTerms, nonGhostConstants,
              extractSelectInfo(c))
            case Some(c) if isStore(c)  => instOp.rewriteStore(
              bodyGhostTerms, headGhostTerms, nonGhostConstants,
              extractStoreInfo(c))
            case Some(c) if isConst(c) => instOp.rewriteConst(
              bodyGhostTerms, headGhostTerms, nonGhostConstants,
              extractConstInfo(c))
            case None => Nil
          }
        for(result <- instrumentationResults) yield Instrumentation(
          result.newConjunct, result.assertions, headTermMap, Map())
      }).flatten
    }

    // todo: correctly compose identity and regular instrumentations for multiple sets of ghost variables!

    // given a sequence of instrumentations produced from a body atom,
    // produces a sequence of instrumentations with the same size that passes
    //   unused ghost variables to the matching ghost variables in the head
    //   without changing their values.
    //  e.g. h(g1,g2,g3) :- b(g1,g2,g3). Assume g1 & g2 were instrumented,
    //  we create a new instrumentation where g1 & g2 are instrumented and g3 is
    //  passed unchanged (the original instrumentation says nothing about g3).
    def getCompleteInstrumentation (bodyAtom : IAtom,
                                    inst     : Instrumentation)
    : Instrumentation = {
      if(predToGhostVarInds contains clause.head.pred) {
        val bodyGhostVarInds : GhostVariableInds =
          predToGhostVarInds(bodyAtom.pred)
        val headGhostVarInds : GhostVariableInds =
          predToGhostVarInds(clause.head.pred)
        val unusedHeadBodyInds : Seq[(Map[GhostVar, Int], Map[GhostVar, Int])] =
          (headGhostVarInds zip bodyGhostVarInds).filter(inds =>
            !inst.headTerms.exists(t => inds._1.values.toSeq.contains(t._1)))
        val identityInds =
          for ((hInds, bInds) <- unusedHeadBodyInds) yield {
            val ghostHeadTerms = (for (ghostVar <- instOp.ghostVars) yield
              ghostVar -> clause.head.args(hInds(ghostVar))).toMap

            val ghostBodyTerms = (for (ghostVar <- instOp.ghostVars) yield
              ghostVar -> bodyAtom.args(bInds(ghostVar))).toMap

            val newConjunct = and(for(ghostVar <- instOp.ghostVars) yield
              ghostHeadTerms(ghostVar) === ghostBodyTerms(ghostVar))

            val headTermMap : Map[Int, ITerm] =
              (for (ghostVar <- instOp.ghostVars) yield
                hInds(ghostVar) -> ghostHeadTerms(ghostVar)).toMap

            Instrumentation(newConjunct, Nil, headTermMap, Map())
          }
        identityInds.reduceOption(_ + _).
          getOrElse(Instrumentation.emptyInstrumentation) + inst
      } else inst
    }

    // returns the identity instrumentation (i.e., all ghost vars are passed unchanged)
    def identityInstrumentation (bAtom : IAtom) =
      if(predToGhostVarInds contains clause.head.pred)
        getCompleteInstrumentation(bAtom, Instrumentation.emptyInstrumentation)
      else Instrumentation.emptyInstrumentation

    val instrsForBodyAtoms : Seq[(IAtom, Seq[Instrumentation])] =
      clause.body map (atom => (atom, instrForBodyAtom(atom)))
    val identityInstrsForBodyAtoms : Seq[Instrumentation] =
      clause.body map identityInstrumentation

    // this will propagate ghost variables if there is a head
    val instrsFromRewrites =
      if(rewrites nonEmpty) {
        rewrites.map(inst => getCompleteInstrumentation(clause.body.head, inst))
      } else rewrites

    // if we have a rewrite in this clause, there should not be any other
    // instrumentations due to normalization.
    assert(rewrites.isEmpty || instrsForBodyAtoms.forall(_._2.isEmpty))

    val numGhostVarSets = predToGhostVarInds.head._2.length
    val combsForBodyAtoms: Seq[Seq[Instrumentation]] =
      for ((bAtom, instrs) <- instrsForBodyAtoms) yield {
        val combinations: Seq[Seq[Instrumentation]] =
          (for (i <- 1 to numGhostVarSets) yield {
            instrs.combinations(i)
          }).flatten

        val differentCombinations = combinations.filter{combs =>
          val headTermsSeq = combs.map(_.headTerms)
          val firstElementsSeq = headTermsSeq.map(_.toSeq.headOption)
          // no duplicates, i.e., no instrumentations are updating the same
          // head terms, they can be combined
          (firstElementsSeq.distinct.size == firstElementsSeq.size)
        }
        val completeCombinatons: Seq[Instrumentation] =
          for (combination <- differentCombinations) yield {
            getCompleteInstrumentation(bAtom,
              combination.reduceOption(_ + _).getOrElse(
                Instrumentation.emptyInstrumentation))
          }
        completeCombinatons
      }

    if(rewrites isEmpty)
      combsForBodyAtoms.reduceOption((instrs1, instrs2) =>
        Instrumentation.product(instrs1, instrs2)).getOrElse(Nil) ++
        identityInstrsForBodyAtoms
    else
      instrsFromRewrites
  }
}

// A simple instrumenter that works for all extended quantifiers, but is very
// general and thus imprecise.
//class SimpleClauseInstrumenter(extendedQuantifier : ExtendedQuantifier)
//  extends ClauseInstrumenter(extendedQuantifier) {
//
//  private def pred(o : ITerm, i : ITerm, alienSubstMap : Map[ConstantTerm, ITerm]) = {
//    extendedQuantifier.predicate match {
//      case Some(p) =>
//      // rewrite alien terms in the app to their corresponding ghost variables
//      ConstantSubstVisitor(p(o, i), alienSubstMap)
//      case None => o
//    }
//  }
//
//  private def getAlienTermsFormulaAndAssertion(headTerms : GhostVariableTerms,
//                                               bodyTerms : GhostVariableTerms,
//                                               alienTermMap : Map[ITerm, ITerm]) :
//  (IFormula, IFormula) = {
//    val initConjuncts      = new ArrayBuffer[IFormula]
//    val assertionConjuncts = new ArrayBuffer[IFormula]
//    if (bodyTerms.alienTerms isEmpty)
//      IBoolLit(true)
//    else {
//      (for ((AlienGhostVariableTerms(bv, bvSet),
//      AlienGhostVariableTerms(hv, hvSet)) <-
//              bodyTerms.alienTerms zip headTerms.alienTerms) {
//        initConjuncts +=
//        ((expr2Formula(bvSet) &&& hv === bv) ||| hv === alienTermMap(bv)) &&& expr2Formula(hvSet)
////        ite(expr2Formula(bvSet),
////            hv === bv &&& hvSet === bvSet, // then
////            expr2Formula(hvSet) &&& hv === alienTermMap(bv)) // else
//        assertionConjuncts +=
//          (expr2Formula(bvSet) ==> (bv === alienTermMap(bv)))// &&& (expr2Formula(hvSet))
//      })
//    }
//    (initConjuncts.fold(i(true))((c1, c2) => c1 &&& c2),
//      assertionConjuncts.fold(i(true))((c1, c2) => c1 &&& c2))
//  }
//
//  override protected
//  def instrumentStore(storeInfo             : StoreInfo,
//                      headTerms             : GhostVariableTerms,
//                      bodyTerms             : GhostVariableTerms,
//                      alienTermMap          : Map[ITerm, ITerm]): Seq[InstrumentationResult] = {
//    val StoreInfo(a1, a2, i, o, arrayTheory2) = storeInfo
//    if (arrayTheory != arrayTheory2)
//      Nil
//    else {
//      import extendedQuantifier._
//      import bodyTerms._
//      import arrayTheory2._
//      val (alienTermInitFormula, alienTermAssertionFormula) =
//        getAlienTermsFormulaAndAssertion(headTerms, bodyTerms, alienTermMap)
//
//      val standardInstrumentation = {
//        val alienSubstMap : Map[ConstantTerm, ITerm] =  // todo: incorrect - fix
//          (for ((alienC, alienI) <- extendedQuantifier.alienConstantsInPredicate.zipWithIndex) yield {
//            alienC -> headTerms.alienTerms(alienI).v
//          }).toMap
//        val instrConstraint1 =
//          (headTerms.arr === a2) &&& alienTermInitFormula &&&
//          ite(bodyTerms.lo === bodyTerms.hi,
//            (headTerms.lo === i) & (headTerms.hi === i + 1) & (headTerms.res === pred(o, i, alienSubstMap)),
//            ite((lo - 1 === i),
//              (headTerms.res === reduceOp(res, pred(o, i, alienSubstMap))) & (headTerms.lo === i) & headTerms.hi === hi,
//              ite(hi === i,
//                (headTerms.res === reduceOp(res, pred(o, i, alienSubstMap))) & (headTerms.hi === i + 1 & headTerms.lo === lo),
//                ite(lo <= i & hi > i,
//                  invReduceOp match {
//                    case Some(f) =>
//                      headTerms.res === reduceOp(f(res, select(a1, i)), pred(o, i, alienSubstMap)) &
//                      headTerms.lo === lo & headTerms.hi === hi
//                    case _ =>
//                      (headTerms.lo === i) & (headTerms.hi === i + 1) &
//                      (headTerms.res === pred(o, i, alienSubstMap))
//                  },
//                  (headTerms.lo === i) & (headTerms.hi === i + 1) &
//                  (headTerms.res === pred(o, i, alienSubstMap)))))) // outside bounds, reset
//        val assertion = lo === hi ||| (a1 === arr &&& alienTermAssertionFormula)
//
//          InstrumentationResult(newConjunct = instrConstraint1,
//                                rewriteConjuncts = Map(),
//                                assertions = Seq(assertion))
//      }
//      //////////////////////////////////////////////////////////////////////////
//      // also add an array pass-through instrumentation for stores
//      val arrayPassThroughInstrumentation : InstrumentationResult = {
//        val instrConstraint = {
////          ((i < bodyTerms.lo ||| bodyTerms.hi <= i) &&& bodyTerms.arr === a1) ==>
////            (headTerms.arr === a2)
//          headTerms.lo === bodyTerms.lo &&& headTerms.hi === bodyTerms.hi &&&
//          headTerms.res === bodyTerms.res &&&
//          ite(((i < bodyTerms.lo) ||| (bodyTerms.hi <= i)) &&& (bodyTerms.arr === a1),
//              headTerms.arr === a2,
//              headTerms.arr === bodyTerms.arr)
//        }
//        InstrumentationResult(newConjunct = instrConstraint,
//                              rewriteConjuncts = Map(),
//                              assertions = Nil)
//      }
//
//      Seq(standardInstrumentation, arrayPassThroughInstrumentation)
//    }
//  }
//
//  override protected
//  def instrumentSelect(selectInfo            : SelectInfo,
//                       headTerms             : GhostVariableTerms,
//                       bodyTerms             : GhostVariableTerms,
//                       alienTermMap          : Map[ITerm, ITerm]): Seq[InstrumentationResult] = {
//    val SelectInfo(a, i, o, arrayTheory2) = selectInfo
//    if (arrayTheory != arrayTheory2)
//      Nil
//    else {
//      import extendedQuantifier._
//      import bodyTerms._
//      val alienSubstMap : Map[ConstantTerm, ITerm] = // todo: incorrect - fix
//        (for ((alienC, alienI) <- extendedQuantifier
//          .alienConstantsInPredicate.zipWithIndex) yield {
//          alienC -> headTerms.alienTerms(alienI).v
//        }).toMap
//      val (alienTermInitFormula, alienTermAssertionFormula) =
//        getAlienTermsFormulaAndAssertion(headTerms, bodyTerms,
//                                         alienTermMap : Map[ITerm, ITerm])
//      val instrConstraint1 =
//        (headTerms.arr === a) &&& alienTermInitFormula &&&
//        ite(lo === hi,
//          (headTerms.lo === i) & (headTerms.hi === i + 1) &
//          (headTerms.res === pred(o, i, alienSubstMap)),
//          ite((lo - 1 === i),
//            (headTerms.res === reduceOp(res, pred(o, i, alienSubstMap))) & (headTerms.lo === i) & headTerms.hi === hi,
//            ite(hi === i,
//              (headTerms.res === reduceOp(res, pred(o, i, alienSubstMap))) & (headTerms.hi === i + 1 & headTerms.lo === lo),
//              ite(lo <= i & hi > i,
//                headTerms.res === res & headTerms.lo === lo & headTerms.hi === hi, // no change within bounds
//                (headTerms.lo === i) & (headTerms.hi === i + 1) &
//                (headTerms.res === pred(o, i, alienSubstMap)))))) // outside bounds, reset
//      val assertion = lo === hi ||| (a === arr &&& alienTermAssertionFormula)
//      Seq(InstrumentationResult(newConjunct = instrConstraint1,
//                                rewriteConjuncts = Map(),
//                                assertions = Seq(assertion)))
//    }
//  }
//
//  // todo: instrument const operation
//  override protected
//  def instrumentConst(constInfo : ConstInfo,
//                      headTerms : GhostVariableTerms,
//                      bodyTerms : GhostVariableTerms,
//                      alienTermMap : Map[ITerm, ITerm]) : Seq[InstrumentationResult] =
//    Nil
//  //  val ConstInfo(a, o, arrayTheory) = constInfo
//  //  val instr =
//  //    hhi === 10 &&& hlo === 0 &&& harr === a &&&
//  //      hres === extendedQuantifier.reduceOp(o, o)
//
//  override protected
//  def rewriteAggregateFun(exqInfo       : ExtendedQuantifierApp,
//                          ghostVarTerms : Seq[GhostVariableTerms],
//                          alienVarToPredVar : Map[ITerm, ITerm]) : Seq[InstrumentationResult] = {
//    // range1 ? res1 : (range 2 ? res2 : (... : range1+range2 ? res1+res : range2+range1 ? res2+res1 : ... ))
//    val combinations: Seq[Seq[GhostVariableTerms]] =
//      (for (i <- 1 to ghostVarTerms.length) yield {
//        ghostVarTerms.combinations(i)
//      }).flatten
//
//    val ExtendedQuantifierApp(_, funApp, a, lo, hi, o, conjunct) = exqInfo
//    def loExpr = extendedQuantifier.rangeFormulaLo.getOrElse(
//      (t1 : ITerm, t2 : ITerm, t3 : ITerm) => t1 === t2)
//    def hiExpr = extendedQuantifier.rangeFormulaHi.getOrElse(
//      (t1 : ITerm, t2 : ITerm, t3 : ITerm) => t1 === t2)
//
//    def buildRangeFormula(combs : Seq[Seq[GhostVariableTerms]]) : IFormula = {
//      combs.headOption match {
//        case Some(comb) =>
//          comb length match {
//            case 1 =>
//              ((loExpr(comb.head.lo, lo, comb.head.res) &
//                hiExpr(comb.head.hi, hi, comb.head.res) &
//                comb.head.arr === a) ==> (comb.head.res === o)) &&&
//              ((lo >= hi) ==> (extendedQuantifier.identity === o)) &&&
//                buildRangeFormula(combs.tail)
//            case 2 => //todo: empty range for more than one ghost var range?
//              ((loExpr(comb(0).lo, lo, comb(0).res) & hiExpr(comb(0).hi, comb(1).lo, comb(0).res) &
//                hiExpr(comb(1).hi, hi, comb(1).res) & comb(0).arr === a & comb(1).arr === a) ==>
//                (extendedQuantifier.reduceOp(comb(0).res, comb(1).res) === o) &&&
//                ((loExpr(comb(1).lo, lo, comb(1).res) & hiExpr(comb(1).hi, comb(0).lo, comb(1).res) &
//                  hiExpr(comb(0).hi, hi, comb(0).res) & comb(0).arr === a & comb(1).arr === a) ==>
//                  (extendedQuantifier.reduceOp(comb(1).res, comb(0).res) === o))) &&&
//                buildRangeFormula(combs.tail)
//            case _ => ??? // todo: generalize this!
//          }
//        case None => i(true)
//      }
//    }
//
//    // this builds a formula to be asserted, such that at least one of the
//    // branches must be taken
//    def buildAssertionFormula(combs : Seq[Seq[GhostVariableTerms]]) : IFormula = {
//      // todo: refactor
//      combs.headOption match {
//        case Some(comb) =>
//          comb length match {
//            case 1 =>
//              // assert that the alien ghost vars are the same as those used
//              // in the aggregate
//              val alienGuard = {
//                for (AlienGhostVariableTerms(v, vSet) <- comb.head.alienTerms)
//                  yield {
//                    (expr2Formula(vSet)) &&&
//                    (v === alienVarToPredVar(v))
//                  }
//              }.fold(i(true))((c1, c2) => c1 &&& c2)
//
//              val guard =
//                (loExpr(comb.head.lo, lo, comb.head.res) &
//                 hiExpr(comb.head.hi, hi, comb.head.res) &
//                 comb.head.arr === a &&& alienGuard) ||| (lo >= hi)
//              guard ||| buildAssertionFormula(combs.tail)
//            case 2 => //todo: empty range for more than one ghost var range?
//              val alienGuard1 = {
//                for (AlienGhostVariableTerms(v, vSet) <- comb(0).alienTerms)
//                  yield {
//                    expr2Formula(vSet) &&& v === alienVarToPredVar(v)
//                  }
//              }.fold(i(true))((c1, c2) => c1 &&& c2)
//              val alienGuard2 = {
//                for (AlienGhostVariableTerms(v, vSet) <- comb(1).alienTerms)
//                  yield {
//                    expr2Formula(vSet) &&& v === alienVarToPredVar(v)
//                  }
//              }.fold(i(true))((c1, c2) => c1 &&& c2)
//              val c1 =
//                loExpr(comb(0).lo, lo, comb(0).res) &
//                hiExpr(comb(0).hi, comb(1).lo, comb(0).res) &
//                hiExpr(comb(1).hi, hi, comb(1).res) & comb(0).arr === a &
//                comb(1).arr === a &&& alienGuard1
//              val c2 =
//                loExpr(comb(1).lo, lo, comb(1).res) &
//                hiExpr(comb(1).hi, comb(0).lo, comb(1).res) &
//                hiExpr(comb(0).hi, hi, comb(0).res) &
//                comb(0).arr === a & comb(1).arr === a &&& alienGuard2
//              (c1 ||| c2) ||| buildAssertionFormula(combs.tail)
//            case _ => ??? // todo: generalize this!
//          }
//        case None => IExpression.i(false)
//      }
//    }
//
//    val rewriteConjuncts =
//      Map(exqInfo.conjunct -> buildRangeFormula(combinations))
//    val assertionFormula = buildAssertionFormula(combinations)
//
//    Seq(InstrumentationResult(newConjunct      = IExpression.i(true),
//                              rewriteConjuncts = rewriteConjuncts,
//                              assertions       = Seq(assertionFormula)))
//  }
//
//
//}
