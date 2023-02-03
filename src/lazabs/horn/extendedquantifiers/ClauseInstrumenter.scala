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

import ap.parser.IExpression.Predicate
import ap.parser._
import ap.types.SortedConstantTerm
import lazabs.horn.bottomup.HornClauses.Clause
import Util._
import ap.parser.IExpression._
import GhostVariableAdder._
import lazabs.prover.PrincessWrapper.expr2Formula

import scala.collection.mutable.ArrayBuffer

abstract class
ClauseInstrumenter(extendedQuantifier : ExtendedQuantifier) {
  case class InstrumentationResult(newConjunct      : IFormula,
                                   rewriteConjuncts : Map[IFormula, IFormula],
                                   assertions       : Seq[IFormula])

  protected def instrumentStore (storeInfo             : StoreInfo,
                                 headTerms             : GhostVariableTerms,
                                 bodyTerms             : GhostVariableTerms,
                                 alienTermMap          : Map[ITerm, ITerm],
                                 termToHeadAlienVarInd : Map[ConstantTerm, Int],
                                 bodyArgs              : Seq[ITerm]) : Seq[InstrumentationResult]
  protected def instrumentSelect(selectInfo            : SelectInfo,
                                 headTerms             : GhostVariableTerms,
                                 bodyTerms             : GhostVariableTerms,
                                 alienTermMap          : Map[ITerm, ITerm],
                                 termToHeadAlienVarInd : Map[ConstantTerm, Int],
                                 bodyArgs              : Seq[ITerm]) : Seq[InstrumentationResult]
  protected def instrumentConst (constInfo             : ConstInfo,
                                 headTerms             : GhostVariableTerms,
                                 bodyTerms             : GhostVariableTerms,
                                 alienTermMap          : Map[ITerm, ITerm],
                                 termToHeadAlienVarInd : Map[ConstantTerm, Int],
                                 bodyArgs              : Seq[ITerm]) : Seq[InstrumentationResult]
  protected def rewriteAggregateFun (exqInfo    : ExtendedQuantifierInfo,
                                     ghostVarTerms : Seq[GhostVariableTerms],
                                     alienVarToPredVar : Map[ITerm, ITerm]) : Seq[InstrumentationResult]

  protected val arrayTheory = extendedQuantifier.arrayTheory

  if (arrayTheory.indexSorts.length > 1)
    throw new UnsupportedOperationException("Only 1-d arrays are supported currently.")

  protected val indexSort = arrayTheory.indexSorts.head

  // returns all instrumentations of a clause
  def instrument (clause                 : Clause,
                  allGhostVarInds        : Map[Predicate, Seq[GhostVariableInds]],
                  extendedQuantifierInfo : ExtendedQuantifierInfo,
                  alienVarToPredVar : Map[ITerm, ITerm]) : Seq[Instrumentation] = {
    val rewrites : Seq[Instrumentation] = {
      val conjuncts : Seq[IFormula] =
        LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)
      val relevantConjuncts =
        conjuncts filter (c => isAggregateFun(c))

      if (relevantConjuncts nonEmpty) {
        if (relevantConjuncts.length > 1)
          throw new Exception("More than one conjunct found for rewriting," +
            " are the clauses normalized?\n" + clause.toPrologString)

        val ghostVarTerms: Seq[GhostVariableTerms] =
          for (GhostVariableInds(iblo, ibhi, ibres, ibarr, bAlienInds) <-
                  allGhostVarInds(clause.body.head.pred)) yield {
            val blo = clause.body.head.args(iblo)
            val bhi = clause.body.head.args(ibhi)
            val bres = clause.body.head.args(ibres)
            val barr = clause.body.head.args(ibarr)
            val alienTerms =
              for (AlienGhostVariableInds(iv, ivSet) <- bAlienInds) yield
                AlienGhostVariableTerms(v = clause.body.head.args(iv),
                                        vSet = clause.body.head.args(ivSet))
            GhostVariableTerms(lo = blo, hi = bhi, res = bres, arr = barr,
                               alienTerms = alienTerms)
          }

        val instrumentationResults: Seq[InstrumentationResult] =
          relevantConjuncts.headOption match {
            case Some(c) if extendedQuantifierInfo ==
              ExtQuantifierFunctionApplicationCollector(c).head =>
              rewriteAggregateFun(extendedQuantifierInfo, ghostVarTerms, alienVarToPredVar)
            case _ => Nil
          }
        for (result <- instrumentationResults) yield
          Instrumentation(result.newConjunct,
            result.assertions, Map(), result.rewriteConjuncts)
      } else Nil
    }

    // returns instrumentations for body atom, EXCEPT the identity instrumentations
    def instrForBodyAtom(bAtom : IAtom) : Seq[Instrumentation] = {
      (for ((GhostVariableInds(iblo, ibhi, ibres, ibarr, bAlienInds), iGhostVars) <-
              allGhostVarInds(bAtom.pred).zipWithIndex
            if allGhostVarInds contains clause.head.pred) yield {
        val alienBodyTerms =
          for (AlienGhostVariableInds(iv, ivSet) <- bAlienInds) yield
            AlienGhostVariableTerms(v = bAtom.args(iv),
                                    vSet = bAtom.args(ivSet))
        val bodyTerms : GhostVariableTerms =
          GhostVariableTerms(bAtom.args(iblo), bAtom.args(ibhi),
                             bAtom.args(ibres), bAtom.args(ibarr),
                             alienBodyTerms)
        val conjuncts : Seq[IFormula]      =
          LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)
        val relevantConjuncts =
          conjuncts filter (c => isSelect(c) || isConst(c) || isStore(c))
        if(relevantConjuncts.length > 1)
          throw new Exception("More than one conjunct found for instrumentation," +
            " are the clauses normalized?\n" + clause.toPrologString)

        val resultSort = extendedQuantifier.predicate match {
          case Some(_) =>
            ap.types.Sort.Bool
          case None    =>
            arrayTheory.objSort
        }

        val alienHeadTerms =
          for (AlienGhostVariableTerms(v, vSet) <- bodyTerms.alienTerms) yield {
            AlienGhostVariableTerms(
              IConstant(new SortedConstantTerm(v.toString + iGhostVars + "'", Sort.sortOf(v))),
              IConstant(new SortedConstantTerm(vSet.toString + iGhostVars + "'", Sort.Bool)))
          }

        val headTerms = GhostVariableTerms(
          IConstant(new SortedConstantTerm("lo_" + iGhostVars + "'", indexSort)),
          IConstant(new SortedConstantTerm("hi_" + iGhostVars + "'", indexSort)),
          IConstant(new SortedConstantTerm("res_" + iGhostVars + "'", resultSort)),
          IConstant(new SortedConstantTerm("arr_" + iGhostVars + "'", arrayTheory.sort)),
          alienHeadTerms
        )

        val ghostVarSetsInPred = allGhostVarInds(clause.head.pred)
        val hInds = ghostVarSetsInPred(iGhostVars)

        val alienTermIndMap : Map[Int, ITerm] = ({
          (for((inds, terms) <- hInds.alienInds zip headTerms.alienTerms) yield {
            Seq(inds.v -> terms.v, inds.vSet -> terms.vSet)
          }).flatten
        }).toMap
        val headTermMap : Map[Int, ITerm] =
          Map(hInds.lo -> headTerms.lo, hInds.hi -> headTerms.hi,
              hInds.res -> headTerms.res, hInds.arr -> headTerms.arr) ++
          alienTermIndMap

        // try to "guess" some constants for the alien terms in predicates
        val alienTermMap : Map[ITerm, ITerm] = {
          val clauseConstants : Seq[ConstantTerm] = clause.constantsSorted
          for (t <- alienBodyTerms) yield {
            clauseConstants.find(c => // todo: refactor
              t.v.asInstanceOf[IConstant].c.name contains (c.name ++ "_shad"))
            match {
              case Some(c) =>
                t.v -> IConstant(c)
              case None => // try the first argument,
                // if the wrong argument is picked this will be caught in the
                // last assertion
                t.v -> IConstant(clauseConstants.headOption.getOrElse(
                  t.v.asInstanceOf[IConstant].c))
            }
          }
        }.toMap

        val termToHeadAlienVarInd : Map[ConstantTerm, Int] = {
          extendedQuantifier.alienConstantsInPredicate zip
            allGhostVarInds(clause.head.pred).flatMap(_.alienInds.map(_.v))
        }.toMap

        val instrumentationResults : Seq[InstrumentationResult] =
          relevantConjuncts.headOption match {
            case Some(c) if isSelect(c) =>
              instrumentSelect(extractSelectInfo(c), headTerms, bodyTerms,
                               alienTermMap, termToHeadAlienVarInd, bAtom.args)
            case Some(c) if isStore(c) =>
              instrumentStore(extractStoreInfo(c), headTerms, bodyTerms,
                              alienTermMap, termToHeadAlienVarInd, bAtom.args)
            case Some(c) if isConst(c) =>
              instrumentConst(extractConstInfo(c), headTerms, bodyTerms,
                              alienTermMap, termToHeadAlienVarInd, bAtom.args)
            case None => Nil
          }
        for(result <- instrumentationResults) yield
          Instrumentation(result.newConjunct,
            result.assertions, headTermMap, Map())
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
                                    inst    : Instrumentation)
    : Instrumentation = {
      if(allGhostVarInds contains clause.head.pred) {
        val bodyGhostVarInds: Seq[GhostVariableInds] =
          allGhostVarInds(bodyAtom.pred)
        val headGhostVarInds   : Seq[GhostVariableInds] =
          allGhostVarInds(clause.head.pred)
        val unusedHeadBodyInds : Seq[(GhostVariableInds, GhostVariableInds)] =
          (headGhostVarInds zip bodyGhostVarInds).filter(inds =>
            !inst.headTerms.contains(inds._1.lo))
        val identityInds =
          for ((hInds, bInds) <- unusedHeadBodyInds) yield {
            val alienHeadTerms =
              for(AlienGhostVariableInds(iv, ivSet) <- bInds.alienInds) yield {
                AlienGhostVariableTerms(v = clause.head.args(iv),
                                        vSet = clause.head.args(ivSet))
              }
            val headTerms = GhostVariableTerms(
              lo = clause.head.args(hInds.lo), hi = clause.head.args(hInds.hi),
              res = clause.head.args(hInds.res), arr = clause.head.args(hInds.arr),
              alienHeadTerms)

            val alienBodyTerms =
              for (AlienGhostVariableInds(iv, ivSet) <- bInds.alienInds)
                yield {
                AlienGhostVariableTerms(v = bodyAtom.args(iv),
                                        vSet = bodyAtom.args(ivSet))
              }
            val bodyTerms = GhostVariableTerms(
              lo = bodyAtom.args(bInds.lo), hi = bodyAtom.args(bInds.hi),
              res = bodyAtom.args(bInds.res), arr = bodyAtom.args(bInds.arr),
              alienBodyTerms)

            val alienConjuncts =
              (for ((ts1, ts2) <-
                      headTerms.alienTerms zip bodyTerms.alienTerms) yield {
                ts1.v === ts2.v &&& ts1.vSet === ts2.vSet
              }).fold(i(true))((c1, c2) => c1 &&& c2)

            val newConjunct =
              (headTerms.arr === bodyTerms.arr) &&&
                (headTerms.lo === bodyTerms.lo) &&&
                (headTerms.hi === bodyTerms.hi) &&&
                (headTerms.res === bodyTerms.res) &&& alienConjuncts

            val alienTermIndMap : Map[Int, ITerm] = ({
              (for ((inds, terms) <- hInds.alienInds zip headTerms
                .alienTerms) yield {
                Seq(inds.v -> terms.v, inds.vSet -> terms.vSet)
              }).flatten
            }).toMap

            val headTermMap: Map[Int, ITerm] = Map(
              hInds.lo -> headTerms.lo, hInds.hi -> headTerms.hi,
              hInds.res -> headTerms.res, hInds.arr -> headTerms.arr) ++ alienTermIndMap
            Instrumentation(newConjunct, Nil, headTermMap, Map())
          }
        identityInds.reduceOption(_ + _).
          getOrElse(Instrumentation.emptyInstrumentation) + inst
      } else inst
    }

    // returns the identity instrumentation (i.e., all ghost vars are passed unchanged)
    def identityInstrumentation (bAtom : IAtom) =
      if(allGhostVarInds contains clause.head.pred)
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

    val numGhostVarSets = allGhostVarInds.head._2.length
    val combsForBodyAtoms: Seq[Seq[Instrumentation]] =
      for ((bAtom, instrs) <- instrsForBodyAtoms) yield {
        val combinations: Seq[Seq[Instrumentation]] =
          (for (i <- 1 to numGhostVarSets) yield {
            instrs.combinations(i)
          }).flatten
        val completeCombinatons: Seq[Instrumentation] =
          for (combination <- combinations) yield {
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
class SimpleClauseInstrumenter(extendedQuantifier : ExtendedQuantifier)
  extends ClauseInstrumenter(extendedQuantifier) {

  private def pred(o : ITerm, i : ITerm, alienSubstMap : Map[ConstantTerm, ITerm]) = {
    extendedQuantifier.predicate match {
      case Some(p) =>
      // rewrite alien terms in the app to their corresponding ghost variables
      ConstantSubstVisitor(p(o, i), alienSubstMap)
      case None => o
    }
  }

  private def getAlienTermsFormulaAndAssertion(headTerms : GhostVariableTerms,
                                               bodyTerms : GhostVariableTerms,
                                               alienTermMap : Map[ITerm, ITerm]) :
  (IFormula, IFormula) = {
    val initConjuncts      = new ArrayBuffer[IFormula]
    val assertionConjuncts = new ArrayBuffer[IFormula]
    if (bodyTerms.alienTerms isEmpty)
      IBoolLit(true)
    else {
      (for ((AlienGhostVariableTerms(bv, bvSet),
      AlienGhostVariableTerms(hv, hvSet)) <-
              bodyTerms.alienTerms zip headTerms.alienTerms) {
        initConjuncts +=
        ((expr2Formula(bvSet) &&& hv === bv) ||| hv === alienTermMap(bv)) &&& expr2Formula(hvSet)
//        ite(expr2Formula(bvSet),
//            hv === bv &&& hvSet === bvSet, // then
//            expr2Formula(hvSet) &&& hv === alienTermMap(bv)) // else
        assertionConjuncts +=
          (expr2Formula(bvSet) ==> (bv === alienTermMap(bv)))// &&& (expr2Formula(hvSet))
      })
    }
    (initConjuncts.fold(i(true))((c1, c2) => c1 &&& c2),
      assertionConjuncts.fold(i(true))((c1, c2) => c1 &&& c2))
  }

  override protected
  def instrumentStore(storeInfo             : StoreInfo,
                      headTerms             : GhostVariableTerms,
                      bodyTerms             : GhostVariableTerms,
                      alienTermMap          : Map[ITerm, ITerm],
                      termToHeadAlienVarInd : Map[ConstantTerm, Int],
                      bodyArgs              : Seq[ITerm]): Seq[InstrumentationResult] = {
    val StoreInfo(a1, a2, i, o, arrayTheory2) = storeInfo
    if (arrayTheory != arrayTheory2)
      Nil
    else {
      import extendedQuantifier._
      import bodyTerms._
      import arrayTheory2._
      val (alienTermInitFormula, alienTermAssertionFormula) =
        getAlienTermsFormulaAndAssertion(headTerms, bodyTerms, alienTermMap)

      val alienSubstMap : Map[ConstantTerm, ITerm] =  // todo: incorrect - fix
        (for ((alienC, alienI) <- extendedQuantifier.alienConstantsInPredicate.zipWithIndex) yield {
          alienC -> headTerms.alienTerms(alienI).v//headArgs(termToHeadAlienVarInd(alienC))
        }).toMap
      val instrConstraint1                           =
        (headTerms.arr === a2) &&& alienTermInitFormula &&&
        ite(bodyTerms.lo === bodyTerms.hi,
          (headTerms.lo === i) & (headTerms.hi === i + 1) & (headTerms.res === pred(o, i, alienSubstMap)),
          ite((lo - 1 === i),
            (headTerms.res === reduceOp(res, pred(o, i, alienSubstMap))) & (headTerms.lo === i) & headTerms.hi === hi,
            ite(hi === i,
              (headTerms.res === reduceOp(res, pred(o, i, alienSubstMap))) & (headTerms.hi === i + 1 & headTerms.lo === lo),
              ite(lo <= i & hi > i,
                invReduceOp match {
                  case Some(f) =>
                    headTerms.res === reduceOp(f(res, select(a1, i)), pred(o, i, alienSubstMap)) &
                    headTerms.lo === lo & headTerms.hi === hi
                  case _ =>
                    (headTerms.lo === i) & (headTerms.hi === i + 1) &
                    (headTerms.res === pred(o, i, alienSubstMap))
                },
                (headTerms.lo === i) & (headTerms.hi === i + 1) &
                (headTerms.res === pred(o, i, alienSubstMap)))))) // outside bounds, reset
      val assertion = lo === hi ||| (a1 === arr &&& alienTermAssertionFormula)
      Seq(InstrumentationResult(newConjunct = instrConstraint1,
                                              rewriteConjuncts = Map(),
                                              assertions = Seq(assertion)))
    }
  }

  override protected
  def instrumentSelect(selectInfo            : SelectInfo,
                       headTerms             : GhostVariableTerms,
                       bodyTerms             : GhostVariableTerms,
                       alienTermMap          : Map[ITerm, ITerm],
                       termToHeadAlienVarInd : Map[ConstantTerm, Int],
                       bodyArgs              : Seq[ITerm]): Seq[InstrumentationResult] = {
    val SelectInfo(a, i, o, arrayTheory2) = selectInfo
    if (arrayTheory != arrayTheory2)
      Nil
    else {
      import extendedQuantifier._
      import bodyTerms._
      val alienSubstMap : Map[ConstantTerm, ITerm] = // todo: incorrect - fix
        (for ((alienC, alienI) <- extendedQuantifier
          .alienConstantsInPredicate.zipWithIndex) yield {
          alienC -> headTerms.alienTerms(alienI).v//headArgs
          // (termToHeadAlienVarInd(alienC))
        }).toMap
      val (alienTermInitFormula, alienTermAssertionFormula) =
        getAlienTermsFormulaAndAssertion(headTerms, bodyTerms,
                                         alienTermMap : Map[ITerm, ITerm])
      val instrConstraint1 =
        (headTerms.arr === a) &&& alienTermInitFormula &&&
        ite(lo === hi,
          (headTerms.lo === i) & (headTerms.hi === i + 1) &
          (headTerms.res === pred(o, i, alienSubstMap)),
          ite((lo - 1 === i),
            (headTerms.res === reduceOp(res, pred(o, i, alienSubstMap))) & (headTerms.lo === i) & headTerms.hi === hi,
            ite(hi === i,
              (headTerms.res === reduceOp(res, pred(o, i, alienSubstMap))) & (headTerms.hi === i + 1 & headTerms.lo === lo),
              ite(lo <= i & hi > i,
                headTerms.res === res & headTerms.lo === lo & headTerms.hi === hi, // no change within bounds
                (headTerms.lo === i) & (headTerms.hi === i + 1) &
                (headTerms.res === pred(o, i, alienSubstMap)))))) // outside bounds, reset
      val assertion = lo === hi ||| (a === arr &&& alienTermAssertionFormula)
      Seq(InstrumentationResult(newConjunct = instrConstraint1,
                                rewriteConjuncts = Map(),
                                assertions = Seq(assertion)))
    }
  }

  // todo: instrument const operation
  override protected
  def instrumentConst(constInfo : ConstInfo,
                      headTerms : GhostVariableTerms,
                      bodyTerms : GhostVariableTerms,
                      alienTermMap : Map[ITerm, ITerm],
                      termToHeadAlienVarInd : Map[ConstantTerm, Int],
                      bodyArgs : Seq[ITerm]) : Seq[InstrumentationResult] =
    Nil
  //  val ConstInfo(a, o, arrayTheory) = constInfo
  //  val instr =
  //    hhi === 10 &&& hlo === 0 &&& harr === a &&&
  //      hres === extendedQuantifier.reduceOp(o, o)

  override protected
  def rewriteAggregateFun(exqInfo       : ExtendedQuantifierInfo,
                          ghostVarTerms : Seq[GhostVariableTerms],
                          alienVarToPredVar : Map[ITerm, ITerm]) : Seq[InstrumentationResult] = {
    // range1 ? res1 : (range 2 ? res2 : (... : range1+range2 ? res1+res : range2+range1 ? res2+res1 : ... ))
    val combinations: Seq[Seq[GhostVariableTerms]] =
      (for (i <- 1 to ghostVarTerms.length) yield {
        ghostVarTerms.combinations(i)
      }).flatten

    val ExtendedQuantifierInfo(_, funApp, a, lo, hi, o, conjunct) = exqInfo
    def loExpr = extendedQuantifier.rangeFormulaLo.getOrElse(
      (t1 : ITerm, t2 : ITerm) => t1 === t2)
    def hiExpr = extendedQuantifier.rangeFormulaHi.getOrElse(
      (t1 : ITerm, t2 : ITerm) => t1 === t2)

    def buildRangeFormula(combs : Seq[Seq[GhostVariableTerms]]) : IFormula = {
      combs.headOption match {
        case Some(comb) =>
          comb length match {
            case 1 =>
              ((loExpr(comb.head.lo, lo) & hiExpr(comb.head.hi, hi) & comb.head.arr === a) ==>
                (comb.head.res === o)) &&&
              ((lo >= hi) ==> (extendedQuantifier.identity === o)) &&&
                buildRangeFormula(combs.tail)
            case 2 => //todo: empty range for more than one ghost var range?
              ((loExpr(comb(0).lo, lo) & hiExpr(comb(0).hi, comb(1).lo) &
                hiExpr(comb(1).hi, hi) & comb(0).arr === a & comb(1).arr === a) ==>
                (extendedQuantifier.reduceOp(comb(0).res, comb(1).res) === o) &&&
                ((loExpr(comb(1).lo, lo) & hiExpr(comb(1).hi, comb(0).lo) &
                  hiExpr(comb(0).hi, hi) & comb(0).arr === a & comb(1).arr === a) ==>
                  (extendedQuantifier.reduceOp(comb(1).res, comb(0).res) === o))) &&&
                buildRangeFormula(combs.tail)
            case _ => ??? // todo: generalize this!
          }
        case None => i(true)
      }
    }

    // this builds a formula to be asserted, such that at least one of the
    // branches must be taken
    def buildAssertionFormula(combs : Seq[Seq[GhostVariableTerms]]) : IFormula = {
      // todo: refactor
      combs.headOption match {
        case Some(comb) =>
          comb length match {
            case 1 =>
              // assert that the alien ghost vars are the same as those used
              // in the aggregate
              val alienGuard = {
                for (AlienGhostVariableTerms(v, vSet) <- comb.head.alienTerms)
                  yield {
                    (expr2Formula(vSet)) &&&
                    (v === alienVarToPredVar(v))
                  }
              }.fold(i(true))((c1, c2) => c1 &&& c2)

              val guard =
                (loExpr(comb.head.lo, lo) & hiExpr(comb.head.hi, hi) & comb.head.arr === a &&& alienGuard) ||| (lo >= hi)
              guard ||| buildAssertionFormula(combs.tail)
            case 2 => //todo: empty range for more than one ghost var range?
              val alienGuard1 = {
                for (AlienGhostVariableTerms(v, vSet) <- comb(0).alienTerms)
                  yield {
                    expr2Formula(vSet) &&& v === alienVarToPredVar(v)
                  }
              }.fold(i(true))((c1, c2) => c1 &&& c2)
              val alienGuard2 = {
                for (AlienGhostVariableTerms(v, vSet) <- comb(1).alienTerms)
                  yield {
                    expr2Formula(vSet) &&& v === alienVarToPredVar(v)
                  }
              }.fold(i(true))((c1, c2) => c1 &&& c2)
              val c1 =
                loExpr(comb(0).lo, lo) & hiExpr(comb(0).hi, comb(1).lo) &
                  hiExpr(comb(1).hi, hi) & comb(0).arr === a & comb(1).arr === a &&& alienGuard1
              val c2 =
                loExpr(comb(1).lo, lo) & hiExpr(comb(1).hi, comb(0).lo) &
                 hiExpr(comb(0).hi, hi) & comb(0).arr === a & comb(1).arr === a &&& alienGuard2
              (c1 ||| c2) ||| buildAssertionFormula(combs.tail)
            case _ => ??? // todo: generalize this!
          }
        case None => IExpression.i(false)
      }
    }

    val rewriteConjuncts =
      Map(exqInfo.conjunct -> buildRangeFormula(combinations))
    val assertionFormula = buildAssertionFormula(combinations)

    Seq(InstrumentationResult(newConjunct      = IExpression.i(true),
                              rewriteConjuncts = rewriteConjuncts,
                              assertions       = Seq(assertionFormula)))
  }


}