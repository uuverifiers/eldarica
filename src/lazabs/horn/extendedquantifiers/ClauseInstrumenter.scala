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

abstract class
ClauseInstrumenter(extendedQuantifier : ExtendedQuantifier) {
  case class InstrumentationResult(conjunct : IFormula,
                                   assertion : IFormula)

  protected def instrumentStore (storeInfo  : StoreInfo,
                                 headTerms  : GhostVariableTerms,
                                 bodyTerms  : GhostVariableTerms) : Seq[InstrumentationResult]
  protected def instrumentSelect(selectInfo : SelectInfo,
                                 headTerms  : GhostVariableTerms,
                                 bodyTerms  : GhostVariableTerms) : Seq[InstrumentationResult]
  protected def instrumentConst (constInfo  : ConstInfo,
                                 headTerms  : GhostVariableTerms,
                                 bodyTerms  : GhostVariableTerms) : Seq[InstrumentationResult]

  protected val arrayTheory = extendedQuantifier.arrayTheory
  protected val indexSort = arrayTheory.indexSorts.head  // todo: assuming 1-d array

  // returns all instrumentations of a clause
  def instrument (clause                 : Clause,
                  allGhostVarInds           : Map[Predicate, Seq[GhostVariableInds]],
                  extendedQuantifierInfo : ExtendedQuantifierInfo) : Seq[Instrumentation] = {
    // returns instrumentations for body atom, EXCEPT the identity instrumentations
    def instrForBodyAtom(bAtom : IAtom) : Seq[Instrumentation] = {
      (for ((GhostVariableInds(iblo, ibhi, ibres, ibarr), iGhostVars) <-
              allGhostVarInds(bAtom.pred).zipWithIndex
            if allGhostVarInds contains clause.head.pred) yield {
        val bodyTerms = GhostVariableTerms(
          bAtom.args(iblo), bAtom.args(ibhi), bAtom.args(ibres), bAtom.args(ibarr))
        val conjuncts : Seq[IFormula] =
          LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)
        val relevantConjuncts =
          conjuncts filter (c => isSelect(c) || isConst(c) || isStore(c))
        if(relevantConjuncts.length > 1)
          throw new Exception("More than one conjunct found for instrumentation," +
            " are the clauses normalized?\n" + clause.toPrologString)

        val headTerms = GhostVariableTerms(
          IConstant(new SortedConstantTerm("lo_" + iGhostVars + "'", indexSort)),
          IConstant(new SortedConstantTerm("hi_" + iGhostVars + "'", indexSort)),
          IConstant(new SortedConstantTerm("res_" + iGhostVars + "'", arrayTheory.objSort)),
          IConstant(new SortedConstantTerm("arr_" + iGhostVars + "'", arrayTheory.sort))
        )

        val ghostVarSetsInPred = allGhostVarInds(clause.head.pred)
        val hInds = ghostVarSetsInPred(iGhostVars)

        val headTermMap : Map[Int, ITerm] = Map(
          hInds.lo -> headTerms.lo, hInds.hi -> headTerms.hi,
          hInds.res -> headTerms.res, hInds.arr -> headTerms.arr)

        val instrumentationConstraints : Seq[InstrumentationResult] =
          relevantConjuncts.headOption match {
            case Some(c) if isSelect(c) =>
              instrumentSelect(extractSelectInfo(c), headTerms, bodyTerms)
            case Some(c) if isStore(c) =>
              instrumentStore(extractStoreInfo(c), headTerms, bodyTerms)
            case Some(c) if isConst(c) =>
              instrumentConst(extractConstInfo(c), headTerms, bodyTerms)
            case None => Nil
          }
        for(instrumentationConstraint <- instrumentationConstraints) yield
          Instrumentation(instrumentationConstraint.conjunct,
            Seq(instrumentationConstraint.assertion), headTermMap)
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
      val bodyGhostVarInds : Seq[GhostVariableInds] =
        allGhostVarInds(bodyAtom.pred)
      val headGhostVarInds : Seq[GhostVariableInds] =
        allGhostVarInds(clause.head.pred)
      val unusedHeadBodyInds =
        (headGhostVarInds zip bodyGhostVarInds).filter(inds =>
          !inst.headTerms.contains(inds._1.lo))
      val identityInds =
        for((hInds, bInds) <- unusedHeadBodyInds) yield {
          val headTerms = GhostVariableTerms(
            lo = clause.head.args(hInds.lo), hi = clause.head.args(hInds.hi),
            res = clause.head.args(hInds.res), arr = clause.head.args(hInds.arr))
          val bodyTerms = GhostVariableTerms(
            lo = bodyAtom.args(bInds.lo), hi = bodyAtom.args(bInds.hi),
            res = bodyAtom.args(bInds.res), arr = bodyAtom.args(bInds.arr))
          val newConjunct =
            (headTerms.arr === bodyTerms.arr) &&&
              (headTerms.lo === bodyTerms.lo) &&&
              (headTerms.hi === bodyTerms.hi) &&&
              (headTerms.res === bodyTerms.res)
          val headTermMap : Map[Int, ITerm] = Map(
            hInds.lo -> headTerms.lo, hInds.hi -> headTerms.hi,
            hInds.res -> headTerms.res, hInds.arr -> headTerms.arr)
          Instrumentation(newConjunct, Nil, headTermMap)
        }
      identityInds.reduceOption(_ + _).
        getOrElse(Instrumentation.emptyInstrumentation) + inst
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

    combsForBodyAtoms.reduceOption((instrs1, instrs2) =>
      Instrumentation.product(instrs1, instrs2)).getOrElse(Nil) ++
      identityInstrsForBodyAtoms
  }
}

// A simple instrumenter that works for all extended quantifiers, but is very
// general and thus imprecise.
class SimpleClauseInstrumenter(extendedQuantifier : ExtendedQuantifier)
  extends ClauseInstrumenter(extendedQuantifier) {
  override protected
  def instrumentStore(storeInfo: StoreInfo,
                      headTerms : GhostVariableTerms,
                      bodyTerms: GhostVariableTerms): Seq[InstrumentationResult] = {
    val StoreInfo(a1, a2, i, o, arrayTheory2) = storeInfo
    if (arrayTheory != arrayTheory2)
      Nil
    else {
      import extendedQuantifier._
      import bodyTerms._
      import arrayTheory2._
      val instrConstraint1 =
        (headTerms.arr === a2) &&& ite(bodyTerms.lo === bodyTerms.hi,
          (headTerms.lo === i) & (headTerms.hi === i + 1) & (headTerms.res === o),
          ite((lo - 1 === i),
            (headTerms.res === reduceOp(res, o)) & (headTerms.lo === i) & headTerms.hi === hi,
            ite(hi === i,
              (headTerms.res === reduceOp(res, o)) & (headTerms.hi === i + 1 & headTerms.lo === lo),
              ite(lo <= i & hi > i,
                invReduceOp match {
                  case Some(f) => headTerms.res === reduceOp(f(res, select(a1, i)), o) & headTerms.lo === lo & headTerms.hi === hi
                  case _ => (headTerms.lo === i) & (headTerms.hi === i + 1) & (headTerms.res === o) //??? //TODO: Implement non-cancellative case
                },
                //hres === ifInsideBounds_help(o, arrayTheory.select(a1, i), bres) & hlo === blo & hhi === bhi, //relate to prev val
                (headTerms.lo === i) & (headTerms.hi === i + 1) & (headTerms.res === o))))) // outside bounds, reset
      val assertion = lo === hi ||| a1 === arr
      Seq(InstrumentationResult(instrConstraint1, assertion))
    }
  }

  override protected
  def instrumentSelect(selectInfo : SelectInfo,
                       headTerms  : GhostVariableTerms,
                       bodyTerms  : GhostVariableTerms): Seq[InstrumentationResult] = {
    val SelectInfo(a, i, o, arrayTheory2) = selectInfo
    if (arrayTheory != arrayTheory2)
      Nil
    else {
      import extendedQuantifier._
      import bodyTerms._
      val instrConstraint1 =
        (headTerms.arr === a) &&& ite(lo === hi,
          (headTerms.lo === i) & (headTerms.hi === i + 1) & (headTerms.res === o),
          ite((lo - 1 === i),
            (headTerms.res === reduceOp(res, o)) & (headTerms.lo === i) & headTerms.hi === hi,
            ite(hi === i,
              (headTerms.res === reduceOp(res, o)) & (headTerms.hi === i + 1 & headTerms.lo === lo),
              ite(lo <= i & hi > i,
                headTerms.res === res & headTerms.lo === lo & headTerms.hi === hi, // no change within bounds
                (headTerms.lo === i) & (headTerms.hi === i + 1) & (headTerms.res === o))))) // outside bounds, reset
      val assertion = lo === hi ||| a === arr
      Seq(InstrumentationResult(instrConstraint1, assertion))
    }
  }

  // todo: instrument const operation
  override protected
  def instrumentConst(constInfo : ConstInfo,
                      headTerms : GhostVariableTerms,
                      bodyTerms : GhostVariableTerms): Seq[InstrumentationResult] =
    Nil

  //  val ConstInfo(a, o, arrayTheory) = constInfo
  //  val instr =
  //    hhi === 10 &&& hlo === 0 &&& harr === a &&&
  //      hres === extendedQuantifier.reduceOp(o, o)
}