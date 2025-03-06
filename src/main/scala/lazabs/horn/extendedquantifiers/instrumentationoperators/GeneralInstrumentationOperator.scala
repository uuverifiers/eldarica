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


package lazabs.horn.extendedquantifiers.instrumentationoperators

import ap.parser.{IConstant, IExpression, IFormula, ITerm}
import lazabs.horn.extendedquantifiers.Util._
import lazabs.horn.extendedquantifiers._
import InstrumentationOperator.GhostVar
import lazabs.horn.extendedquantifiers.theories.ExtendedQuantifier

/**
 * A general instrumentation operator suitable for \sum, \min and \max.
 */
class GeneralInstrumentationOperator(exq: ExtendedQuantifier)
    extends InstrumentationOperator(exq) {
  // Extended quantifier ghost variables.
  case object GhLo     extends GhostVar(exq.arrayIndexSort, "gLo")
  case object GhHi     extends GhostVar(exq.arrayIndexSort, "gHi")
  case object GhRes    extends GhostVar(exq.arrayTheory.objSort, "gRes")
  case object GhArr    extends GhostVar(exq.arrayTheory.sort, "gArr")
  case object GhArrInd extends GhostVar(exq.arrayIndexSort, "gArrInd")

  /**
   * Declare the ghost variables for the extended quantifier + other ghosts.
   */
  override val ghostVars : Seq[GhostVar] =
    Seq(GhLo, GhHi, GhRes, GhArr, GhArrInd)

  override val ghostVarInitialValues: Map[GhostVar, ITerm] = Map(
    GhLo     -> IExpression.i(0),
    GhHi     -> IExpression.i(0),
    GhRes    -> exq.identity,
    GhArrInd -> IExpression.i(0)
    // GhArr is left uninitialized
  )

  override def ghostVarsToAggregateFormula(ghostTerms : Map[GhostVar, ITerm])
  : IFormula = {
    import IExpression._
    assert(ghostVars.forall(ghostTerms contains))
    // exq.morphism(arr, lo, hi) === res
    exq.morphism(ghostTerms(GhArr),
                 ghostTerms(GhLo),
                 ghostTerms(GhHi)) === ghostTerms(GhRes)
  }

  //////////////////////////////////////////////////////////////////////////////

  override def rewriteStore(oldGhostTerms  : Map[GhostVar, ITerm],
                            newGhostTerms  : Map[GhostVar, ITerm],
                            otherConstants : Set[IConstant],
                            storeInfo      : StoreInfo)
  : Seq[RewriteRules.Result] = {
    import IExpression._

    val StoreInfo(a1, a2, i, o, arrayTheory2) = storeInfo

    if (arrayTheory2 != exq.arrayTheory) return Seq()

    val (oldLo, newLo)         = (oldGhostTerms(GhLo), newGhostTerms(GhLo))
    val (oldHi, newHi)         = (oldGhostTerms(GhHi), newGhostTerms(GhHi))
    val (oldRes, newRes)       = (oldGhostTerms(GhRes), newGhostTerms(GhRes))
    val (oldArr, newArr)       = (oldGhostTerms(GhArr), newGhostTerms(GhArr))
    val (oldArrInd, newArrInd) = (oldGhostTerms(GhArrInd), newGhostTerms(GhArrInd))

    // Array pass-through instrumentation for stores. This allows ignoring
    // stores to outside the tracked range.
    val arrayPassThroughInstrumentation: RewriteRules.Result = {
      val instrConstraint = {
        newLo === oldLo &&& newHi === oldHi &&& newRes === oldRes &&&
          ite(
              // if the write is outside bounds
              ((i < oldLo) ||| (oldHi <= i)) &&& (oldArr === a1),
              newArr === a2,
              newArr === oldArr)
      }
      RewriteRules.Result(newConjunct = instrConstraint,
                          rewriteFormulas = Map(),
                          assertions = Seq())
    }

    val standardInstrumentation = {
      val storeEmptySeq = (newLo === i) & (newHi === i + 1) & (newRes === o)
      val storeBelow = (newRes === exq.reduceOp(oldRes, o)) &
                        (newLo === i) & newHi === oldHi
      val storeAbove = (newRes === exq.reduceOp(oldRes, o)) &
        (newHi === i + 1 & newLo === oldLo)
      val storeInside = exq.invReduceOp match {
        case Some(f) =>
          newRes === exq.reduceOp(
            f(oldRes, exq.arrayTheory.select(a1, i)),
            o) &
          newLo === oldLo & newHi === oldHi
        case _ =>
          (newLo === i) & (newHi === i + 1) &
            (newRes === o)
      }
      val storeOutside = (newLo === i) & (newHi === i + 1) & (newRes === o)
      val instrConstraint =
        (newArr === a2) &&&
          ite(
            oldLo === oldHi,
            storeEmptySeq,
            ite(
              (oldLo - 1 === i),
              storeBelow,
              ite(
                oldHi === i,
                storeAbove,
                ite(
                  oldLo <= i & oldHi > i,
                  storeInside,
                  storeOutside
                )
              )
            )
          ) // outside bounds, reset
      val assertion = oldLo === oldHi ||| (a1 === oldArr)

      RewriteRules.Result(newConjunct = instrConstraint,
                          rewriteFormulas = Map(),
                          assertions = Seq(assertion))
    }
    Seq(arrayPassThroughInstrumentation, standardInstrumentation)
  }

  override def rewriteSelect(
      oldGhostTerms  : Map[GhostVar, ITerm],
      newGhostTerms  : Map[GhostVar, ITerm],
      otherConstants : Set[IConstant],
      selectInfo     : SelectInfo) : Seq[RewriteRules.Result] = {
    import IExpression._

    val SelectInfo(a, i, o, arrayTheory2) = selectInfo

    if (arrayTheory2 != exq.arrayTheory) return Seq()

    val (oldLo, newLo)         = (oldGhostTerms(GhLo), newGhostTerms(GhLo))
    val (oldHi, newHi)         = (oldGhostTerms(GhHi), newGhostTerms(GhHi))
    val (oldRes, newRes)       = (oldGhostTerms(GhRes), newGhostTerms(GhRes))
    val (oldArr, newArr)       = (oldGhostTerms(GhArr), newGhostTerms(GhArr))
    val (oldArrInd, newArrInd) = (oldGhostTerms(GhArrInd), newGhostTerms(GhArrInd))

    val selectEmpty = (newLo === i) & (newHi === i + 1) &
      (newRes === o)
    val selectBelow = (newRes === exq.reduceOp(oldRes, o)) &
                      (newLo === i) & (newHi === oldHi)
    val selectAbove = (newRes === exq.reduceOp(oldRes, o)) &
                      (newHi === i + 1 & newLo === oldLo)
    val selectInside = newRes === oldRes & newLo === oldLo & newHi === oldHi
    val selectOutside = (newLo === i) & (newHi === i + 1) & (newRes === o)

    val instrConstraint =
      (newArr === a) &&&
        ite(
          oldLo === oldHi,
          selectEmpty,
          ite(
            (oldLo - 1 === i),
            selectBelow,
            ite(
              oldHi === i,
              selectAbove,
              ite(oldLo <= i & oldHi > i,
                  selectInside, //
                  // no change within bounds
                  selectOutside
              )
            )
          )
        ) //outside bounds, reset
    val assertion = (oldLo === oldHi) ||| (a === oldArr)
    Seq(RewriteRules.Result(newConjunct = instrConstraint,
                            rewriteFormulas = Map(),
                            assertions = Seq(assertion)))
  }

  override def rewriteConst(oldGhostTerms  : Map[GhostVar, ITerm],
                            newGhostTerms  : Map[GhostVar, ITerm],
                            otherConstants : Set[IConstant],
                            constInfo      : ConstInfo)
  : Seq[RewriteRules.Result] = {
    ???
  }

  override def rewriteAggregate(ghostTerms : Seq[Map[GhostVar, ITerm]],
                                exqInfo    : ExtendedQuantifierApp)
  : Seq[RewriteRules.Result] = {
    if (ghostTerms.size > 1) {
      // TODO: Generalize to multiple ghost variable ranges.
      throw new NotImplementedError(
        "Multiple ghost variable sets are currently unsupported.")
    }

    val ghostVarToGhostTerm                = ghostTerms.head
    val Seq(gLo, gHi, gArr, gRes, gArrInd) = Seq(
      ghostVarToGhostTerm(GhLo),
      ghostVarToGhostTerm(GhHi),
      ghostVarToGhostTerm(GhArr),
      ghostVarToGhostTerm(GhRes),
      ghostVarToGhostTerm(GhArrInd)
    )

    val ExtendedQuantifierApp(_, funApp, a, lo, hi, o, _, conjunct) = exqInfo

    def loExpr =
      exq.rangeFormulaLo.getOrElse((t1: ITerm, t2: ITerm, t3: ITerm) =>
        t1 === t2)
    def hiExpr =
      exq.rangeFormulaHi.getOrElse((t1: ITerm, t2: ITerm, t3: ITerm) =>
        t1 === t2)

    val newConjunct =
      ((loExpr(gLo, lo, gRes) & hiExpr(gHi, hi, gRes) & gArr === a) ==>
        (gRes === o)) & ((lo >= hi) ==> (exq.identity === o))
    val assertionFormula =
      (loExpr(gLo, lo, gRes) & hiExpr(gHi, hi, gRes) & gArr === a) | (lo >= hi)

    Seq(RewriteRules.Result(newConjunct = IExpression.i(true),
                            rewriteFormulas = Map(conjunct -> newConjunct),
                            assertions = Seq(assertionFormula)))
  }
}
