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

import ap.parser.IExpression.i
import ap.parser._
import ap.terfor.ConstantTerm
import ap.theories.ADT
import ap.types.Sort
import lazabs.horn.extendedquantifiers.InstrumentationOperator.GhostVar
import lazabs.horn.extendedquantifiers.Util._
import lazabs.horn.extendedquantifiers._
import lazabs.horn.extendedquantifiers.theories.ExtendedQuantifierWithPredicate
import lazabs.prover.PrincessWrapper.expr2Formula

import scala.collection.mutable.ArrayBuffer

/**
 * An instrumentation operator for forall and exists.
 */
class BooleanInstrumentationOperator(exq : ExtendedQuantifierWithPredicate)
    extends InstrumentationOperator(exq) {
  // Extended quantifier ghost variables.
  case object GhLo     extends GhostVar(exq.arrayIndexSort, "gLo")
  case object GhHi     extends GhostVar(exq.arrayIndexSort, "gHi")
  case object GhRes    extends GhostVar(exq.arrayTheory.objSort, "gRes")
  case object GhArr    extends GhostVar(exq.arrayTheory.sort, "gArr")
  case object GhArrInd extends GhostVar(exq.arrayIndexSort, "gArrInd")

  /**
   * In the paper we cannot deal with alien terms appearing in
   * [[ExtendedQuantifierWithPredicate.predicate]].
   * Example: in `p(o, i): o = i + c`, `c` is an alien term.
   *
   * In practice such terms pop up often. To deal with such terms, we do an
   * encoding as follows:
   * (1)Introduce a pair of ghost variables `(cShad, cSet)` for each `c`.
   *    Primed versions denote the corresponding updated variables. Note that
   *    these ghost variables track actual variables of the program and do not
   *    need to be duplicated as other ghost variables with more tracked ranges,
   *    but for simplicity of the implementation we duplicate them too.
   * (2)During instrumentation, for each `c`, add the following as a conjunct
   *    to the instrumentation constraint:
   *      `cShad' = ite(cSet, cShad, c) & cSet'`
   *    This ensures that cShad tracks c and is set.
   *    And add the following as an assertion:
   *      `cSet ==> (cShad === c))`
   *    This fails if `cShad` is tracking the wrong `c`. This can happen because
   *    the implementation ''guesses'' which `c` to track in the clauses by the
   *    name of `c`, which can be incorrect. If this assertion fails, that means
   *    the guess was incorrect.
   */

  case class AlienGhostVars(vShad : GhostVar, vSet : GhostVar)

  // We declare two case classes to be able to easily distinguish between the
  // 'shadow' and 'set' ghost variables for alien terms.
  case class GhAlienShad(_sort : Sort, _name : String)
    extends GhostVar(_sort, _name)
  case class GhAlienSet (_name : String) extends GhostVar(Sort.Bool, _name)

  private val alienShadowVarSuffix = "Shad"
  private val alienSetVarSuffix = "Set"

  val alienConstantToAlienGhostVars : Map[ConstantTerm, AlienGhostVars] =
    (for (c <- exq.alienConstants) yield {
      // As per (1) from the explanation above, create one pair per constant.
      val vShad = GhAlienShad(Sort.sortOf(IConstant(c)), c.name ++ alienShadowVarSuffix)
      val vSet  = GhAlienSet(c.name ++ alienSetVarSuffix)
      c -> AlienGhostVars(vShad = vShad, vSet = vSet)
    }).toMap

  /**
   * A utility method to guess alien terms for their corresponding ghost
   * variables. Returns a map from alien ghost variables to the guessed terms.
   * @note The guess is primitive and tries to find a constant such that its
   *       name appended with [[alienShadowVarSuffix]] corresponds to the ghost
   *       variable.
   */
  private def guessAlienTerms(nonGhostConstants : Set[IConstant])
  : Map[GhostVar, IConstant] = {
    val vShads = alienConstantToAlienGhostVars.values.map(_.vShad)
    for (vShad <- vShads;
         term <- nonGhostConstants.find(
           term => vShad.name contains(term.c.name ++ alienShadowVarSuffix))
    ) yield vShad -> term
  }.toMap

  private def getAlienTermsFormulaAndAssertion(
    oldGhostTerms         : Map[GhostVar, ITerm],
    newGhostTerms         : Map[GhostVar, ITerm],
    alienVarToGuessedTerm : Map[GhostVar, IConstant]) : (IFormula, IFormula) = {
    val initConjuncts      = new ArrayBuffer[IFormula]
    val assertionConjuncts = new ArrayBuffer[IFormula]

    for ((_, AlienGhostVars(vShad, vSet)) <- alienConstantToAlienGhostVars
         if alienVarToGuessedTerm contains vShad) {
      val vShadOld = oldGhostTerms(vShad)
      val vSetOld  = oldGhostTerms(vSet)
      val vShadNew = newGhostTerms(vShad)
      val vSetNew  = newGhostTerms(vSet)

      initConjuncts +=
      ((expr2Formula(vSetOld) &&& vShadOld === vShadNew) |||
       vShadNew === alienVarToGuessedTerm(vShad)) &&& expr2Formula(vSetNew)

      assertionConjuncts +=
      (expr2Formula(vSetNew) ==> (vShadOld === alienVarToGuessedTerm(vShad)))// &&&
      (expr2Formula(vSetNew))
    }

    (initConjuncts.fold(i(true))((c1, c2) => c1 &&& c2),
      assertionConjuncts.fold(i(true))((c1, c2) => c1 &&& c2))
  }

  // Alien ghost variables should not be duplicated, so we declare them as such.
  val alienGhostVars : Seq[GhostVar] =
    alienConstantToAlienGhostVars.values.flatMap(
      pair => Seq(pair.vShad, pair.vSet)).toSeq

  /**
   * Declare the ghost variables for the extended quantifier + other ghosts.
   */
  override val ghostVars : Seq[GhostVar] =
    Seq(GhLo, GhHi, GhRes, GhArr, GhArrInd) ++ alienGhostVars

  private val alienGhostVarInitialValues : Map[GhostVar, ITerm] =
    alienGhostVars.collect{
      // GhAlienShad variables should be left uninitialized so we only set vSet
      // to false during initialization.
      case vSet  : GhAlienSet => vSet   -> ADT.BoolADT.False
    }.toMap

  override val ghostVarInitialValues: Map[GhostVar, ITerm] = Map(
    GhLo     -> IExpression.i(0),
    GhHi     -> IExpression.i(0),
    GhRes    -> exq.identity,
    GhArrInd -> IExpression.i(0)
    // GhArr is left uninitialized
  ) ++ alienGhostVarInitialValues

  /**
   * This is used during back-translation of solutions.
   * @todo Do we need to consider the back-translation of alien ghost variables?
   */
  override def ghostVarsToAggregateFormula(ghostTerms : Map[GhostVar, ITerm])
  : IFormula = {
    import IExpression._
    assert(ghostVars.forall(ghostTerms contains))
    // exq.morphism(arr, lo, hi) === res
    exq.applyMorphism(ghostTerms(GhArr),
                      ghostTerms(GhLo),
                      ghostTerms(GhHi)) === ghostTerms(GhRes)
  }

  //////////////////////////////////////////////////////////////////////////////
  /**
   * A convenience method that uses the predicate of the extended quantifier
   * theory.
   * @param o `o` in `a[i] = o`
   * @param i `i` in `a[i] = o`
   * @param alienSubstMap If the predicate contains alien terms, these should be
   *                      rewritten. This map provides that information.
   */
  private def pred(o: ITerm,
                   i: ITerm,
                   alienSubstMap : Map[ConstantTerm, ITerm]) =
    if(alienSubstMap.nonEmpty)
      // rewrite alien terms in the app to their corresponding ghost variables
      ConstantSubstVisitor(exq.predicate(o, i), alienSubstMap)
    else exq.predicate(o, i)

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

    val alienSubstMap : Map[ConstantTerm, ITerm] =
      (for (alienC <- exq.alienConstants) yield {
        alienC -> newGhostTerms(alienConstantToAlienGhostVars(alienC).vShad)
      }).toMap

    val alienTermGuesses = guessAlienTerms(otherConstants)

    val (alienTermInitFormula, alienTermAssertionFormula) =
      getAlienTermsFormulaAndAssertion(oldGhostTerms, newGhostTerms,
                                       alienTermGuesses)

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
      val storeEmptySeq = (newLo === i) & (newHi === i + 1) &
                            (newRes === pred(o, i, alienSubstMap))
      val storeBelow =
        (newRes === exq.reduceOp(oldRes, pred(o, i, alienSubstMap))) &
          (newLo === i) & newHi === oldHi
      val storeAbove =
        (newRes === exq.reduceOp(oldRes, pred(o, i, alienSubstMap))) &
          (newHi === i + 1 & newLo === oldLo)
      val storeInside =
        exq.invReduceOp match {
          case Some(f) =>
            newRes === exq.reduceOp(
              f(oldRes, exq.arrayTheory.select(a1, i)),
              pred(o, i, alienSubstMap)) &
            newLo === oldLo & newHi === oldHi
          case _ =>
            storeEmptySeq
        }
        val storeOutside = storeEmptySeq

      val instrConstraint =
        (newArr === a2) &&& alienTermInitFormula &&&
          ite(oldLo === oldHi, storeEmptySeq,
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
      val assertion = oldLo === oldHi ||| (a1 === oldArr &&&
                                           alienTermAssertionFormula)

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

    val alienSubstMap : Map[ConstantTerm, ITerm] =
      (for (alienC <- exq.alienConstants) yield {
        alienC -> newGhostTerms(alienConstantToAlienGhostVars(alienC).vShad)
      }).toMap

    val alienTermGuesses = guessAlienTerms(otherConstants)

    val (alienTermInitFormula, alienTermAssertionFormula) =
      getAlienTermsFormulaAndAssertion(oldGhostTerms, newGhostTerms,
                                       alienTermGuesses)
    val selectEmptySeq = (newLo === i) & (newHi === i + 1) &
                          (newRes === pred(o, i, alienSubstMap))
    val selectBelow =
      (newRes === exq.reduceOp(oldRes, pred(o, i, alienSubstMap))) &
        (newLo === i) & newHi === oldHi
    val selectAbove =
      (newRes === exq.reduceOp(oldRes, pred(o, i, alienSubstMap))) &
        (newHi === i + 1 & newLo === oldLo)
    val selectInside = newRes === oldRes & newLo === oldLo & newHi === oldHi //
    // no change within bounds
    val selectOutside = selectEmptySeq

    val instrConstraint =
      (newArr === a) &&& alienTermInitFormula &&&
        ite(
          oldLo === oldHi,
          selectEmptySeq,
          ite(
            (oldLo - 1 === i),
            selectBelow,
            ite(
              oldHi === i,
              selectAbove,
              ite(oldLo <= i & oldHi > i,
                  selectInside,
                  selectOutside
                  )
            )
          )
        ) //outside bounds, reset
    val assertion = oldLo === oldHi ||| (a === oldArr &&& alienTermAssertionFormula)
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

    val ghostVarToGhostTerm = ghostTerms.head
    val Seq(gLo, gHi, gArr, gRes, gArrInd) = Seq(
      ghostVarToGhostTerm(GhLo),
      ghostVarToGhostTerm(GhHi),
      ghostVarToGhostTerm(GhArr),
      ghostVarToGhostTerm(GhRes),
      ghostVarToGhostTerm(GhArrInd)
    )

    val ExtendedQuantifierApp(_, funApp, a, lo, hi, o, alienTerms, conjunct) =
      exqInfo

    def loExpr =
      exq.rangeFormulaLo.getOrElse((t1: ITerm, t2: ITerm, t3: ITerm) =>
        t1 === t2)
    def hiExpr =
      exq.rangeFormulaHi.getOrElse((t1: ITerm, t2: ITerm, t3: ITerm) =>
        t1 === t2)

    val alienGuard = {
      for ((alienC, ind) <- exq.alienConstants zipWithIndex)
        yield {
          val AlienGhostVars(vShad, vSet) = alienConstantToAlienGhostVars(alienC)
          expr2Formula(ghostVarToGhostTerm(vSet)) &&&
          (ghostVarToGhostTerm(vShad) === alienTerms(ind))
        }
    }.fold(i(true))((c1, c2) => c1 &&& c2)

    val newConjunct =
      ((loExpr(gLo, lo, gRes) & hiExpr(gHi, hi, gRes) & gArr === a) ==>
        (gRes === o)) & ((lo >= hi) ==> (exq.identity === o))
    val assertionFormula =
      (loExpr(gLo, lo, gRes) & hiExpr(gHi, hi, gRes) &
       gArr === a &&& alienGuard) ||| (lo >= hi)

    Seq(RewriteRules.Result(newConjunct = IExpression.i(true),
                            rewriteFormulas = Map(conjunct -> newConjunct),
                            assertions = Seq(assertionFormula)))
  }
}
