package lazabs.horn.extendedquantifiers.instrumentationoperators

import ap.parser.{IConstant, IExpression, ITerm}
import lazabs.horn.extendedquantifiers.Util._
import lazabs.horn.extendedquantifiers._
import InstrumentationOperator.GhostVar
import ap.terfor.ConstantTerm
import ap.theories.ADT
import ap.types.Sort

/**
 * A general instrumentation not specialized to any operator.
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
   * In the paper we cannot deal with alien terms appearing in
   * [[ExtendedQuantifier.predicate]].
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
   *      `ite(cSet, cShad' === cShad, cShad' = c) & cSet'`
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

  val alienConstantToAlienGhostVars : Map[ConstantTerm, AlienGhostVars] =
    (for (c <- exq.alienConstantsInPredicate) yield {
      // As per (1) from the explanation above, create one pair per constant.
      val vShad = GhAlienShad(Sort.sortOf(IConstant(c)), c.name + "Shad")
      val vSet  = GhAlienSet(c.name + "Set")
      c -> AlienGhostVars(vShad = vShad, vSet = vSet)
    }).toMap

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
      case vSet : GhAlienSet => vSet -> ADT.BoolADT.False
    }.toMap

  override val ghostVarInitialValues: Map[GhostVar, ITerm] = Map(
    GhLo     -> IExpression.i(0),
    GhHi     -> IExpression.i(0),
    GhRes    -> exq.identity,
    GhArrInd -> IExpression.i(0)
    // GhArr is not initialized
  ) ++ alienGhostVarInitialValues

  //////////////////////////////////////////////////////////////////////////////
  /**
   * A convenience method that uses the predicate of the extended quantifier
   * theory, if one is provided, otherwise the passed object. This allows
   * having a common encoding for extended quantifiers with predicates and
   * without predicates.
   * @param o `o` in `a[i] = o`
   * @param i `i` in `a[i] = o`
   */
  private def pred(o: ITerm, i: ITerm) = exq.predicate match {
    case Some(p) => p(o, i)
    case None    => o
  }

  override def rewriteStore(oldGhostTerms: Map[GhostVar, ITerm],
                            newGhostTerms: Map[GhostVar, ITerm],
                            storeInfo:     StoreInfo)
  : Seq[RewriteRules.Result] = {
    import IExpression._

    val StoreInfo(a1, a2, i, o, arrayTheory2) = storeInfo

    if (arrayTheory2 != exq.arrayTheory) return Seq()

    val Seq(oldLo, oldHi, oldArr, oldRes, oldArrInd) =
      ghostVars.map(gVar => oldGhostTerms(gVar))
    val Seq(newLo, newHi, newRes, newArr, newArrInd) =
      ghostVars.map(gVar => newGhostTerms(gVar))

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
      val instrConstraint =
        (newArr === a2) &&&
          ite(
            oldLo === oldHi,
            (newLo === i) & (newHi === i + 1) & (newRes === pred(o, i)),
            ite(
              (oldLo - 1 === i),
              (newRes === exq.reduceOp(oldRes, pred(o, i)))
                & (newLo === i) & newHi === oldHi,
              ite(
                oldHi === i,
                (newRes === exq.reduceOp(oldRes, pred(o, i))) &
                  (newHi === i + 1 & newLo === oldLo),
                ite(
                  oldLo <= i & oldHi > i,
                  exq.invReduceOp match {
                    case Some(f) =>
                      newRes === exq.reduceOp(
                        f(oldRes, exq.arrayTheory.select(a1, i)), pred(o, i)) &
                      newLo === oldLo & newHi === oldHi
                    case _ =>
                      (newLo === i) & (newHi === i + 1) &
                        (newRes === pred(o, i))
                  },
                  (newLo === i) & (newHi === i + 1) &
                    (newRes === pred(o, i))
                )
              )
            )
          ) // outside bounds, reset
      val assertion = oldLo === oldHi ||| a1 === oldArr

      RewriteRules.Result(newConjunct = instrConstraint,
                          rewriteFormulas = Map(),
                          assertions = Seq(assertion))
    }
    Seq(arrayPassThroughInstrumentation, standardInstrumentation)
  }

  override def rewriteSelect(
      oldGhostTerms : Map[GhostVar, ITerm],
      newGhostTerms : Map[GhostVar, ITerm],
      selectInfo    : SelectInfo) : Seq[RewriteRules.Result] = {
    import IExpression._

    val SelectInfo(a, i, o, arrayTheory2) = selectInfo

    if (arrayTheory2 != exq.arrayTheory) return Seq()

    val Seq(oldLo, oldHi, oldArr, oldRes, oldArrInd) =
      ghostVars.map(gVar => oldGhostTerms(gVar))
    val Seq(newLo, newHi, newRes, newArr, newArrInd) =
      ghostVars.map(gVar => newGhostTerms(gVar))

    val instrConstraint =
      (newArr === a) &&&
        ite(
          oldLo === oldHi,
          (newLo === i) & (newHi === i + 1) &
            (newRes === pred(o, i)),
          ite(
            (oldLo - 1 === i),
            (newRes === exq.reduceOp(oldRes, pred(o, i))) &
              (newLo === i) & newHi === oldHi,
            ite(
              oldHi === i,
              (newRes === exq
                .reduceOp(oldRes, pred(o, i))) & (newHi === i + 1 & newLo ===
                                                                    oldLo),
              ite(oldLo <= i & oldHi > i,
                  newRes === oldRes & newLo === oldLo & newHi === oldHi, //
                  // no change within bounds
                  (newLo === i) & (newHi === i + 1) &
                    (newRes === pred(o, i)))
            )
          )
        ) //outside bounds, reset
    val assertion = oldLo === oldHi ||| a === oldArr
    Seq(RewriteRules.Result(newConjunct = instrConstraint,
                            rewriteFormulas = Map(),
                            assertions = Seq(assertion)))
  }

  override def rewriteConst(oldGhostTerms : Map[GhostVar, ITerm],
                            newGhostTerms : Map[GhostVar, ITerm],
                            constInfo     : ConstInfo)
  : Seq[RewriteRules.Result] = {
    ???
  }

  override def rewriteAggregate(ghostTerms : Seq[Map[GhostVar, ITerm]],
                                exqInfo    :    ExtendedQuantifierApp)
  : Seq[RewriteRules.Result] = {
    if (ghostTerms.size > 1) {
      // TODO: Generalize to multiple ghost variable ranges.
      throw new NotImplementedError("Multiple ghost variable sets are currently" +
                                    "unsupported.")
    }

    val ghostVarToGhostTerm = ghostTerms.head
    val Seq(gLo, gHi, gArr, gRes, gArrInd) =
      ghostVars.map(gVar => ghostVarToGhostTerm(gVar))

    val ExtendedQuantifierApp(_, funApp, a, lo, hi, o, conjunct) = exqInfo

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
