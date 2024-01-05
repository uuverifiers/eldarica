package lazabs.horn.extendedquantifiers

import ap.parser._
import ap.types.Sort
import lazabs.horn.extendedquantifiers.Util.{ConstInfo, ExtendedQuantifierApp, SelectInfo, StoreInfo}
import sun.reflect.generics.reflectiveObjects.NotImplementedException

object RewriteRules {
  case class Result(newConjunct     : IFormula,
                    rewriteFormulas : Map[IFormula, IFormula],
                    assertions      : Seq[IFormula])
}

abstract class GhostVar(val sort : Sort)

trait RewriteRules {
  // These rules are hardcoded as the array operations, but with some effort
  // the methods could also be generalized to a map from theory functions to
  // rewrite rules.

  /**
   * `oldGhostTerms` and `newGhostTerms` are the sequence of ghost variables
   * in the same order as [[InstrumentationOperator.ghostVars]], referring to
   * the old and new values of those variables, respectively.
   *
   * @param storeInfo
   * @return
   */
  def rewriteStore(oldGhostTerms : Map[GhostVar, ITerm],
                   newGhostTerms : Map[GhostVar, ITerm],
                   storeInfo     : StoreInfo) : Seq[RewriteRules.Result]
  def rewriteSelect(oldGhostTerms : Map[GhostVar, ITerm],
                    newGhostTerms : Map[GhostVar, ITerm],
                    selectInfo    : SelectInfo) : Seq[RewriteRules.Result]
  def rewriteConst(oldGhostTerms : Map[GhostVar, ITerm],
                   newGhostTerms : Map[GhostVar, ITerm],
                   constInfo     : ConstInfo) : Seq[RewriteRules.Result]
  def rewriteAggregate(ghostTerms : Seq[Map[GhostVar, ITerm]],
                       exqInfo    : ExtendedQuantifierApp) : Seq[RewriteRules.Result]
}

abstract class InstrumentationOperator(val exq : ExtendedQuantifier)
  extends RewriteRules {
  // old and new ghost variables will be passed in the same order as specified
  // in ghostVars.
  val ghostVars : Seq[GhostVar]
  // Initial values for the ghost variables. If an initial value is not found
  // for a GhostVar, it is not initialized to any value.
  val ghostVarInitialValues : Map[GhostVar, ITerm]
}

/**
 * A general instrumentation not specialized to any operator.
 */
class StandardInstrumentation(exq : ExtendedQuantifier)
  extends InstrumentationOperator(exq) {
  case object GhLo     extends GhostVar(exq.arrayIndexSort)
  case object GhHi     extends GhostVar(exq.arrayIndexSort)
  case object GhRes    extends GhostVar(exq.arrayTheory.objSort)
  case object GhArr    extends GhostVar(exq.arrayTheory.sort)
  case object GhArrInd extends GhostVar(exq.arrayIndexSort)

  /**
   * The concrete rewrite rules in this class depend on the order and length of
   * ghostVars, so those rules should be updated if ghostVars is modified.
   */
  override val ghostVars : Seq[GhostVar] =
    Seq(GhLo, GhHi, GhRes, GhArr, GhArrInd)

  override val ghostVarInitialValues : Map[GhostVar, ITerm] = Map(
    GhLo     -> IExpression.i(0),
    GhHi     -> IExpression.i(0),
    GhRes    -> exq.identity,
    GhArrInd -> IExpression.i(0)
    // GhArr is not initialized
  )

  private def pred(o : ITerm, i : ITerm) = exq.predicate match {
    case Some(p) => p(o, i)
    case None    => o
  }

  override def rewriteStore(oldGhostTerms : Map[GhostVar, ITerm],
                            newGhostTerms : Map[GhostVar, ITerm],
                            storeInfo     : StoreInfo)
  : Seq[RewriteRules.Result] = {
    import IExpression._
    import exq.arrayTheory.select

    val StoreInfo(a1, a2, i, o, arrayTheory2) = storeInfo

    if(arrayTheory2 != exq.arrayTheory) return Seq()

    val Seq(oldLo, oldHi, oldArr, oldRes, oldArrInd) =
      ghostVars.map(gVar => oldGhostTerms(gVar))
    val Seq(newLo, newHi, newRes, newArr, newArrInd) =
      ghostVars.map(gVar => newGhostTerms(gVar))

    // Array pass-through instrumentation for stores. This allows ignoring
    // stores to outside the tracked range.
    val arrayPassThroughInstrumentation : RewriteRules.Result = {
      val instrConstraint = {
        newLo === oldLo &&& newHi === oldHi &&& newRes === oldRes &&&
        ite(
          // if the write is outside bounds
          ((i < oldLo) ||| (oldHi <= i)) &&& (oldArr === a1),
          newArr === a2,
          newArr === oldArr)
      }
      RewriteRules.Result(newConjunct     = instrConstraint,
                          rewriteFormulas = Map(),
                          assertions      = Seq())
    }

    val standardInstrumentation = {
      val instrConstraint =
        (newArr === a2) &&&
        ite(oldLo === oldHi,
            (newLo === i) & (newHi === i + 1) & (newRes === pred(o, i)),
            ite((oldLo - 1 === i),
                (newRes === exq.reduceOp(oldRes, pred(o, i)))
                & (newLo === i) & newHi === oldHi,
                ite(oldHi === i,
                    (newRes === exq.reduceOp(oldRes, pred(o, i))) &
                    (newHi === i + 1 & newLo === oldLo),
                    ite(oldLo <= i & oldHi > i,
                        exq.invReduceOp match {
                          case Some(f) =>
                            newRes === exq.reduceOp(f(oldRes, select(a1, i)),
                                                    pred(o, i)) &
                            newLo === oldLo & newHi === oldHi
                          case _ =>
                            (newLo === i) & (newHi === i + 1) &
                            (newRes === pred(o, i))
                        },
                        (newLo === i) & (newHi === i + 1) &
                        (newRes === pred(o, i)))))) // outside bounds, reset
      val assertion  = oldLo === oldHi ||| a1 === oldArr

      RewriteRules.Result(newConjunct     = instrConstraint,
                          rewriteFormulas = Map(),
                          assertions      = Seq(assertion))
    }
    Seq(arrayPassThroughInstrumentation, standardInstrumentation)
  }

  override def rewriteSelect(oldGhostTerms : Map[GhostVar, ITerm],
                             newGhostTerms : Map[GhostVar, ITerm],
                             selectInfo    : SelectInfo)
  : Seq[RewriteRules.Result] = {
    import IExpression._

    val SelectInfo(a, i, o, arrayTheory2) = selectInfo

    if(arrayTheory2 != exq.arrayTheory) return Seq()

    val Seq(oldLo, oldHi, oldArr, oldRes, oldArrInd) =
      ghostVars.map(gVar => oldGhostTerms(gVar))
    val Seq(newLo, newHi, newRes, newArr, newArrInd) =
      ghostVars.map(gVar => newGhostTerms(gVar))

    val instrConstraint =
      (newArr === a) &&&
      ite(oldLo === oldHi,
          (newLo === i) & (newHi === i + 1) &
          (newRes === pred(o, i)),
          ite((oldLo - 1 === i),
              (newRes === exq.reduceOp(oldRes, pred(o, i))) &
              (newLo === i) & newHi === oldHi,
              ite(oldHi === i,
                  (newRes === exq.reduceOp(oldRes, pred(o, i))
                    ) & (newHi === i + 1 & newLo === oldLo),
                  ite(oldLo <= i & oldHi > i,
                      newRes === oldRes & newLo === oldLo & newHi === oldHi, // no change within bounds
                      (newLo === i) & (newHi === i + 1) &
                      (newRes === pred(o, i)))))) //outside bounds, reset
    val assertion = oldLo === oldHi ||| a === oldArr
    Seq(RewriteRules.Result(newConjunct = instrConstraint,
                            rewriteFormulas = Map(),
                            assertions = Seq(assertion)))
  }

  override def rewriteConst(oldGhostTerms : Map[GhostVar, ITerm],
                            newGhostTerms : Map[GhostVar, ITerm],
                            constInfo     : ConstInfo) : Seq[RewriteRules.Result] = {
    ???
  }

  override def rewriteAggregate(ghostTerms : Seq[Map[GhostVar, ITerm]],
                                exqInfo    : ExtendedQuantifierApp)
  : Seq[RewriteRules.Result] = {

    if(ghostTerms.size > 1) {
      // TODO: Generalize to multiple ghost variable ranges.
      throw new NotImplementedException
    }

    val ghostVarToGhostTerm = ghostTerms.head
    val Seq(gLo, gHi, gArr, gRes, gArrInd) =
      ghostVars.map(gVar => ghostVarToGhostTerm(gVar))

    val ExtendedQuantifierApp(_, funApp, a, lo, hi, o, conjunct) = exqInfo

    def loExpr = exq.rangeFormulaLo.getOrElse(
      (t1 : ITerm, t2 : ITerm, t3 : ITerm) => t1 === t2)
    def hiExpr = exq.rangeFormulaHi.getOrElse(
      (t1 : ITerm, t2 : ITerm, t3 : ITerm) => t1 === t2)

    val newConjunct =
      ((loExpr(gLo, lo, gRes) & hiExpr(gHi, hi, gRes) & gArr === a) ==>
       (gRes === o)) & ((lo >= hi) ==> (exq.identity === o))
    val assertionFormula =
      (loExpr(gLo, lo, gRes) & hiExpr(gHi, hi, gRes) & gArr === a) | (lo >= hi)

    Seq(RewriteRules.Result(
      newConjunct     = IExpression.i(true),
      rewriteFormulas = Map(conjunct -> newConjunct),
      assertions      = Seq(assertionFormula)))
  }
}

