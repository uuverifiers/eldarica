package lazabs.horn.extendedquantifiers

import ap.parser._
import lazabs.horn.extendedquantifiers.Util.{ConstInfo, ExtendedQuantifierInfo, SelectInfo, StoreInfo}
import sun.reflect.generics.reflectiveObjects.NotImplementedException

object RewriteRules {
  case class Result(newConjunct     : IFormula,
                    rewriteFormulas : Map[IFormula, IFormula],
                    assertions      : Seq[IFormula])
}

abstract class GhostVar

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
  def ruleStore(oldGhostTerms : Seq[ITerm],
                newGhostTerms : Seq[ITerm],
                storeInfo     : StoreInfo) : Seq[RewriteRules.Result]
  def ruleSelect(oldGhostTerms : Seq[ITerm],
                 newGhostTerms : Seq[ITerm],
                 selectInfo    : SelectInfo) : Seq[RewriteRules.Result]
  def ruleConst(oldGhostTerms : Seq[ITerm],
                newGhostTerms : Seq[ITerm],
                constInfo     : ConstInfo) : Seq[RewriteRules.Result]
  def ruleAggregate(ghostTerms : Seq[Seq[ITerm]],
                    exqInfo : ExtendedQuantifierInfo) : Seq[RewriteRules.Result]
}

abstract class InstrumentationOperator extends RewriteRules {
  // old and new ghost variables will be passed in the same order as specified
  // in ghostVars.
  val ghostVars : Seq[GhostVar]
}

/**
 * A general instrumentation not specialized to any operator.
 */
class StandardInstrumentation(exq : ExtendedQuantifier) extends InstrumentationOperator {
  case object GhLo     extends GhostVar
  case object GhHi     extends GhostVar
  case object GhRes    extends GhostVar
  case object GhArr    extends GhostVar
  case object GhArrInd extends GhostVar

  override val ghostVars : Seq[GhostVar] =
    Seq(GhLo, GhHi, GhRes, GhArr, GhArrInd)

  private def pred(o : ITerm, i : ITerm) = exq.predicate match {
    case Some(p) => p(o, i)
    case None    => o
  }

  override def ruleStore(oldGhostTerms : Seq[ITerm],
                         newGhostTerms : Seq[ITerm],
                         storeInfo     : StoreInfo)
  : Seq[RewriteRules.Result] = {
    import IExpression._
    import exq.arrayTheory.select

    val Seq(oldLo, oldHi, oldRes, oldArr, oldArrInd) = oldGhostTerms
    val Seq(newLo, newHi, newRes, newArr, newArrInd) = newGhostTerms

    val StoreInfo(a1, a2, i, o, arrayTheory2) = storeInfo

    if(arrayTheory2 != exq.arrayTheory) return Seq()

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

  override def ruleSelect(oldGhostTerms : Seq[ITerm],
                          newGhostTerms : Seq[ITerm],
                          selectInfo    : SelectInfo)
  : Seq[RewriteRules.Result] = {
    import IExpression._

    val Seq(oldLo, oldHi, oldRes, oldArr, oldArrInd) = oldGhostTerms
    val Seq(newLo, newHi, newRes, newArr, newArrInd) = newGhostTerms
    val SelectInfo(a, i, o, arrayTheory2) = selectInfo

    if(arrayTheory2 != exq.arrayTheory) return Seq()

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

  override def ruleConst(oldGhostTerms : Seq[ITerm],
                         newGhostTerms : Seq[ITerm],
                         constInfo : ConstInfo) : Seq[RewriteRules.Result] = {
    ???
  }

  override def ruleAggregate(ghostTerms : Seq[Seq[ITerm]],
                             exqInfo : ExtendedQuantifierInfo)
  : Seq[RewriteRules.Result] = {

    if(ghostTerms.size > 1) {
      // TODO: Generalize to multiple ghost variable ranges.
      throw new NotImplementedException
    }

    val Seq(gLo, gHi, gRes, gArr, gArrInd) = ghostTerms.head
    val ExtendedQuantifierInfo(_, funApp, a, lo, hi, o, conjunct) = exqInfo

    val newConjunct =
      ((gLo === lo & gHi === hi & gArr === a) ==> (gRes === o)) &&&
      ((lo >= hi) ==> (exq.identity === o))
    val assertionFormula =
      (gLo === lo & gHi === hi & gArr === a) ||| (gLo >= gHi)

    Seq(RewriteRules.Result(
      newConjunct     = IExpression.i(true),
      rewriteFormulas = Map(conjunct -> newConjunct),
      assertions      = Seq(assertionFormula)))
  }
}

