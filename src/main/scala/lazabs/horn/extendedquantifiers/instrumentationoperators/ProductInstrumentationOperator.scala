package lazabs.horn.extendedquantifiers.instrumentationoperators

import ap.parser.{ConstantSubstVisitor, IBoolLit, IConstant, IExpression, IFormula, ITerm}
import lazabs.horn.extendedquantifiers.Util._
import lazabs.horn.extendedquantifiers._
import InstrumentationOperator.GhostVar
import ap.parser.IExpression.i
import ap.terfor.ConstantTerm
import ap.theories.ADT
import ap.types.Sort
import lazabs.prover.PrincessWrapper.expr2Formula

import scala.collection.mutable.ArrayBuffer

/**
 * A general instrumentation operator suitable for \sum, \min and \max.
 */
class ProductInstrumentationOperator(exq: ExtendedQuantifier)
    extends InstrumentationOperator(exq) {
  // Extended quantifier ghost variables.
  case object GhLo     extends GhostVar(exq.arrayIndexSort, "gLo")
  case object GhHi     extends GhostVar(exq.arrayIndexSort, "gHi")
  case object GhRes    extends GhostVar(exq.arrayTheory.objSort, "gRes")
  case object GhArr    extends GhostVar(exq.arrayTheory.sort, "gArr")
  case object GhArrInd extends GhostVar(exq.arrayIndexSort, "gArrInd")
  case object GhZeroCnt extends GhostVar(Sort.Integer, "ghZeroCnt")

  /**
   * Declare the ghost variables for the extended quantifier + other ghosts.
   */
  override val ghostVars : Seq[GhostVar] =
    Seq(GhLo, GhHi, GhRes, GhArr, GhArrInd, GhZeroCnt)

  override val ghostVarInitialValues: Map[GhostVar, ITerm] = Map(
    GhLo     -> IExpression.i(0),
    GhHi     -> IExpression.i(0),
    GhRes    -> exq.identity,
    GhArrInd -> IExpression.i(0),
    // GhArr is left uninitialized
    GhZeroCnt -> IExpression.i(0)
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
    val (oldZeroCnt, newZeroCnt) = (oldGhostTerms(GhZeroCnt), newGhostTerms(GhZeroCnt))

    def zeroReduceOp(res: ITerm, newVal: ITerm) =
        { ite(newVal === 0, res, exq.reduceOp(res,newVal)) }
    def zeroInvReduceOp(res:ITerm, oldVal:ITerm, inv_f:(ITerm, ITerm) => ITerm) =
        {if(oldVal == 0) {res} else {inv_f(res,oldVal)}}
    // Array pass-through instrumentation for stores. This allows ignoring
    // stores to outside the tracked range.
    val arrayPassThroughInstrumentation: RewriteRules.Result = {
      val instrConstraint = {
        newLo === oldLo &&& newHi === oldHi &&& newRes === oldRes &&&
        newZeroCnt === oldZeroCnt &&&
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
      val storeEmptySeq = (newLo === i) & (newHi === i + 1) & (newRes === o) &
                           (newZeroCnt === ite(o===0, 1, 0))
      val storeBelow = (newRes === exq.reduceOp(oldRes, o)) &
                        (newLo === i) & (newHi === oldHi) &
                         (newZeroCnt === ite(o===0,oldZeroCnt+1,oldZeroCnt))
      val storeAbove = (newRes === exq.reduceOp(oldRes, o)) &
        (newHi === i + 1 & newLo === oldLo)
      val storeInside = exq.invReduceOp match {
        case Some(f) =>
          newRes === zeroReduceOp(
            zeroInvReduceOp(oldRes, exq.arrayTheory.select(a1, i), f),
            o) &
          newLo === oldLo & newHi === oldHi &
          (newZeroCnt === ite(exq.arrayTheory.select(a1, i)===0, ite(o===0, oldZeroCnt, oldZeroCnt-1),
                            ite(o===0, oldZeroCnt+1, oldZeroCnt)))
        case _ => storeEmptySeq
      }
      val storeOutside = storeEmptySeq //(newLo === i) & (newHi === i + 1) & (newRes === o)
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
    val (oldZeroCnt, newZeroCnt) = (oldGhostTerms(GhZeroCnt), newGhostTerms(GhZeroCnt))

    val selectEmpty = (newLo === i) & (newHi === i + 1) &
      (newRes === o) & (newZeroCnt === ite(o===0, 1, 0))
    val selectBelow = (newRes === exq.reduceOp(oldRes, o)) &
                      (newLo === i) & (newHi === oldHi) &
                      (newZeroCnt === ite(o===0,oldZeroCnt+1,oldZeroCnt))
    val selectAbove = (newRes === exq.reduceOp(oldRes, o)) &
                      (newHi === i + 1 & newLo === oldLo)
    val selectInside = newRes === oldRes & newLo === oldLo & newHi === oldHi &
                      (newZeroCnt === oldZeroCnt)
    val selectOutside = selectEmpty

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
