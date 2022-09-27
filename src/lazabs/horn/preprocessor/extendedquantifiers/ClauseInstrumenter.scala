package lazabs.horn.preprocessor.extendedquantifiers

import ap.parser.IExpression.Predicate
import ap.parser._
import ap.types.SortedConstantTerm
import lazabs.horn.bottomup.HornClauses.Clause
import GhostVariableAdder._
import Util._
import ap.parser.IExpression._

abstract class
ClauseInstrumenter(extendedQuantifier  : ExtendedQuantifier) {
  protected def instrumentStore (storeInfo  : StoreInfo,
                                 bodyTerms  : GhostVariableTerms) : Seq[IFormula]
  protected def instrumentSelect(selectInfo : SelectInfo,
                                 bodyTerms  : GhostVariableTerms) : Seq[IFormula]
  protected def instrumentConst (constInfo  : ConstInfo,
                                 bodyTerms  : GhostVariableTerms) : Seq[IFormula]

  protected val arrayTheory = extendedQuantifier.arrayTheory
  protected val indexSort = arrayTheory.indexSorts.head  // todo: assuming 1-d array

  protected val (hlo, hhi, hres, harr) =
    (IConstant(new SortedConstantTerm("lo'", indexSort)),
      IConstant(new SortedConstantTerm("hi'", indexSort)),
      IConstant(new SortedConstantTerm("res'", arrayTheory.objSort)),
      IConstant(new SortedConstantTerm("arr'", arrayTheory.sort)))

  // returns all instrumentations of a clause
  def instrument (clause                 : Clause,
                  ghostVarInds           : Map[Predicate, Seq[GhostVariableInds]],
                  extendedQuantifierInfo : ExtendedQuantifierInfo) : Seq[Instrumentation] = {
    // todo: below code must be modified to track multiple ranges (with multiple ghost vars)
    val hInds = ghostVarInds(clause.head.pred).head
    val headTermMap : Map[Int, ITerm] = Map(
      hInds.lo -> hlo, hInds.hi -> hhi, hInds.res -> hres, hInds.arr -> harr)

    // returns instrumentations for body atom, EXCEPT the identity instrumentation
    def instrForBodyAtom(bAtom : IAtom) : Seq[Instrumentation] = {
      val GhostVariableInds(iblo, ibhi, ibres, ibarr) = ghostVarInds(bAtom.pred).head // todo: support multiple ghost var sets
      val bodyTerms = GhostVariableTerms(
        bAtom.args(iblo), bAtom.args(ibhi), bAtom.args(ibres), bAtom.args(ibarr))
      val conjuncts : Seq[IFormula] =
        LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)

      val instrumentationConstraints : Seq[IFormula] = {
        val relevantConjuncts =
          conjuncts filter (c => isSelect(c) || isConst(c) || isStore(c))
        if(relevantConjuncts.length > 1)
          throw new Exception("More than one conjunct found for instrumentation," +
            " are the clauses normalized?\n" + clause.toPrologString)
        relevantConjuncts.headOption match {
          case Some(c) if isSelect(c) =>
            instrumentSelect(extractSelectInfo(c), bodyTerms)
          case Some(c) if isStore(c) =>
            instrumentStore(extractStoreInfo(c), bodyTerms)
          case Some(c) if isConst(c) =>
            instrumentConst(extractConstInfo(c), bodyTerms)
          case None => Nil
        }
      }

      for(instrumentationConstraint <- instrumentationConstraints) yield
        Instrumentation(instrumentationConstraint, headTermMap)
    }

    // returns the identity instrumentation for a body atom
    def identityInstrumentation (bAtom : IAtom) = {
      val GhostVariableInds(iblo, ibhi, ibres, ibarr) = ghostVarInds(bAtom.pred).head // todo: support multiple ghost var sets
      val bodyTerms = GhostVariableTerms(
        bAtom.args(iblo), bAtom.args(ibhi), bAtom.args(ibres), bAtom.args(ibarr))
      val newConjunct =
        (harr === bodyTerms.arr) &&&
          (hlo === bodyTerms.lo) &&&
          (hhi === bodyTerms.hi) &&&
          (hres === bodyTerms.res)
      Instrumentation(newConjunct, headTermMap)
    }

    val instrsForBodyAtoms : Seq[Seq[Instrumentation]] =
      clause.body map instrForBodyAtom
    val identityInstrsForBodyAtoms : Seq[Instrumentation] =
      clause.body map identityInstrumentation
    // todo: are ghost terms of each atom initially distinct?
    instrsForBodyAtoms.reduceOption((instrs1, instrs2) =>
      Instrumentation.product(instrs1, instrs2)).getOrElse(Nil) ++ identityInstrsForBodyAtoms
  }
}

// A simple instrumenter that works for all extended quantifiers, but is very
// general and thus imprecise.
// todo: add ghost array assertions
class SimpleClauseInstrumenter(extendedQuantifier : ExtendedQuantifier)
  extends ClauseInstrumenter(extendedQuantifier) {
  override protected
  def instrumentStore(storeInfo : StoreInfo,
                      bodyTerms : GhostVariableTerms): Seq[IFormula] = {
    val StoreInfo(a1, a2, i, o, arrayTheory2) = storeInfo
    if(arrayTheory != arrayTheory2)
      Nil
    else {
      import extendedQuantifier._
      import bodyTerms._
      import arrayTheory2._
      val instrConstraint1 =
        (harr === a2) &&& ite(bodyTerms.lo === bodyTerms.hi,
          (hlo === i) & (hhi === i + 1) & (hres === o),
          ite((lo - 1 === i),
            (hres === reduceOp(res, o)) & (hlo === i) & hhi === hi,
            ite(hi === i,
              (hres === reduceOp(res, o)) & (hhi === i + 1 & hlo === lo),
              ite(lo <= i & hi > i,
                invReduceOp match {
                  case Some(f) => hres === reduceOp(f(res, select(a1, i)), o) & hlo === lo & hhi === hi
                  case _ => (hlo === i) & (hhi === i + 1) & (hres === o) //??? //TODO: Implement non-cancellative case
                },
                //hres === ifInsideBounds_help(o, arrayTheory.select(a1, i), bres) & hlo === blo & hhi === bhi, //relate to prev val
                (hlo === i) & (hhi === i + 1) & (hres === o))))) // outside bounds, reset
      Seq(instrConstraint1)
    }
  }

  override protected
  def instrumentSelect(selectInfo : SelectInfo,
                       bodyTerms : GhostVariableTerms): Seq[IFormula] = {
    val SelectInfo(a, i, o, arrayTheory2) = selectInfo
    if (arrayTheory != arrayTheory2)
      Nil
    else {
      import extendedQuantifier._
      import bodyTerms._
      val instrConstraint1 =
        (harr === a) &&& ite(lo === hi,
          (hlo === i) & (hhi === i + 1) & (hres === o),
          ite((lo - 1 === i),
            (hres === reduceOp(res, o)) & (hlo === i) & hhi === hi,
            ite(hi === i,
              (hres === reduceOp(res, o)) & (hhi === i + 1 & hlo === lo),
              ite(lo <= i & hi > i,
                hres === res & hlo === lo & hhi === hi, // no change within bounds
                (hlo === i) & (hhi === i + 1) & (hres === o))))) // outside bounds, reset
      Seq(instrConstraint1)
    }
  }

  // todo: instrument const operation
  override protected
  def instrumentConst(constInfo : ConstInfo,
                      bodyTerms : GhostVariableTerms): Seq[IFormula] = Nil
}