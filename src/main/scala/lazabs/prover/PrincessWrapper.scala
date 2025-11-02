/**
 * Copyright (c) 2011-2025 Hossein Hojjat and Philipp Ruemmer.
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

package lazabs.prover

import lazabs.ast.ASTree._
import lazabs.types._
import ap.basetypes._
import ap.basetypes.IdealInt._
import ap.parser._
import ap.parser.IExpression._
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Quantifier
import ap.theories._
import ap.theories.heaps.Heap
import ap.theories.nia.GroebnerMultiplication
import ap.theories.rationals.Rationals
import ap.types.MonoSortedIFunction

import scala.collection.mutable.LinkedHashMap

object PrincessWrapper {
  private val localWrapper =
    new scala.util.DynamicVariable[PrincessWrapper] (new PrincessWrapper)

  def newWrapper : Unit =
    localWrapper.value = new PrincessWrapper

  def formula2Princess(
        ts: List[Expression],
        initialSymbolMap: LinkedHashMap[String, ConstantTerm] =
          LinkedHashMap[String, ConstantTerm]().empty,
        keepReservoir: Boolean = false) 
       : (List[IExpression], LinkedHashMap[String, ConstantTerm]) =
    localWrapper.value.formula2Princess(ts, initialSymbolMap, keepReservoir)

  def formula2Eldarica(t: IFormula,
                       symMap : Map[ConstantTerm, String],
                       removeVersions: Boolean): Expression =
    localWrapper.value.formula2Eldarica(t, symMap, removeVersions)

  def pathInterpols(fs: List[Expression]): List[Expression] =
    localWrapper.value.pathInterpols(fs)

  def isSatisfiable(e: Expression): Option[Boolean] =
    localWrapper.value.isSatisfiable(e)

  def elimQuantifiers(e : Expression) : Expression =
    localWrapper.value.elimQuantifiers(e)

  def simplify(e : Expression) : Expression =
    localWrapper.value.simplify(e)

  def expr2Term(ex : IExpression) : ITerm = ex match {
    case t : ITerm       => t
    case IBoolLit(true)  => 0
    case IBoolLit(false) => 1
    case f : IFormula    => ite(f, 0, 1)
  }

  def expr2Formula(ex : IExpression) : IFormula = ex match {
    case f : IFormula           => f
    case IIntLit(IdealInt.ZERO) => true
    case IIntLit(IdealInt.ONE)  => false
    case ADT.BoolADT.True       => true
    case ADT.BoolADT.False      => false
    case t : ITerm              => eqZero(t)
  }

  def type2Sort(t : Type) : Sort = t match {
    case IntegerType()            => Sort.Integer
    case RationalType()           => Rationals.dom
    case BooleanType()            => Sort.MultipleValueBool
    case AdtType(s)               => s //??? sorts are in ADT.sorts
    case BVType(n)                => ModuloArithmetic.UnsignedBVSort(n)
    case ArrayType(index, obj)    => ExtArray(List(toNormalBool(type2Sort(index))),
                                              toNormalBool(type2Sort(obj))).sort
    case HeapType(h)              => h.HeapSort
    case HeapAddressType(h)       => h.AddressSort
    case HeapAddressRangeType(h)  => h.AddressRangeSort
    case HeapAllocResType(h)      => h.AllocResSort
    case HeapBatchAllocResType(h) => h.BatchAllocResSort
    case HeapAdtType(h, s)        => s
    case _ =>
      throw new Exception("Unhandled type: " + t)
  }

  private def toNormalBool(s : Sort) : Sort = s match {
    case Sort.MultipleValueBool => Sort.Bool
    case s => s
  }

  val IntT = IntegerType()
  val RatT = RationalType()
  val BoolT = BooleanType()

  def sort2Type(s : Sort) : Type = s match {
    case Sort.Integer =>
      IntT
    case Rationals.dom =>
      RatT
    case Sort.Bool | Sort.MultipleValueBool =>
      BoolT
    case s@Heap.HeapRelatedSort(h) => {
      s match {
        case h.HeapSort          => HeapType(h)
        case h.AddressSort       => HeapAddressType(h)
        case h.AddressRangeSort  => HeapAddressRangeType(h)
        case h.AllocResSort      => HeapAllocResType(h)
        case h.BatchAllocResSort => HeapBatchAllocResType(h)
        case s if h.userHeapSorts.contains(s) => HeapAdtType(h, s)
      }
    }
    case s : ADT.ADTProxySort =>
      AdtType(s) // ??? s.adtTheory is the ADT
    case ModuloArithmetic.UnsignedBVSort(n) =>
      BVType(n)
    case SimpleArray.ArraySort(1) =>
      ArrayType(IntT, IntT)
    case ExtArray.ArraySort(theory) if theory.indexSorts.size == 1 =>
      ArrayType(sort2Type(theory.indexSorts.head), sort2Type(theory.objSort))
    case Sort.Interval(_, _) =>
      IntT
    case _ =>
      throw new Exception("Unhandled sort: " + s)
  }

}

class PrincessWrapper {
  
  private val api = new PrincessAPI_v1
  import api._
  import PrincessWrapper.{type2Sort, sort2Type, IntT, RatT, BoolT}

  /**
   * converts a list of formulas in Eldarica format to a list of formulas in Princess format
   * returns both the formulas in Princess format and the symbols used in the formulas
   */
  def formula2Princess(ts: List[Expression],
                       initialSymbolMap: LinkedHashMap[String, ConstantTerm] =
                         LinkedHashMap[String, ConstantTerm]().empty,
                       keepReservoir: Boolean = false) 
    : (List[IExpression], LinkedHashMap[String, ConstantTerm]) = {
    val symbolMap = initialSymbolMap

    def f2p(ex: Expression): IExpression = ex match {
      case ArraySelect(ArrayWithType(array, t), ind) =>
        theoryForArrayType(t).select(f2pterm(array), f2pterm(ind))
      case ArrayUpdate(ArrayWithType(array, t), index, value) =>
        theoryForArrayType(t).store(f2pterm(array), f2pterm(index), f2pterm(value))
      case ex@ConstArray(value) =>
        theoryForArrayType(ex.stype).const(f2pterm(value))

/*      case ScArray(None, None) =>
        0
      case ScArray(Some(aName), _) =>
        f2p(aName)
      case ScArray(None, Some(len)) =>
        // let's just store the size of the array at index -1
        // is this needed at all anywhere?
        store(0, -1, f2pterm(len)) */

      // Theory of sets (not really supported anymore ...)
      case SetUnion(e1, e2) =>
        union(f2pterm(e1), f2pterm(e2))
      case SetIntersect(e1, e2) =>
        intersection(f2pterm(e1), f2pterm(e2))      
      case SetSubset(e1, e2) =>
        subsetof(f2pterm(e1), f2pterm(e2))
      case SetDifference(e1, e2) =>
        difference(f2pterm(e1), f2pterm(e2))
      case SetContains(e1, e2) =>
        in(f2pterm(e2), f2pterm(e1))  // note that Eldarica has "contains" and princess has "in". They are reverse
      case SetSize(e1) =>
        size(f2pterm(e1))
      case SetConst(elems) =>
        elems.map(x =>
        singleton(f2pterm(x))).foldLeft[ITerm](emptyset)((a,b) => union(a,b))
        
      case Universal(v: BinderVariable, qe: Expression) =>
        ISortedQuantified(Quantifier.ALL, type2Sort(v.stype), f2pformula(qe))
      case Existential(v: BinderVariable, qe: Expression) =>
        ISortedQuantified(Quantifier.EX, type2Sort(v.stype), f2pformula(qe))
      case Conjunction(e1, e2) =>
        f2pformula(e1) & f2pformula(e2)
      case Disjunction(e1, e2) =>
        f2pformula(e1) | f2pformula(e2)
      case LessThan(e1, e2) if areRational(e1, e2) =>
        Rationals.lt(f2pterm(e1), f2pterm(e2))
      case LessThan(e1, e2) =>
        f2pterm(e1) < f2pterm(e2)
      case LessThanEqual(e1, e2) if areRational(e1, e2) =>
        Rationals.leq(f2pterm(e1), f2pterm(e2))
      case LessThanEqual(e1, e2) =>
        f2pterm(e1) <= f2pterm(e2)
      case GreaterThan(e1, e2) if areRational(e1, e2) =>
        Rationals.lt(f2pterm(e2), f2pterm(e1))
      case GreaterThan(e1, e2) =>
        f2pterm(e1) > f2pterm(e2)
      case GreaterThanEqual(e1, e2) if areRational(e1, e2) =>
        Rationals.leq(f2pterm(e2), f2pterm(e1))
      case GreaterThanEqual(e1, e2) =>
        f2pterm(e1) >= f2pterm(e2)
      case Addition(e1,e2)
        if (e1.stype == SetType(IntT) && e2.stype == IntT) =>
        union(f2pterm(e1), singleton(f2pterm(e2)))
      case Addition(e1,e2) if areRational(e1, e2) =>
        Rationals.plus(f2pterm(e1), f2pterm(e2))
      case Addition(e1,e2) =>
        f2pterm(e1) + f2pterm(e2)
      case Minus(e) if areRational(e) =>
        Rationals.minus(f2pterm(e))
      case Minus(e) =>
        -f2pterm(e)    
      case Subtraction(e1,e2) if areRational(e1, e2) =>
        Rationals.minus(f2pterm(e1), f2pterm(e2))
      case Subtraction(e1,e2) =>
        f2pterm(e1) - f2pterm(e2)
      case Multiplication(ToRational(e1),e2) if areRational(e2) =>
        Rationals.times(f2pterm(e1), f2pterm(e2))
      case Multiplication(Division(ToRational(e1), ToRational(e2)), e3) if areRational(e2) =>
        Rationals.multWithFraction(f2pterm(e1), f2pterm(e2), f2pterm(e3))
      case Multiplication(e1,e2) if areRational(e1, e2) =>
        Rationals.mul(f2pterm(e1), f2pterm(e2))
      case Multiplication(e1,e2) =>
        GroebnerMultiplication.mult(f2pterm(e1), f2pterm(e2))
      case Division(e1,e2) if areRational(e1, e2) =>
        Rationals.div(f2pterm(e1), f2pterm(e2))
      case Division(e1,e2) =>
        div(f2pterm(e1), f2pterm(e2))
      case Modulo(e1,e2) =>
        mod(f2pterm(e1), f2pterm(e2))

      case ToRational(e) =>
        Rationals.int2ring(f2pterm(e))

      case Not(e) =>
        !f2pformula(e)
      case Inequality(e1, e2) =>
        f2p(Not(Equality(e1, e2)))
      case Equality(e1, ScSet(None)) =>
        size(f2pterm(e1)) === 0
      case Equality(ScSet(None), e1) =>
        isEmpty(f2pterm(e1))
      case Equality(e1, e2) =>
        e1.stype match {
          case BooleanType() =>
            f2pformula(e1) <=> f2pformula(e2)
          case SetType(_) =>        
            setEqual(f2pterm(e1), f2pterm(e2))
          case _ =>
            f2pterm(e1) === f2pterm(e2)
        }
      case s@Variable(vname,None) =>
        symbolMap.getOrElseUpdate(vname, {
          type2Sort(s.stype) newConstant vname
        })

      // ADT conversion to Princess
      case ADTctor(adt, ctorName, exprList) => {
        val Some(ctor) = adt.constructors.find(_.name == ctorName)
        val termArgs = exprList.map(f2pterm(_))
        ctor(termArgs : _*)
      }
      case ADTsel(adt, selName, exprList) => {
        val Some(sel) = adt.selectors.flatten.find(_.name == selName)
        val termArgs = exprList.map(f2pterm(_))
        sel(termArgs : _*)
      }
      case e1@ADTtest(adt, sortNum, v) =>
        adt.ctorIds(sortNum)(f2pterm(v))
      case e2@ADTsize(adt, sortNum, v) =>
        adt.termSize(sortNum)(f2pterm(v))

      // Heap theory
      
      case HeapFun(heap, fun, exprList) =>
        val termArgs = exprList.map(f2pterm(_))
        fun(termArgs : _*)

      case HeapPred(heap, pred, exprList) =>
        val termArgs = exprList.map(f2pterm(_))
        pred(termArgs : _*)

      // Bit-vectors

      case BVconst(bits, value) =>
        ModuloArithmetic.bv(bits, IdealInt(value.bigInteger))

      case BinaryExpression(left, BVconcat(bits1, bits2), right) =>
        ModuloArithmetic.bv_concat(bits1, bits2, f2pterm(left), f2pterm(right))
      case UnaryExpression(BVextract(begin, end), arg) =>
        ModuloArithmetic.bv_extract(begin, end, f2pterm(arg))

      case UnaryExpression(BVnot(bits), arg) =>
        ModuloArithmetic.bv_not(bits, f2pterm(arg))
      case UnaryExpression(BVneg(bits), arg) =>
        ModuloArithmetic.bv_neg(bits, f2pterm(arg))

      case BinaryExpression(left, BVBinFun(fun, bits), right) =>
        fun(bits, f2pterm(left), f2pterm(right))

      case BinaryExpression(left, BVBinPred(pred, bits), right) =>
        pred(bits, f2pterm(left), f2pterm(right))
       
      case UnaryExpression(BV2Int(bits), arg) =>
        ModuloArithmetic.cast2SignedBV(bits, f2pterm(arg))
      case UnaryExpression(BV2Nat(bits), arg) =>
        ModuloArithmetic.cast2UnsignedBV(bits, f2pterm(arg))
      case UnaryExpression(Int2BV(bits), arg) =>
        ModuloArithmetic.cast2UnsignedBV(bits, f2pterm(arg))

      case Variable(vname,Some(i)) => IVariable(i)
      case NumericalConst(e) => IIntLit(ap.basetypes.IdealInt(e.bigInteger))
      case RationalConst(num, denom) =>
        Rationals.Fraction(IIntLit(ap.basetypes.IdealInt(num.bigInteger)),
                           IIntLit(ap.basetypes.IdealInt(denom.bigInteger)))
      case BoolConst(v) => IBoolLit(v)
      case ScSet(None) => emptyset
      case _ =>
        println("Error in conversion from Eldarica to Princess: " + ex)
        IBoolLit(false)
    }

    import PrincessWrapper.{expr2Formula, expr2Term}

    def f2pterm(ex: Expression): ITerm = expr2Term(f2p(ex))

    def f2pformula(ex: Expression): IFormula = expr2Formula(f2p(ex))

    val res = ts.map(f2p)
    (res,symbolMap)
  }

  private def areRational(e : Expression*) : Boolean =
    e.forall(t => t.stype == RatT)

  private object BVBinFun {
    def unapply(op : BinaryOperator) : Option[(IFunction, Int)] = op match {
      case BVand(bits) => Some((ModuloArithmetic.bv_and, bits))
      case BVor(bits)  => Some((ModuloArithmetic.bv_or, bits))
      case BVadd(bits) => Some((ModuloArithmetic.bv_add, bits))
      case BVsub(bits) => Some((ModuloArithmetic.bv_sub, bits))
      case BVmul(bits) => Some((ModuloArithmetic.bv_mul, bits))
      case BVudiv(bits)=> Some((ModuloArithmetic.bv_udiv, bits))
      case BVsdiv(bits)=> Some((ModuloArithmetic.bv_sdiv, bits))
      case BVurem(bits)=> Some((ModuloArithmetic.bv_urem, bits))
      case BVsrem(bits)=> Some((ModuloArithmetic.bv_srem, bits))
      case BVsmod(bits)=> Some((ModuloArithmetic.bv_smod, bits))
      case BVshl(bits) => Some((ModuloArithmetic.bv_shl, bits))
      case BVlshr(bits)=> Some((ModuloArithmetic.bv_lshr, bits))
      case BVashr(bits)=> Some((ModuloArithmetic.bv_ashr, bits))
      case BVxor(bits) => Some((ModuloArithmetic.bv_xor, bits))
      case BVxnor(bits)=> Some((ModuloArithmetic.bv_xnor, bits))
      case BVcomp(bits)=> Some((ModuloArithmetic.bv_comp, bits))
      case _           => None
    }
  }
  
  private object BVBinPred {
    def unapply(op : BinaryOperator)
                 : Option[(IExpression.Predicate, Int)] = op match {
      case BVult(bits) => Some((ModuloArithmetic.bv_ult, bits))
      case BVule(bits) => Some((ModuloArithmetic.bv_ule, bits))
      case BVslt(bits) => Some((ModuloArithmetic.bv_slt, bits))
      case BVsle(bits) => Some((ModuloArithmetic.bv_sle, bits))
      case _           => None
    }
  }

  private object ArrayWithType {
    def unapply(expr : Expression) : Option[(Expression, Type)] =
      expr.stype match {
        case t : ArrayType => Some((expr, t))
        case _ => None
      }
  }

  private def theoryForArrayType(t : Type) : ExtArray = t match {
    case t : ArrayType =>
      type2Sort(t).asInstanceOf[ExtArray.ArraySort].theory
    case _ =>
      throw new Exception ("" + t + " is not an array type")
  }
  
  
  /**
   * converts a formula in Princess format to a formula in Eldarica format
   * @param removeVersions Removes the versions in the SSA conversion 
   */
  def formula2Eldarica(t: IFormula,
                       symMap : Map[ConstantTerm, String],
                       removeVersions: Boolean): Expression = {
    import Sort.:::
    def rvT(t: ITerm): Expression = t match {
      case IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2)) =>
        Subtraction(rvT(e1).stype(IntT), rvT(e2).stype(IntT)).stype(IntT)
      case IPlus(ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2), e1) =>
        Subtraction(rvT(e1).stype(IntT), rvT(e2).stype(IntT)).stype(IntT)
      case IPlus(e1,e2) => Addition(rvT(e1).stype(IntT), rvT(e2).stype(IntT)).stype(IntT)
      case ITimes(e1,e2) => Multiplication(rvT(e1).stype(IntT), rvT(e2).stype(IntT)).stype(IntT)

      // Theory of sets (not really supported anymore ...)
      case IFunApp(`size`, arg) =>
        SetSize(rvT(arg.head).stype(SetType(IntT)))
      case IFunApp(`singleton`, Seq(e)) =>
        SetAdd(ScSet(None).stype(SetType(IntT)),rvT(e).stype(IntT))
      case IFunApp(`difference`, Seq(e0,e1)) =>
        SetDifference(rvT(e0).stype(SetType(IntT)),rvT(e1).stype(SetType(IntT)))
      case IFunApp(`union`, Seq(e0,e1)) =>
        SetUnion(rvT(e0).stype(SetType(IntT)),rvT(e1).stype(SetType(IntT)))
      case IFunApp(`intersection`, Seq(e0,e1)) =>
        SetIntersect(rvT(e0).stype(SetType(IntT)),rvT(e1).stype(SetType(IntT)))
      case IConstant(`emptyset`) =>
        ScSet(None).stype(SetType(IntT))

      // Multiplication
      case IFunApp(MulTheory.Mul(), Seq(e1, e2)) =>
        Multiplication(rvT(e1).stype(IntT), rvT(e2).stype(IntT)).stype(IntT)

      // Booleans
      case ADT.BoolADT.True =>
        BoolConst(true)
      case ADT.BoolADT.False =>
        BoolConst(false)

      // Rationals
      case Rationals.Fraction(IIntLit(e1), IIntLit(e2)) =>
        RationalConst(e1.bigIntValue, e2.bigIntValue)
      case IFunApp(Rationals.addition, Seq(e1, e2)) =>
        Addition(rvT(e1).stype(RatT),
                 rvT(e2).stype(RatT)).stype(RatT)
      case IFunApp(Rationals.multiplication, Seq(e1, e2)) =>
        Multiplication(rvT(e1).stype(RatT),
                       rvT(e2).stype(RatT)).stype(RatT)
      case IFunApp(Rationals.division, Seq(e1, e2)) =>
        Division(rvT(e1).stype(RatT),
                 rvT(e2).stype(RatT)).stype(RatT)
      case IFunApp(Rationals.multWithRing, Seq(e1, e2)) =>
        Multiplication(ToRational(rvT(e1).stype(IntT)).stype(RatT),
                       rvT(e2).stype(RatT)).stype(RatT)
      case IFunApp(Rationals.multWithFraction, Seq(e1, e2, e3)) =>
        Multiplication(
          Division(ToRational(rvT(e1).stype(IntT)).stype(RatT),
                   ToRational(rvT(e2).stype(IntT)).stype(RatT)),
          rvT(e3).stype(RatT)).stype(RatT)

      // Unary arrays of integers
      case IFunApp(SimpleArray.Select(), Seq(ar, ind)) =>
        ArraySelect(rvT(ar), rvT(ind).stype(IntT)).stype(IntT)
      case IFunApp(SimpleArray.Store(), Seq(ar, ind, value)) =>
        ArrayUpdate(rvT(ar), rvT(ind).stype(IntT),
                    rvT(value).stype(IntT)).stype(ArrayType(IntT, IntT))

      // Unary arrays
      case IFunApp(ExtArray.Select(theory), Seq(ar, ind)) =>
        ArraySelect(
          rvT(ar).stype(sort2Type(theory.sort)),
          rvT(ind)).stype(sort2Type(theory.objSort))
      case IFunApp(ExtArray.Store(theory), Seq(ar, ind, value)) =>
        ArrayUpdate(
          rvT(ar).stype(sort2Type(theory.sort)),
          rvT(ind).stype(sort2Type(theory.indexSorts.head)),
          rvT(value).stype(sort2Type(theory.objSort))).stype(sort2Type(theory.sort))
      case IFunApp(ExtArray.Const(theory), Seq(value)) =>
        ConstArray(rvT(value)).stype(sort2Type(theory.sort))

      // Theory of heap
      case IFunApp(f@Heap.HeapRelatedFunction(h), e) ::: s => {
        HeapFun(h, f, e.map(rvT(_)))
      }

      // General ADTs
      case IFunApp(ADT.TermSize(adt, sortNum), Seq(e)) =>
        ADTsize(adt, sortNum, rvT(e))
      case IFunApp(f@ADT.Constructor(adt, _), e) =>
        ADTctor(adt, f.name, e.map(rvT(_)))
      case IFunApp(f@ADT.Selector(adt, _, _), Seq(e)) =>
        ADTsel(adt, f.name, Seq(rvT(e))).stype(IntT)
      case IFunApp(f@ADT.CtorId(adt, sortNum), Seq(e)) =>
        ADTtest(adt, sortNum, rvT(e))

      // Bit-vectors

      case IFunApp(ModuloArithmetic.mod_cast,
                   Seq(IIntLit(IdealInt.ZERO),
                       IIntLit(upper), IIntLit(value))) => {
        val ModuloArithmetic.UnsignedBVSort(bits) =
          ModuloArithmetic.ModSort(IdealInt.ZERO, upper)
        BVconst(bits, value.bigIntValue).stype(BVType(bits))
      }

      // A sequence encoding sign_extend
      case IFunApp(ModuloArithmetic.mod_cast,
                   Seq(IIntLit(IdealInt.ZERO), IIntLit(upper),
                       IFunApp(ModuloArithmetic.mod_cast,
                               Seq(IIntLit(lower2), IIntLit(upper2),
                                   arg)))) => {
        val ModuloArithmetic.UnsignedBVSort(bits1) =
          ModuloArithmetic.ModSort(IdealInt.ZERO, upper)
        val ModuloArithmetic.SignedBVSort(bits2) =
          ModuloArithmetic.ModSort(lower2, upper2)
        UnaryExpression(Int2BV(bits1),
          UnaryExpression(BV2Int(bits2),
                          rvT(arg)).stype(IntT)).stype(BVType(bits1))
      }

      case IFunApp(ModuloArithmetic.mod_cast,
                   Seq(IIntLit(IdealInt.ZERO), IIntLit(upper), arg)) => {
        val ModuloArithmetic.UnsignedBVSort(bits) =
          ModuloArithmetic.ModSort(IdealInt.ZERO, upper)
        val argExpr = rvT(arg)
        argExpr.stype match {
          case IntegerType() =>
            UnaryExpression(Int2BV(bits), argExpr).stype(BVType(bits))
          case BVType(bits2) =>
            UnaryExpression(Int2BV(bits),
              UnaryExpression(BV2Nat(bits2),
                              argExpr).stype(IntT)).stype(BVType(bits))
          case t =>
            throw new Exception("Unhandled type: " + t)
        }
      }

      case IFunApp(ModuloArithmetic.mod_cast,
                   Seq(IIntLit(lower), IIntLit(upper), arg)) => {
        val ModuloArithmetic.SignedBVSort(bits) =
          ModuloArithmetic.ModSort(lower, upper)
        val argExpr = rvT(arg)
        argExpr.stype match {
          case BVType(_) =>
            UnaryExpression(BV2Int(bits), argExpr).stype(IntT)
          case t =>
            throw new Exception("Unhandled type: " + t)
        }
      }

      case IFunApp(ModuloArithmetic.int_cast, Seq(arg)) => {
        val sub = rvT(arg)
        sub.stype match {
          case BVType(bits) =>
            UnaryExpression(BV2Nat(bits), sub).stype(IntT)
          case IntegerType() =>
            sub
          case t =>
            throw new Exception("Unhandled type: " + t)
        }
      }

      case IFunApp(fun, Seq(IIntLit(IdealInt(bits)), left, right))
             if fun2BVBinOp contains fun => {
        val (op, typ) = fun2BVBinOp(fun)(bits)
        BinaryExpression(rvT(left), op, rvT(right)).stype(typ)
      }

      case IFunApp(ModuloArithmetic.bv_comp,
                   Seq(IIntLit(IdealInt(bits)), left, right)) =>
        BinaryExpression(rvT(left), BVcomp(bits), rvT(right)).stype(BVType(1))

      case IFunApp(ModuloArithmetic.bv_concat,
                   Seq(IIntLit(IdealInt(bits1)), IIntLit(IdealInt(bits2)),
                       left, right)) =>
        BinaryExpression(rvT(left), BVconcat(bits1, bits2),
                         rvT(right)).stype(BVType(bits1 + bits2))

      case IFunApp(ModuloArithmetic.bv_extract,
                   Seq(IIntLit(IdealInt(begin)),
                       IIntLit(IdealInt(end)),
                       arg)) =>
        UnaryExpression(BVextract(begin, end),
                        rvT(arg)).stype(BVType(begin - end + 1))

      case IFunApp(ModuloArithmetic.bv_not,
                   Seq(IIntLit(IdealInt(bits)), arg)) =>
        UnaryExpression(BVnot(bits), rvT(arg)).stype(BVType(bits))

      case IFunApp(ModuloArithmetic.bv_neg,
                   Seq(IIntLit(IdealInt(bits)), arg)) =>
        UnaryExpression(BVneg(bits), rvT(arg)).stype(BVType(bits))

      // Constants and variables

      case IConstant(cterm) ::: sort => {
        val pattern = """x(\d+)(\w+)""".r
        symMap(cterm) match {
          case pattern(cVersion,n) if (removeVersions) =>
            Variable(n,None).stype(sort2Type(sort))
          case noVersion@_ =>
            Variable(noVersion,None).stype(sort2Type(sort))
        }
      }
      case IVariable(index) =>
        Variable("_" + index,Some(index)).stype(IntT)      
      case IIntLit(value) =>
        NumericalConst(value.bigIntValue).stype(IntT)
      case Rationals.Fraction(IIntLit(num), IIntLit(denom)) =>
        RationalConst(num.bigIntValue, denom.bigIntValue).stype(RatT)
      case _ =>
        println("Error in conversion from Princess to Eldarica (ITerm): " + t + " subclass of " + t.getClass)
        BoolConst(false)
    }
    
    val Var0Eq = SymbolEquation(IVariable(0))
    def rvF(t: IFormula): Expression = t match {

      // Set constraints (not used currently)

      case IIntFormula(IIntRelation.EqZero, IPlus(IFunApp(`difference`, Seq(left, right)), ITimes(IdealInt.MINUS_ONE, `emptyset`))) =>
        SetSubset(rvT(left).stype(SetType(IntT)),
          rvT(right).stype(SetType(IntT)))
      case IIntFormula(IIntRelation.EqZero, IFunApp(`size`, Seq(e))) =>
        Equality(rvT(e).stype(SetType(IntT)),ScSet(None).stype(SetType(IntT)))      
      case IIntFormula(IIntRelation.EqZero, IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, `emptyset`))) =>
        Equality(rvT(e1).stype(SetType(IntT)),ScSet(None).stype(SetType(IntT)))
      case INot(IIntFormula(IIntRelation.EqZero, IPlus(ap.parser.IIntLit(ap.basetypes.IdealInt.MINUS_ONE), 
          IFunApp(`size`, Seq(IFunApp(`difference`, Seq(IFunApp(`singleton`, Seq(e1)), e2))))))) =>
        SetContains(rvT(e2).stype(SetType(IntT)),rvT(e1).stype(IntT))
      //case IIntFormula(IIntRelation.EqZero, IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2))) =>
        //Equality(rvT(e1).stype(SetType(IntT)),rvT(e2).stype(SetType(IntT)))

      // Equality constraints

      case EqZ(e ::: (Sort.Bool | Sort.MultipleValueBool)) =>
        rvT(e).stype(BoolT)

      case EqLit(e ::: (Sort.Bool | Sort.MultipleValueBool),
                 IdealInt.ZERO) =>
        rvT(e).stype(BoolT)
      case EqLit(e ::: (Sort.Bool | Sort.MultipleValueBool),
                 IdealInt.ONE) =>
        Not(rvT(e).stype(BoolT))

      case Eq(e1, e2) =>
        Equality(rvT(e1), rvT(e2))

      // Inequality constraints

      case Geq(e1 : IIntLit, e2) =>
        LessThanEqual(rvT(e2).stype(IntT), rvT(e1).stype(IntT))
      case Geq(e1, e2) =>
        GreaterThanEqual(rvT(e1).stype(IntT), rvT(e2).stype(IntT))

      case IBinFormula(IBinJunctor.And, e1, e2) =>
        Conjunction(rvF(e1).stype(BoolT),
                    rvF(e2).stype(BoolT))
      case IBinFormula(IBinJunctor.Or, e1, e2) =>
        Disjunction(rvF(e1).stype(BoolT),
                    rvF(e2).stype(BoolT))
      case IBinFormula(IBinJunctor.Eqv, e1, e2) =>
        Iff(rvF(e1).stype(BoolT),
            rvF(e2).stype(BoolT))
      
       // EX (varCoeff * _0 = remainder)
      case ISortedQuantified(Quantifier.EX,
                             Sort.Integer, Var0Eq(varCoeff, remainder)) =>
       Equality(
         Modulo(rvT(shiftVars(remainder, 1, -1)).stype(IntT),
                                  rvT(varCoeff.abs).stype(IntT)),
         NumericalConst(0)).stype(BoolT)
      case ISortedQuantified(Quantifier.EX, s, e) =>
        Existential(BinderVariable("i").stype(sort2Type(s)), rvF(e).stype(BoolT))
      case ISortedQuantified(Quantifier.ALL, s, e) =>
        Universal(BinderVariable("i").stype(sort2Type(s)), rvF(e).stype(BoolT))
      case INot(e) => Not(rvF(e).stype(BoolT))
      case IBoolLit(b) => BoolConst(b)

      // Heap theory
      case IAtom(pred@Heap.HeapRelatedPredicate(h), e) =>
        HeapPred(h, pred, e.map(rvT(_)))

      // Rationals
      case IAtom(Rationals.lessThan, Seq(e1, e2)) =>
        LessThan(rvT(e1).stype(RatT), rvT(e2).stype(RatT))
      case IAtom(Rationals.lessThanOrEqual, Seq(e1, e2)) =>
        LessThanEqual(rvT(e1).stype(RatT), rvT(e2).stype(RatT))

      // Bit-vectors
      case IAtom(pred, Seq(IIntLit(IdealInt(bits)), left, right))
             if pred2BVBinOp contains pred =>
        BinaryExpression(rvT(left), pred2BVBinOp(pred)(bits),
                         rvT(right)).stype(BoolT)

      case _ =>
        println("Error in conversion from Princess to Eldarica (IFormula): " + t + " subclass of " + t.getClass)
        BoolConst(false)
    }
    rvF(t)
  }

  private val fun2BVBinOp : Map[IFunction, Int => (BinaryOperator, Type)] =
    Map(
      ModuloArithmetic.bv_and -> ((bits:Int) => (BVand(bits), BVType(bits))),
      ModuloArithmetic.bv_or  -> ((bits:Int) => (BVor(bits), BVType(bits))),
      ModuloArithmetic.bv_add -> ((bits:Int) => (BVadd(bits), BVType(bits))),
      ModuloArithmetic.bv_sub -> ((bits:Int) => (BVsub(bits), BVType(bits))),
      ModuloArithmetic.bv_mul -> ((bits:Int) => (BVmul(bits), BVType(bits))),
      ModuloArithmetic.bv_udiv-> ((bits:Int) => (BVudiv(bits), BVType(bits))),
      ModuloArithmetic.bv_sdiv-> ((bits:Int) => (BVsdiv(bits), BVType(bits))),
      ModuloArithmetic.bv_urem-> ((bits:Int) => (BVurem(bits), BVType(bits))),
      ModuloArithmetic.bv_srem-> ((bits:Int) => (BVsrem(bits), BVType(bits))),
      ModuloArithmetic.bv_smod-> ((bits:Int) => (BVsmod(bits), BVType(bits))),
      ModuloArithmetic.bv_shl -> ((bits:Int) => (BVshl(bits), BVType(bits))),
      ModuloArithmetic.bv_lshr-> ((bits:Int) => (BVlshr(bits), BVType(bits))),
      ModuloArithmetic.bv_ashr-> ((bits:Int) => (BVashr(bits), BVType(bits))),
      ModuloArithmetic.bv_xor -> ((bits:Int) => (BVxor(bits), BVType(bits))),
      ModuloArithmetic.bv_xnor-> ((bits:Int) => (BVxnor(bits), BVType(bits)))
    )

  private val pred2BVBinOp : Map[IExpression.Predicate, Int => BinaryOperator] =
    Map(
      ModuloArithmetic.bv_ult -> ((bits:Int) => BVult(bits)),
      ModuloArithmetic.bv_ule -> ((bits:Int) => BVule(bits)),
      ModuloArithmetic.bv_slt -> ((bits:Int) => BVslt(bits)),
      ModuloArithmetic.bv_sle -> ((bits:Int) => BVsle(bits))
    )

  // PartNames used in interpolation queries
  private def partNameStream(num : Int) : Stream[PartName] =
    Stream.cons(new PartName("part" + num), partNameStream(num + 1))
  private val globalPartNames = partNameStream(0)
  
  def pathInterpols(fs: List[Expression]): List[Expression] = {
    Prover.increaseInterpolationConsultation
    var (formulas,symbolMap) = formula2Princess(fs)
    val partNames = (globalPartNames take formulas.size).toList
    val path = formulas.zip(partNames).map(fn => INamedPart(fn._2, fn._1.asInstanceOf[IFormula]))
    val partitions : List[IInterpolantSpec] = (1 until partNames.size).map(i => (partNames.splitAt(i))).map(x => IInterpolantSpec(x._1,x._2)).toList
    val interpolants = interpolate(path.reduceLeft[IFormula](_&_),symbolMap.values.toSeq,partitions) match {
      case None =>
        println("No interpolants found")
        lazabs.art.RTreeMethods.stopTimer
        List()
      case Some(is) => is
    }
    val reverseSymMap = (for ((k, v) <- symbolMap.iterator) yield (v -> k)).toMap
    interpolants.map((formula2Eldarica(_, reverseSymMap, true)))
  }
  
  /**
   * inputs a formula and determines if it is satisfiable
   * @param e the input formula
   */
  def isSatisfiable(e: Expression): Option[Boolean] = {
    Prover.increaseTheoremProverConsultation
    val (formulas,symbolMap) = formula2Princess(List(e))
    //println("sat: " + formula.head)
    Some(isSat(formulas.head.asInstanceOf[IFormula], symbolMap.values.toSeq))
  }

  def elimQuantifiers(e : Expression) : Expression = {
    var (Seq(formula),symbolMap) = formula2Princess(List(e))
    //println("qe: " + formula)
    val rawRes = elimQuans(formula.asInstanceOf[IFormula], symbolMap.values.toSeq)
    val reverseSymMap = (for ((k, v) <- symbolMap.iterator) yield (v -> k)).toMap
    formula2Eldarica(rawRes, reverseSymMap, false)
  }

  def simplify(e : Expression) : Expression = {
    var (Seq(formula),symbolMap) = formula2Princess(List(e))
    //println("qe: " + formula)
    val rawRes = dnfSimplify(formula.asInstanceOf[IFormula], symbolMap.values.toSeq)
    val reverseSymMap = (for ((k, v) <- symbolMap.iterator) yield (v -> k)).toMap
    formula2Eldarica(rawRes, reverseSymMap, false)
  }

}
