/**
 * Copyright (c) 2011-2020 Hossein Hojjat and Philipp Ruemmer.
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
import ap.theories.nia.GroebnerMultiplication

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

  def reduceDeBruijn(e: Expression): Expression =
    localWrapper.value.reduceDeBruijn(e)

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
    case BooleanType()            => Sort.MultipleValueBool
    case AdtType(s)               => s //??? sorts are in ADT.sorts
    case BVType(n)                => ModuloArithmetic.UnsignedBVSort(n)
    case ArrayType(IntegerType()) => SimpleArray.ArraySort(1)
    case _ =>
      throw new Exception("Unhandled type: " + t)
  }

  def sort2Type(s : Sort) : Type = s match {
    case Sort.Integer =>
      IntegerType()
    case Sort.Bool | Sort.MultipleValueBool =>
      BooleanType()
    case s : ADT.ADTProxySort =>
      AdtType(s) // ??? s.adtTheory is the ADT
    case ModuloArithmetic.UnsignedBVSort(n) =>
      BVType(n)
    case SimpleArray.ArraySort(1) =>
      ArrayType(IntegerType())
    case _ =>
      throw new Exception("Unhandled sort: " + s)
  }

}

class PrincessWrapper {
  
  private val api = new PrincessAPI_v1
  import api._

  /**
   * converts a list of formulas in Eldarica format to a list of formulas in Princess format
   * returns both the formulas in Princess format and the symbols used in the formulas
   */
  def formula2Princess(ts: List[Expression],initialSymbolMap: LinkedHashMap[String, ConstantTerm] = LinkedHashMap[String, ConstantTerm]().empty, 
                       keepReservoir: Boolean = false) 
    : (List[IExpression], LinkedHashMap[String, ConstantTerm]) = {
    val symbolMap = initialSymbolMap

    def f2p(ex: Expression): IExpression = ex match {
      case lazabs.ast.ASTree.ArraySelect(array, ind) =>
        SimpleArray(1).select(f2pterm(array), f2pterm(ind))
      case ArrayUpdate(array, index, value) =>
        SimpleArray(1).store(f2pterm(array), f2pterm(index), f2pterm(value))

/*      case ScArray(None, None) =>
        0
      case ScArray(Some(aName), _) =>
        f2p(aName)
      case ScArray(None, Some(len)) =>
        // let's just store the size of the array at index -1
        // is this needed at all anywhere?
        store(0, -1, f2pterm(len)) */

      // Theory of sets (not really supported anymore ...)
      case lazabs.ast.ASTree.SetUnion(e1, e2) =>
        union(f2pterm(e1), f2pterm(e2))
      case lazabs.ast.ASTree.SetIntersect(e1, e2) =>
        intersection(f2pterm(e1), f2pterm(e2))      
      case lazabs.ast.ASTree.SetSubset(e1, e2) =>
        subsetof(f2pterm(e1), f2pterm(e2))
      case lazabs.ast.ASTree.SetDifference(e1, e2) =>
        difference(f2pterm(e1), f2pterm(e2))
      case lazabs.ast.ASTree.SetContains(e1, e2) =>
        in(f2pterm(e2), f2pterm(e1))  // note that Eldarica has "contains" and princess has "in". They are reverse
      case lazabs.ast.ASTree.SetSize(e1) =>
        size(f2pterm(e1))
      case lazabs.ast.ASTree.SetConst(elems) =>
        elems.map(x =>
        singleton(f2pterm(x))).foldLeft[ITerm](emptyset)((a,b) => union(a,b))
        
      case lazabs.ast.ASTree.Universal(v: BinderVariable, qe: Expression) =>
        IQuantified(Quantifier.ALL, f2pformula(qe))
      case lazabs.ast.ASTree.Existential(v: BinderVariable, qe: Expression) =>
        IQuantified(Quantifier.EX, f2pformula(qe))
      case lazabs.ast.ASTree.Conjunction(e1, e2) =>
        f2pformula(e1) & f2pformula(e2)
      case lazabs.ast.ASTree.Disjunction(e1, e2) =>
        f2pformula(e1) | f2pformula(e2)
      case lazabs.ast.ASTree.LessThan(e1, e2) =>
        f2pterm(e1) < f2pterm(e2)
      case lazabs.ast.ASTree.LessThanEqual(e1, e2) =>
        f2pterm(e1) <= f2pterm(e2)
      case lazabs.ast.ASTree.GreaterThan(e1, e2) =>
        f2pterm(e1) > f2pterm(e2)
      case lazabs.ast.ASTree.GreaterThanEqual(e1, e2) =>
        f2pterm(e1) >= f2pterm(e2)
      case lazabs.ast.ASTree.Addition(e1,e2)
        if (e1.stype == SetType(IntegerType()) && e2.stype == IntegerType()) =>
        union(f2pterm(e1), singleton(f2pterm(e2)))
      case lazabs.ast.ASTree.Addition(e1,e2) =>
        f2pterm(e1) + f2pterm(e2)
      case lazabs.ast.ASTree.Minus(e) =>
        -f2pterm(e)    
      case lazabs.ast.ASTree.Subtraction(e1,e2) =>
        f2pterm(e1) - f2pterm(e2)
      case lazabs.ast.ASTree.Multiplication(e1,e2) =>
        GroebnerMultiplication.mult(f2pterm(e1), f2pterm(e2))
      case Division(e1,e2) =>
        div(f2pterm(e1), f2pterm(e2))
      case Modulo(e1,e2) =>
        mod(f2pterm(e1), f2pterm(e2))

      case lazabs.ast.ASTree.Not(e) =>
        !f2pformula(e)
      case lazabs.ast.ASTree.Inequality(e1, e2) =>
        f2p(lazabs.ast.ASTree.Not(lazabs.ast.ASTree.Equality(e1, e2)))
      case lazabs.ast.ASTree.Equality(e1, lazabs.ast.ASTree.ScSet(None)) =>
        size(f2pterm(e1)) === 0
      case lazabs.ast.ASTree.Equality(lazabs.ast.ASTree.ScSet(None), e1) =>
        isEmpty(f2pterm(e1))
      case lazabs.ast.ASTree.Equality(e1, e2) =>
        e1.stype match {
          case BooleanType() =>
            f2pformula(e1) <=> f2pformula(e2)
          case SetType(_) =>        
            setEqual(f2pterm(e1), f2pterm(e2))
          case _ =>
            f2pterm(e1) === f2pterm(e2)
        }
      case s@lazabs.ast.ASTree.Variable(vname,None) =>
        symbolMap.getOrElseUpdate(vname, {
          PrincessWrapper.type2Sort(s.stype) newConstant vname
        })

      // ADT conversion to Princess
      case lazabs.ast.ASTree.ADTctor(adt, ctorName, exprList) => {
        val Some(ctor) = adt.constructors.find(_.name == ctorName)
        val termArgs = exprList.map(f2pterm(_))
        ctor(termArgs : _*)
      }
      case lazabs.ast.ASTree.ADTsel(adt, selName, exprList) => {
        val Some(sel) = adt.selectors.flatten.find(_.name == selName)
        val termArgs = exprList.map(f2pterm(_))
        sel(termArgs : _*)
      }
      case e1@lazabs.ast.ASTree.ADTtest(adt, sortNum, v) =>
        adt.ctorIds(sortNum)(f2pterm(v))
      case e2@lazabs.ast.ASTree.ADTsize(adt, sortNum, v) =>
        adt.termSize(sortNum)(f2pterm(v))

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

      case lazabs.ast.ASTree.Variable(vname,Some(i)) => IVariable(i)
      case lazabs.ast.ASTree.NumericalConst(e) => IIntLit(ap.basetypes.IdealInt(e.bigInteger))
      case lazabs.ast.ASTree.BoolConst(v) => IBoolLit(v)
      case lazabs.ast.ASTree.ScSet(None) => emptyset
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
  
  /**
   * reduces all the debruijn indices by one
   */
  def reduceDeBruijn(e: Expression): Expression = e match {
    case Existential(bv, body) => Existential(bv, reduceDeBruijn(body))
    case Universal(bv, body) => Universal(bv, reduceDeBruijn(body))
    case BinaryExpression(e1, op, e2) => BinaryExpression(reduceDeBruijn(e1), op, reduceDeBruijn(e2)).stype(IntegerType())
    case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, reduceDeBruijn(e1), reduceDeBruijn(e2), reduceDeBruijn(e3)).stype(IntegerType())
    case UnaryExpression(op, e) => UnaryExpression(op, reduceDeBruijn(e)).stype(IntegerType())
    case v@Variable(name,Some(i)) => i match {
      case 0 => Variable(name,None).stype(IntegerType())
      case i => Variable("_" + (i-1),Some(i-1)).stype(IntegerType())
    }
    case _ => e
  }

  
  /**
   * converts a formula in Princess format to a formula in Eldarica format
   * @param removeVersions Removes the versions in the SSA conversion 
   */
  def formula2Eldarica(t: IFormula,
                       symMap : Map[ConstantTerm, String],
                       removeVersions: Boolean): Expression = {
    import Sort.:::
    import PrincessWrapper.sort2Type
    def rvT(t: ITerm): Expression = t match {
      case IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2)) =>
        lazabs.ast.ASTree.Subtraction(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case IPlus(ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2), e1) =>
        lazabs.ast.ASTree.Subtraction(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case IPlus(e1,e2) => lazabs.ast.ASTree.Addition(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case ITimes(e1,e2) => lazabs.ast.ASTree.Multiplication(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))

      // Theory of sets (not really supported anymore ...)
      case IFunApp(`size`, arg) =>
        lazabs.ast.ASTree.SetSize(rvT(arg.head).stype(SetType(IntegerType())))
      case IFunApp(`singleton`, Seq(e)) =>
        lazabs.ast.ASTree.SetAdd(lazabs.ast.ASTree.ScSet(None).stype(SetType(IntegerType())),rvT(e).stype(IntegerType()))
      case IFunApp(`difference`, Seq(e0,e1)) =>
        lazabs.ast.ASTree.SetDifference(rvT(e0).stype(SetType(IntegerType())),rvT(e1).stype(SetType(IntegerType())))
      case IFunApp(`union`, Seq(e0,e1)) =>
        lazabs.ast.ASTree.SetUnion(rvT(e0).stype(SetType(IntegerType())),rvT(e1).stype(SetType(IntegerType())))
      case IFunApp(`intersection`, Seq(e0,e1)) =>
        lazabs.ast.ASTree.SetIntersect(rvT(e0).stype(SetType(IntegerType())),rvT(e1).stype(SetType(IntegerType())))
      case IConstant(`emptyset`) =>
        lazabs.ast.ASTree.ScSet(None).stype(SetType(IntegerType()))

      // Multiplication
      case IFunApp(MulTheory.Mul(), Seq(e1, e2)) =>
        lazabs.ast.ASTree.Multiplication(rvT(e1).stype(IntegerType()),
                                         rvT(e2).stype(IntegerType()))

      // Booleans
      case ADT.BoolADT.True =>
        lazabs.ast.ASTree.BoolConst(true)
      case ADT.BoolADT.False =>
        lazabs.ast.ASTree.BoolConst(false)

      // Unary arrays of integers
      case IFunApp(SimpleArray.Select(), Seq(ar, ind)) =>
        lazabs.ast.ASTree.ArraySelect(
          rvT(ar),
          rvT(ind).stype(IntegerType())).stype(IntegerType())
      case IFunApp(SimpleArray.Store(), Seq(ar, ind, value)) =>
        lazabs.ast.ASTree.ArrayUpdate(
          rvT(ar),
          rvT(ind).stype(IntegerType()),
          rvT(value).stype(IntegerType())).stype(ArrayType(IntegerType()))

      // General ADTs
      case IFunApp(ADT.TermSize(adt, sortNum), Seq(e)) =>
        ADTsize(adt, sortNum, rvT(e))
      case IFunApp(f@ADT.Constructor(adt, _), e) =>
        ADTctor(adt, f.name, e.map(rvT(_)))
      case IFunApp(f@ADT.Selector(adt, _, _), Seq(e)) =>
        ADTsel(adt, f.name, Seq(rvT(e))).stype(IntegerType())
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
                          rvT(arg)).stype(IntegerType())).stype(BVType(bits1))
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
                              argExpr).stype(IntegerType())).stype(BVType(bits))
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

      case IConstant(cterm) ::: sort =>
        val pattern = """x(\d+)(\w+)""".r
        symMap(cterm) match {
          case pattern(cVersion,n) if (removeVersions) =>
            lazabs.ast.ASTree.Variable(n,None).stype(sort2Type(sort))
          case noVersion@_ =>
            lazabs.ast.ASTree.Variable(noVersion,None).stype(sort2Type(sort))
        }
      case IVariable(index) =>
        lazabs.ast.ASTree.Variable("_" + index,Some(index)).stype(IntegerType())      
      case IIntLit(value) => lazabs.ast.ASTree.NumericalConst(value.bigIntValue)
      case _ =>
        println("Error in conversion from Princess to Eldarica (ITerm): " + t + " sublcass of " + t.getClass)
        BoolConst(false)
    }
    
    val Var0Extractor = SymbolSum(IVariable(0))
    def rvF(t: IFormula): Expression = t match {

      // Set constraints (not used currently)

      case IIntFormula(IIntRelation.EqZero, IPlus(IFunApp(`difference`, Seq(left, right)), ITimes(IdealInt.MINUS_ONE, `emptyset`))) =>
        lazabs.ast.ASTree.SetSubset(rvT(left).stype(SetType(IntegerType())),
          rvT(right).stype(SetType(IntegerType())))
      case IIntFormula(IIntRelation.EqZero, IFunApp(`size`, Seq(e))) =>
        lazabs.ast.ASTree.Equality(rvT(e).stype(SetType(IntegerType())),lazabs.ast.ASTree.ScSet(None).stype(SetType(IntegerType())))      
      case IIntFormula(IIntRelation.EqZero, IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, `emptyset`))) =>
        lazabs.ast.ASTree.Equality(rvT(e1).stype(SetType(IntegerType())),lazabs.ast.ASTree.ScSet(None).stype(SetType(IntegerType())))
      case INot(IIntFormula(IIntRelation.EqZero, IPlus(ap.parser.IIntLit(ap.basetypes.IdealInt.MINUS_ONE), 
          IFunApp(`size`, Seq(IFunApp(`difference`, Seq(IFunApp(`singleton`, Seq(e1)), e2))))))) =>
        lazabs.ast.ASTree.SetContains(rvT(e2).stype(SetType(IntegerType())),rvT(e1).stype(IntegerType()))
      //case IIntFormula(IIntRelation.EqZero, IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2))) =>
        //lazabs.ast.ASTree.Equality(rvT(e1).stype(SetType(IntegerType())),rvT(e2).stype(SetType(IntegerType())))

      // Equality constraints

      case EqZ(e ::: (Sort.Bool | Sort.MultipleValueBool)) =>
        rvT(e).stype(BooleanType())

      case EqLit(e ::: (Sort.Bool | Sort.MultipleValueBool),
                 IdealInt.ZERO) =>
        rvT(e).stype(BooleanType())
      case EqLit(e ::: (Sort.Bool | Sort.MultipleValueBool),
                 IdealInt.ONE) =>
        lazabs.ast.ASTree.Not(rvT(e).stype(BooleanType()))

      case Eq(e1, e2) =>
        lazabs.ast.ASTree.Equality(rvT(e1), rvT(e2))

      // Inequality constraints

      case Geq(e1 : IIntLit, e2) =>
        lazabs.ast.ASTree.LessThanEqual(rvT(e2).stype(IntegerType()),
                                        rvT(e1).stype(IntegerType()))
      case Geq(e1, e2) =>
        lazabs.ast.ASTree.GreaterThanEqual(rvT(e1).stype(IntegerType()),
                                           rvT(e2).stype(IntegerType()))

      case IBinFormula(IBinJunctor.And, e1, e2) =>
        lazabs.ast.ASTree.Conjunction(rvF(e1).stype(BooleanType()),
                                      rvF(e2).stype(BooleanType()))
      case IBinFormula(IBinJunctor.Or, e1, e2) =>
        lazabs.ast.ASTree.Disjunction(rvF(e1).stype(BooleanType()),
                                      rvF(e2).stype(BooleanType()))
      case IBinFormula(IBinJunctor.Eqv, e1, e2) =>
        lazabs.ast.ASTree.Iff(rvF(e1).stype(BooleanType()),
                              rvF(e2).stype(BooleanType()))
      
      case IQuantified(Quantifier.EX,IIntFormula(IIntRelation.EqZero,Var0Extractor(varCoeff, remainder))) => // EX (varCoeff * _0 + remainder = 0)
       lazabs.ast.ASTree.Equality(lazabs.ast.ASTree.Modulo(reduceDeBruijn(rvT(remainder)).stype(IntegerType()),rvT(varCoeff).stype(IntegerType())),NumericalConst(0)).stype(BooleanType())
      case IQuantified(Quantifier.EX, e) =>
        lazabs.ast.ASTree.Existential(BinderVariable("i").stype(IntegerType()), rvF(e).stype(BooleanType()))
      case IQuantified(Quantifier.ALL, e) => lazabs.ast.ASTree.Universal(BinderVariable("i").stype(IntegerType()), rvF(e).stype(BooleanType()))
      case INot(e) => lazabs.ast.ASTree.Not(rvF(e).stype(BooleanType()))
      case IBoolLit(b) => lazabs.ast.ASTree.BoolConst(b)

      // Bit-vectors
      case IAtom(pred, Seq(IIntLit(IdealInt(bits)), left, right))
             if pred2BVBinOp contains pred =>
        BinaryExpression(rvT(left), pred2BVBinOp(pred)(bits),
                         rvT(right)).stype(BooleanType())

      case _ =>
        println("Error in conversion from Princess to Eldarica (IFormula): " + t + " sublcass of " + t.getClass)
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
