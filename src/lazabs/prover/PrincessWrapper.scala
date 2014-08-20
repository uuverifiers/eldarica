/**
 * Copyright (c) 2011-2014 Hossein Hojjat and Philipp Ruemmer.
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

import scala.collection.mutable.LinkedHashMap

object PrincessWrapper {
  
  private val api = new PrincessAPI_v1
  import api._

  // Constants used in expressions in the Princess API
  private def constantStream(num : Int) : Stream[ConstantTerm] =
    Stream.cons(new ConstantTerm("c" + num), constantStream(num + 1))
  private val globalConstants = constantStream(0)
  var symbolReservoir = globalConstants

  def resetSymbolReservoir =
    symbolReservoir = globalConstants

  /**
   * converts a list of formulas in Eldarica format to a list of formulas in Princess format
   * returns both the formulas in Princess format and the symbols used in the formulas
   */
  def formula2Princess(ts: List[Expression],initialSymbolMap: LinkedHashMap[String, ConstantTerm] = LinkedHashMap[String, ConstantTerm]().empty, keepReservoir: Boolean = false) 
    : (List[IExpression], LinkedHashMap[String, ConstantTerm]) = {
    val symbolMap = initialSymbolMap
    if (!keepReservoir)
      resetSymbolReservoir

    def f2p(ex: Expression): IExpression = ex match {
      case lazabs.ast.ASTree.ArraySelect(array, ind) =>
        select(f2p(array).asInstanceOf[ITerm],
               f2p(ind).asInstanceOf[ITerm])
      case ArrayUpdate(array, index, value) =>
        store(f2p(array).asInstanceOf[ITerm],
              f2p(index).asInstanceOf[ITerm],
              f2p(value).asInstanceOf[ITerm])
      case ScArray(None, None) => 0
      case ScArray(Some(aName), _) => f2p(aName)
      case ScArray(None, Some(len)) =>
        // let's just store the size of the array at index -1
        // is this needed at all anywhere?
        store(0, -1, f2p(len).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.SetUnion(e1, e2) => union(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.SetIntersect(e1, e2) => intersection(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])      
      case lazabs.ast.ASTree.SetSubset(e1, e2) => subsetof(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.SetDifference(e1, e2) => difference(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.SetContains(e1, e2) => in(f2p(e2).asInstanceOf[ITerm], f2p(e1).asInstanceOf[ITerm])  // note that Eldarica has "contains" and princess has "in". They are reverse
      case lazabs.ast.ASTree.SetSize(e1) => size(f2p(e1).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.SetConst(elems) => elems.map(x => singleton(f2p(x).asInstanceOf[ITerm])).foldLeft[ITerm](emptyset)((a,b) => union(a,b))
      case lazabs.ast.ASTree.Universal(v: BinderVariable, qe: Expression) => IQuantified(Quantifier.ALL, f2p(qe).asInstanceOf[IFormula])
      case lazabs.ast.ASTree.Existential(v: BinderVariable, qe: Expression) => IQuantified(Quantifier.EX, f2p(qe).asInstanceOf[IFormula])
      case lazabs.ast.ASTree.Conjunction(e1, e2) => f2p(e1).asInstanceOf[IFormula] & f2p(e2).asInstanceOf[IFormula]
      case lazabs.ast.ASTree.Disjunction(e1, e2) => f2p(e1).asInstanceOf[IFormula] | f2p(e2).asInstanceOf[IFormula]
      case lazabs.ast.ASTree.LessThan(e1, e2) => f2p(e1).asInstanceOf[ITerm] < f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.LessThanEqual(e1, e2) => f2p(e1).asInstanceOf[ITerm] <= f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.GreaterThan(e1, e2) => f2p(e1).asInstanceOf[ITerm] > f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.GreaterThanEqual(e1, e2) => f2p(e1).asInstanceOf[ITerm] >= f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.Addition(e1,e2) if (e1.stype == SetType(IntegerType()) && e2.stype == IntegerType()) =>
        union(f2p(e1).asInstanceOf[ITerm], singleton(f2p(e2).asInstanceOf[ITerm]))
      case lazabs.ast.ASTree.Addition(e1,e2) => f2p(e1).asInstanceOf[ITerm] + f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.Minus(e) => -f2p(e).asInstanceOf[ITerm]    
      case lazabs.ast.ASTree.Subtraction(e1,e2) => f2p(e1).asInstanceOf[ITerm] - f2p(e2).asInstanceOf[ITerm]
      case lazabs.ast.ASTree.Multiplication(e1,e2) => (e1,e2) match {
        case (NumericalConst(_), _) => f2p(e1).asInstanceOf[ITerm] * f2p(e2).asInstanceOf[ITerm]
        case (_,NumericalConst(_)) => f2p(e1).asInstanceOf[ITerm] * f2p(e2).asInstanceOf[ITerm]
        case (Minus(NumericalConst(_)), _) => f2p(e1).asInstanceOf[ITerm] * f2p(e2).asInstanceOf[ITerm]
        case (_,Minus(NumericalConst(_))) => f2p(e1).asInstanceOf[ITerm] * f2p(e2).asInstanceOf[ITerm]
        case _ =>
          throw new Exception("Only multiplication by constant is supported: " + ex)
      }
      case Division(e1,e2) => div(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])
      case Modulo(e1,e2) => mod(f2p(e1).asInstanceOf[ITerm], f2p(e2).asInstanceOf[ITerm])

      case lazabs.ast.ASTree.Not(e) => !f2p(e).asInstanceOf[IFormula]
      case lazabs.ast.ASTree.Inequality(e1, e2) => f2p(lazabs.ast.ASTree.Not(lazabs.ast.ASTree.Equality(e1, e2)))
      case lazabs.ast.ASTree.Equality(e1, lazabs.ast.ASTree.ScSet(None)) =>
        size(f2p(e1).asInstanceOf[ITerm]) === 0
      case lazabs.ast.ASTree.Equality(lazabs.ast.ASTree.ScSet(None), e1) =>
        isEmpty(f2p(e1).asInstanceOf[ITerm])
      case lazabs.ast.ASTree.Equality(e1, e2) =>
        val lhs = f2p(e1)
        val rhs = f2p(e2)
        //println("LHS :: \n" + e1 + " and the type: " + e1.stype)
        //println("RHS :: \n" + e2 + " and the type: " + e2.stype)
        if (lhs.isInstanceOf[IFormula])
          (lhs.asInstanceOf[IFormula] <=> rhs.asInstanceOf[IFormula])
        else if (e1.stype.isInstanceOf[SetType] && e2.stype.isInstanceOf[SetType])
          setEqual(lhs.asInstanceOf[ITerm], rhs.asInstanceOf[ITerm])
        else
          (lhs.asInstanceOf[ITerm] === rhs.asInstanceOf[ITerm])
      case lazabs.ast.ASTree.Variable(vname,None) => symbolMap.getOrElseUpdate(vname, {
        val newSym = symbolReservoir.head
        symbolReservoir = symbolReservoir.tail
        newSym
      })
      case lazabs.ast.ASTree.Variable(vname,Some(i)) => IVariable(i)
      case lazabs.ast.ASTree.NumericalConst(e) => IIntLit(ap.basetypes.IdealInt(e.bigInteger))
      case lazabs.ast.ASTree.BoolConst(v) => IBoolLit(v)
      case lazabs.ast.ASTree.ScSet(None) => emptyset
      case _ =>
        println("Error in conversion from Eldarica to Princess: " + ex)
        IBoolLit(false)
    }
    val res = ts.map(f2p)
    (res,symbolMap)
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
  import scala.util.matching.Regex
  def formula2Eldarica(t: IFormula, symMap : Map[ConstantTerm, String], removeVersions: Boolean): Expression = {
    def rvT(t: ITerm): Expression = t match {
      case IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2)) =>
        lazabs.ast.ASTree.Subtraction(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case IPlus(ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2), e1) =>
        lazabs.ast.ASTree.Subtraction(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case IPlus(e1,e2) => lazabs.ast.ASTree.Addition(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case ITimes(e1,e2) => lazabs.ast.ASTree.Multiplication(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
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
      case IConstant(cterm) =>
        val pattern = """x(\d+)(\w+)""".r
        symMap(cterm) match {
          case pattern(cVersion,n) if (removeVersions) =>
            lazabs.ast.ASTree.Variable(n,None).stype(IntegerType())
          case noVersion@_ =>
            lazabs.ast.ASTree.Variable(noVersion,None).stype(IntegerType())
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

      case IIntFormula(IIntRelation.EqZero, IPlus(IIntLit(value), e)) =>
        lazabs.ast.ASTree.Equality(rvT(e), NumericalConst((-value).bigIntValue))
      case IIntFormula(IIntRelation.EqZero, IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2))) =>
        lazabs.ast.ASTree.Equality(rvT(e1),rvT(e2))
      case IIntFormula(IIntRelation.EqZero, IPlus(ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2), e1)) =>
        lazabs.ast.ASTree.Equality(rvT(e2),rvT(e1))
//      case IIntFormula(IIntRelation.EqZero, IPlus(e1, e2)) =>
//        lazabs.ast.ASTree.Equality(rvT(e1),lazabs.ast.ASTree.Minus(rvT(e2)))
      case IIntFormula(IIntRelation.EqZero, e) => lazabs.ast.ASTree.Equality(rvT(e).stype(IntegerType()), NumericalConst(0))
      case IIntFormula(IIntRelation.GeqZero, IPlus(IIntLit(value), ITimes(ap.basetypes.IdealInt.MINUS_ONE, e))) =>
        lazabs.ast.ASTree.LessThanEqual(rvT(e).stype(IntegerType()), NumericalConst(value.bigIntValue))
      case IIntFormula(IIntRelation.GeqZero, IPlus(IIntLit(value), e)) =>
        lazabs.ast.ASTree.GreaterThanEqual(rvT(e).stype(IntegerType()), NumericalConst((-value).bigIntValue))
      case IIntFormula(IIntRelation.GeqZero, IPlus(e1, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2))) =>
        lazabs.ast.ASTree.GreaterThanEqual(rvT(e1).stype(IntegerType()), rvT(e2).stype(IntegerType()))
      case IIntFormula(IIntRelation.GeqZero, IPlus(ITimes(ap.basetypes.IdealInt.MINUS_ONE, e2), e1)) =>
        lazabs.ast.ASTree.LessThanEqual(rvT(e2).stype(IntegerType()), rvT(e1).stype(IntegerType()))
      case IIntFormula(IIntRelation.GeqZero, ITimes(ap.basetypes.IdealInt.MINUS_ONE, e)) =>
        lazabs.ast.ASTree.LessThanEqual(rvT(e).stype(IntegerType()), NumericalConst(0))
      case IIntFormula(IIntRelation.GeqZero, e) => lazabs.ast.ASTree.GreaterThanEqual(rvT(e).stype(IntegerType()), NumericalConst(0))

      case IBinFormula(IBinJunctor.And, e1, e2) => lazabs.ast.ASTree.Conjunction(rvF(e1).stype(BooleanType()), rvF(e2).stype(BooleanType()))
      case IBinFormula(IBinJunctor.Or, e1, e2) => lazabs.ast.ASTree.Disjunction(rvF(e1).stype(BooleanType()), rvF(e2).stype(BooleanType()))
      
      case IQuantified(Quantifier.EX,IIntFormula(IIntRelation.EqZero,Var0Extractor(varCoeff, remainder))) => // EX (varCoeff * _0 + remainder = 0)
       lazabs.ast.ASTree.Equality(lazabs.ast.ASTree.Modulo(reduceDeBruijn(rvT(remainder)).stype(IntegerType()),rvT(varCoeff).stype(IntegerType())),NumericalConst(0)).stype(BooleanType())
      case IQuantified(Quantifier.EX, e) =>
        lazabs.ast.ASTree.Existential(BinderVariable("i").stype(IntegerType()), rvF(e).stype(BooleanType()))
      case IQuantified(Quantifier.ALL, e) => lazabs.ast.ASTree.Universal(BinderVariable("i").stype(IntegerType()), rvF(e).stype(BooleanType()))
      case INot(e) => lazabs.ast.ASTree.Not(rvF(e).stype(BooleanType()))
      case IBoolLit(b) => lazabs.ast.ASTree.BoolConst(b)
      case _ =>
        println("Error in conversion from Princess to Eldarica (IFormula): " + t + " sublcass of " + t.getClass)
        BoolConst(false)
    }

    rvF(t)
  }
    
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
