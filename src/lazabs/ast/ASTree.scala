/**
 * Copyright (c) 2011-2020 Hossein Hojjat, Philipp Ruemmer. All rights reserved.
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

package lazabs.ast

import lazabs.types._
import ap.theories.{Theory, TheoryRegistry, TheoryCollector, ADT}


object ASTree {
  sealed abstract class ASTree extends ScalaType
  class Declaration() extends ASTree
  class Expression() extends ASTree
  case class Sobject(val preds: List[ASTree], val name: String, val defs: List[Declaration]) extends ASTree  
  case class Parameter(val name: String, val typ: Type) extends ASTree
  
  // Declarations
  case class ClassDeclaration(className: String, paramList: List[Parameter], parentName: Option[String], declList: List[ASTree]) extends Declaration
  /**
   * @param funcName the name of the function
   * @param params the parameters
   * @param t returned type
   * @param body body of the function
   * @param post the post-condition (if any)  
   */
  case class FunctionDefinition(funcName: String, params: List[Parameter], t: Type, body: Expression, post: Option[(Variable,Expression)] = None) extends Declaration
  case class VarDeclaration(name: String, t: Type, value: Expression) extends Declaration
  case class ConstDeclaration(name: String, t: Type, value: Expression) extends Declaration
  case class SingletonActorDeclaration(name: String, declList: List[ASTree]) extends Declaration
  case class PredsDeclaration(preds: List[ASTree]) extends Declaration
  
  // Predicates
  case class Predicate(pred: Expression, children: List[Predicate]) extends ASTree
  
  // Pattern matching
  case class CaseClause(pattern: Pattern, cond: Expression, e: Expression) extends ASTree
  case class Pattern(p: Variable) extends ASTree

  // Expressions
  case class Block(declList: List[ASTree]) extends Expression
  case class FunctionCall(funcName: String, exprList: List[Expression]) extends Expression
  case class Variable(val name: String, deBruijn: Option[Int] = None) extends Expression  
  case class NumericalConst(val num: BigInt) extends Expression
  case class CreateObject(cName: String, cArgs: List[Expression]) extends Expression
  case class BoolConst(value: Boolean) extends Expression
  case class WhileLoop(cond: Expression, body: Expression) extends Expression
  case class DoWhileLoop(cond: Expression, body: Expression) extends Expression
  case class ActorLoop(declList: List[ASTree]) extends Expression
  
  // Quantification
  case class BinderVariable(name: String) extends Expression
  case class Existential(v: BinderVariable, qe: Expression) extends Expression
  case class Universal(v: BinderVariable, qe: Expression) extends Expression
  
  
  // Array
  /**
   *  aName    -->  if an array does not have a name it is a constant array, e.g. Array(1,2)
   *  aLength  -->  if an array does not have a length it is unbounded
   */
  case class ScArray(aName: Option[Variable], aLength: Option[Expression]) extends Expression

  // Set
  /**
   *  aName    -->  if a set does not have a name it is a constant set, e.g. Set(1,2)
   */
  case class ScSet(aName: Option[Variable]) extends Expression
  
  // ADT
  
  case class ADTctor(adt: ADT, name: String,
                     exprList: Seq[Expression]) extends Expression
  case class ADTsel(adt: ADT, name: String,
                    exprList: Seq[Expression]) extends Expression
  case class ADTtest(adt: ADT, sortNum : Int,
                     v: Expression) extends Expression
  case class ADTsize(adt: ADT, sortNum : Int,
                     v: Expression) extends Expression
  
  // Bit-vectors

  case class BVconst(bits: Int, num : BigInt) extends Expression

  case class BVconcat(bits1 : Int, bits2 : Int)
       extends BinaryOperator ("concat")

  // extract bits from a bit-vector, semantics as in SMT-LIB
  case class BVextract(begin : Int, end : Int)
       extends UnaryOperator ("extract")

  case class BVnot(bits : Int) extends UnaryOperator ("bvnot")
  case class BVneg(bits : Int) extends UnaryOperator ("bvneg")

  case class BVand(bits : Int)   extends BinaryOperator("bvand")
  case class BVor(bits : Int)    extends BinaryOperator("bvor")
  case class BVadd(bits : Int)   extends BinaryOperator("bvadd")
  case class BVsub(bits : Int)   extends BinaryOperator("bvsub")
  case class BVmul(bits : Int)   extends BinaryOperator("bvmul")
  case class BVudiv(bits : Int)  extends BinaryOperator("bvudiv")
  case class BVsdiv(bits : Int)  extends BinaryOperator("bvsdiv")
  case class BVurem(bits : Int)  extends BinaryOperator("bvurem")
  case class BVsrem(bits : Int)  extends BinaryOperator("bvsrem")
  case class BVsmod(bits : Int)  extends BinaryOperator("bvsmod")
  case class BVshl(bits : Int)   extends BinaryOperator("bvshl")
  case class BVlshr(bits : Int)  extends BinaryOperator("bvlshr")
  case class BVashr(bits : Int)  extends BinaryOperator("bvashr")
  case class BVxor(bits : Int)   extends BinaryOperator("bvxor")
  case class BVxnor(bits : Int)  extends BinaryOperator("bvxnor")

  case class BVult(bits : Int)   extends BinaryOperator("bvult")
  case class BVule(bits : Int)   extends BinaryOperator("bvule")
  case class BVslt(bits : Int)   extends BinaryOperator("bvslt")
  case class BVsle(bits : Int)   extends BinaryOperator("bvsle")
  case class BVcomp(bits : Int)  extends BinaryOperator("bvcomp")

  case class BV2Int(bits : Int)  extends UnaryOperator ("bv2int")
  case class BV2Nat(bits : Int)  extends UnaryOperator ("bv2nat")

  case class Int2BV(bits : Int)  extends UnaryOperator ("int2bv")


  // Actor
  case class ReactBlock(cases: List[CaseClause]) extends ASTree
  
  // ternary expressions
  sealed abstract class TernaryOperator(val st: String)
  case class IfThenElseOp() extends TernaryOperator ("if")
  case class ArrayUpdateOp() extends TernaryOperator ("update")  
  case class TernaryExpression(op: TernaryOperator, e1: Expression, e2: Expression, e3: Expression) extends Expression  

  // binray expressions
  sealed abstract class BinaryOperator(val st: String)
  case class IfThenOp() extends BinaryOperator ("if")
  case class AssignmentOp() extends BinaryOperator ("=")
  case class DisjunctionOp() extends BinaryOperator ("||")
  case class ConjunctionOp() extends BinaryOperator ("&&")
  case class EqualityOp() extends BinaryOperator ("==")
  case class IffOp() extends BinaryOperator ("===")  
  case class InequalityOp() extends BinaryOperator ("!=")
  case class LessThanOp() extends BinaryOperator ("<")
  case class LessThanEqualOp() extends BinaryOperator("<=")
  case class GreaterThanOp() extends BinaryOperator (">")
  case class GreaterThanEqualOp() extends BinaryOperator (">=")
  case class AdditionOp() extends BinaryOperator ("+")
  case class SubtractionOp() extends BinaryOperator ("-")
  case class MultiplicationOp() extends BinaryOperator ("*")
  case class DivisionOp() extends BinaryOperator ("/")
  case class ModuloOp() extends BinaryOperator ("%")
  case class SendMessageOp() extends BinaryOperator ("!")
  case class ArraySelectOp() extends BinaryOperator ("()")
  case class SetAddOp() extends BinaryOperator ("+")
  case class SetDeleteOp() extends BinaryOperator ("-")  
  case class SetContainsOp() extends BinaryOperator ("contains")
  case class SetIntersectOp() extends BinaryOperator ("intersect")
  case class SetUnionOp() extends BinaryOperator ("union")
  case class SetSubsetOp() extends BinaryOperator ("subsetOf")  
  case class SetDifferenceOp() extends BinaryOperator ("--")
  case class AccessOp() extends BinaryOperator (".")
  case class UntilOp() extends BinaryOperator ("until")
  case class AnonymousFunctionOp() extends BinaryOperator ("=>") 
  case class BinaryExpression(e1: Expression, op: BinaryOperator, e2: Expression) extends Expression
  

  // unary expressions
  sealed abstract class UnaryOperator(val st: String)
  case class MinusOp() extends UnaryOperator ("-")
  case class NotOp() extends UnaryOperator ("!")
  case class SetHeadOp() extends UnaryOperator ("head")
  case class SetSizeOp() extends UnaryOperator ("size")
  case class UnaryExpression(op: UnaryOperator, e: Expression) extends Expression  
  
  case class Skip() extends Expression
  case class Null() extends Expression
 
  // Java-Scala affairs

  def makeVariable(name: String, deBruijn_java: scala.Option[java.lang.Integer]): Variable = {
    val deBruijn: Option[Int] = deBruijn_java match {
      case Some(n) => Some(n.intValue())  // convert Integer to Scala Int
      case None => None
    }
    Variable(name, deBruijn)
  }
  
  def makeScalaObject(name: String, defList_java: java.util.List[Declaration]): ASTree = {
    val defList = defList_java.toArray.toList   // convert java list to scala list
    Sobject(List[Expression](), name, defList.asInstanceOf[List[Declaration]])
  }
  
  def makeClassDeclaration(className: String, paramList_java: java.util.List[Parameter], parentName: Option[String], declList_java: java.util.List[ASTree]): ASTree = {
    val declList = declList_java.toArray.toList   // convert java list to scala list
    val paramList = paramList_java.toArray.toList   // convert java list to scala list
    ClassDeclaration(className, paramList.asInstanceOf[List[Parameter]], parentName, declList.asInstanceOf[List[ASTree]])
  }
  
  def makeScalaObject(predList_java: java.util.List[ASTree], sobj: ASTree): ASTree = {
    val predList = predList_java.toArray.toList   // convert java list to scala list
    val scalaObject = sobj.asInstanceOf[Sobject]
    Sobject(predList.asInstanceOf[List[ASTree]], scalaObject.name, scalaObject.defs)
  }

  def makeBlock(declList_java: java.util.List[ASTree]): Expression = {
    val declList = declList_java.toArray.toList   // convert java list to scala list
    Block(declList.asInstanceOf[List[ASTree]])
  }
  
  def makeSingletonActorDeclaration(name: String, declList_java: java.util.List[ASTree]): ASTree= {
    val declList = declList_java.toArray.toList   // convert java list to scala list    
    SingletonActorDeclaration(name, declList.asInstanceOf[List[ASTree]])
  }
  
  def makeActorLoop(declList_java: java.util.List[ASTree]): ASTree= {
    val declList = declList_java.toArray.toList   // convert java list to scala list    
    ActorLoop(declList.asInstanceOf[List[ASTree]])
  }  
  
  def makeReactBlock(cases_java: java.util.List[CaseClause]): ASTree= {
    val cases = cases_java.toArray.toList   // convert java list to scala list    
    ReactBlock(cases.asInstanceOf[List[CaseClause]])
  }
  
  def makeFunctionCall(funcName: String, exprList_java: java.util.List[Expression]): Expression = {
    val exprList = exprList_java.toArray.toList   // convert java list to scala list
    FunctionCall(funcName, exprList.asInstanceOf[List[Expression]])
  }
  
  def makeCreateObject(objName: String, exprList_java: java.util.List[Expression]): Expression = {
    val exprList = exprList_java.toArray.toList   // convert java list to scala list
    CreateObject(objName, exprList.asInstanceOf[List[Expression]])    
  }
  
  def makeTwoDimArraySelect(aName: String, elems_java1: java.util.List[Expression], elems_java2: java.util.List[Expression]): Expression = {
    val elems1 = elems_java1.toArray.toList.asInstanceOf[List[Expression]]   // convert java list to scala list
    val elems2 = elems_java2.toArray.toList.asInstanceOf[List[Expression]]   // convert java list to scala list
    if(elems1.size != 1 || elems2.size != 1) {
      throw new Exception("Error in selecting an element from a two dimensional array")
    }
    ArraySelect(ArraySelect(ScArray(Some(Variable(aName,None).stype(ArrayType(ArrayType(IntegerType())))), None), elems1.head), elems2.head)
  }
  
  def makeArrayConst(elems_java: java.util.List[Expression]): Expression = {
    val elems = elems_java.toArray.toList   // convert java list to scala list
    elems.asInstanceOf[List[Expression]].zipWithIndex.foldLeft[Expression](ScArray(None, Some(NumericalConst(elems.length))).stype(ArrayType(IntegerType())))((x,y) => (ArrayUpdate(x,NumericalConst(y._2),y._1))).stype(ArrayType(IntegerType()))
  }
   
  def makeSetConst(elems_java: java.util.List[Expression]): Expression = {
    val elems = elems_java.toArray.toList   // convert java list to scala list
    elems.asInstanceOf[List[Expression]].foldLeft[Expression](ScSet(None).stype(SetType(IntegerType())))((x,y) => (SetAdd(x,y))).stype(SetType(IntegerType()))
  }  
  
  def makeFunctionDefinition(funcName: String, params_java: java.util.List[Parameter], t: Type, e: Expression): ASTree = {
    val paramsList = params_java.toArray.toList   // convert java list to scala list
    FunctionDefinition(funcName, paramsList.asInstanceOf[List[Parameter]], t, e)
  }
  
  def makePredsDeclaration(predList_java: java.util.List[ASTree]): ASTree = {
    val predList = predList_java.toArray.toList   // convert java list to scala list
    PredsDeclaration(predList.asInstanceOf[List[ASTree]])
  }
  
  def makePredicate(pred: Expression, childList_java: java.util.List[Predicate]): ASTree = {
    val childList = childList_java.toArray.toList   // convert java list to scala list
    Predicate(pred, childList.asInstanceOf[List[Predicate]])
  }

  // Extractors
  
  object Minus {
    def apply(e: Expression) = UnaryExpression(MinusOp(), e) 
    def unapply(exp: Expression) : Option[(Expression)] = 
      exp match {
        case UnaryExpression(MinusOp(), e) => Some(e)
        case _ => None
      }
  }
  
  object Not {
    def apply(e: Expression) = UnaryExpression(NotOp(), e) 
    def unapply(exp: Expression) : Option[(Expression)] = 
      exp match {
        case UnaryExpression(NotOp(), e) => Some(e)
        case _ => None
      }
  }
  
  object IfThen {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, IfThenOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, IfThenOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object IfThenElse {
    def apply(cond: Expression, conseq: Expression, altern: Expression) = TernaryExpression(IfThenElseOp(), cond, conseq, altern)
    def unapply(exp: Expression) : Option[(Expression,Expression,Expression)] = 
      exp match {
        case TernaryExpression(IfThenElseOp(), cond, conseq, altern) => Some((cond, conseq, altern))
        case _ => None
      }
  }
  
  object ArrayUpdate {
    def apply(array: Expression, index: Expression, value: Expression) = TernaryExpression(ArrayUpdateOp(), array, index, value)
    def unapply(exp: Expression) : Option[(Expression,Expression,Expression)] = 
      exp match {
        case TernaryExpression(ArrayUpdateOp(), array, index, value) => Some((array, index, value))
        case _ => None
      }
  }
  
  object ArraySelect {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, ArraySelectOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, ArraySelectOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object ArrayConst {
    def updatesList(e: Expression): List[(BigInt,Expression)] = e match {
      case TernaryExpression(ArrayUpdateOp(), array, NumericalConst(i), value) => (i,value) :: updatesList(array)
      case TernaryExpression(ArrayUpdateOp(), array, _, value) => List((-1,value))
      case ScArray(Some(_), _) => List((-1,NumericalConst(-1)))
      case ScArray(None, _) => Nil
      case _ => Nil
    }  
    def unapply(exp: Expression) : Option[List[Expression]] =
      exp match {
      case TernaryExpression(ArrayUpdateOp(), array, index, value) =>
        if (updatesList(exp).map(_._1) == (0 until updatesList(exp).size).reverse) 
          Some(updatesList(exp).reverse.map(_._2))
        else None
      case _ => None
    }
  }
  
  object SetAdd {
    def apply(set: Expression, value: Expression) = BinaryExpression(set, SetAddOp(), value)
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(set, SetAddOp(), value) => Some((set, value))
        case _ => None
      }
  }
  
  object SetConst {
    def membersList(e: Expression): List[Expression] = e match {
      case BinaryExpression(set, SetAddOp(), value) => value :: membersList(set)
      case ScSet(aName) => Nil
      case _ => Nil
    }  
    def unapply(exp: Expression) : Option[List[Expression]] = exp match {
      case BinaryExpression(set, SetAddOp(), value) =>
        Some(membersList(exp).reverse)
      case ScSet(aName) => Some(List())
      case _ => None
    }
  }
  
  object SetContains {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, SetContainsOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = exp match {
      case BinaryExpression(left, SetContainsOp(), right) => Some((left, right))
      case _ => None
    }
  }
  
  object SetIntersect {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, SetIntersectOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = exp match {
      case BinaryExpression(left, SetIntersectOp(), right) => Some((left, right))
      case _ => None
    }
  }

  object SetUnion {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, SetUnionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = exp match {
      case BinaryExpression(left, SetUnionOp(), right) => Some((left, right))
      case _ => None
    }
  }
  
  object SetSubset {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, SetSubsetOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = exp match {
      case BinaryExpression(left, SetSubsetOp(), right) => Some((left, right))
      case _ => None
    }  
  }  
  
  object SetDifference {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, SetDifferenceOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = exp match {
      case BinaryExpression(left, SetDifferenceOp(), right) => Some((left, right))
      case _ => None
    }
  }
  
  object SetDelete {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, SetDeleteOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = exp match {
      case BinaryExpression(left, SetDeleteOp(), right) => Some((left, right))
      case _ => None
    }
  }
  
  object SetHead {
    def apply(e: Expression) = UnaryExpression(SetHeadOp(),e) 
    def unapply(exp: Expression) : Option[Expression] = exp match {
      case UnaryExpression(SetHeadOp(), exp) => Some(exp)
      case _ => None
    }
  }
  
  object SetSize {
    def apply(e: Expression) = UnaryExpression(SetSizeOp(),e) 
    def unapply(exp: Expression) : Option[Expression] = exp match {
      case UnaryExpression(SetSizeOp(), exp) => Some(exp)
      case _ => None
    }
  }
    
  object Assignment {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, AssignmentOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, AssignmentOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Disjunction {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, DisjunctionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, DisjunctionOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Conjunction {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, ConjunctionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, ConjunctionOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Equality {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, EqualityOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, EqualityOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Iff {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, IffOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, IffOp(), right) => Some((left, right))
        case _ => None
      }
  }  
  
  object Inequality {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, InequalityOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, InequalityOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object LessThan {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, LessThanOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, LessThanOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object LessThanEqual {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, LessThanEqualOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, LessThanEqualOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object GreaterThan {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, GreaterThanOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, GreaterThanOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object GreaterThanEqual {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, GreaterThanEqualOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, GreaterThanEqualOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Addition {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, AdditionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, AdditionOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Subtraction {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, SubtractionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, SubtractionOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Multiplication {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, MultiplicationOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, MultiplicationOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Division {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, DivisionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, DivisionOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Modulo {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, ModuloOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, ModuloOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object MemberAccess {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, AccessOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, AccessOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object Range {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, UntilOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, UntilOp(), right) => Some((left, right))
        case _ => None
      }
  }
  
  object AnonymousFunction {
    def apply(left: Expression, right: Expression) = BinaryExpression(left, AnonymousFunctionOp(), right) 
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, AnonymousFunctionOp(), right) => Some((left, right))
        case _ => None
      }
  }
   
  object SendMessage {
    def apply(actor: Expression, message: Expression) = BinaryExpression(actor, SendMessageOp(), message)
    def unapply(exp: Expression) : Option[(Expression,Expression)] = 
      exp match {
        case BinaryExpression(left, SendMessageOp(), right) => Some((left,right))
        case _ => None
      }
  }
  
  // helper method
  def expandPreds(p: Predicate): java.util.List[Predicate] = p match {
    case Predicate(Block(pred), children) =>
      scala.collection.JavaConversions.seqAsJavaList(pred.map(p => {
        if(!p.isInstanceOf[Expression]) {
          throw new Exception("Nested predicates are required to be expressions: " + p)
        }
        Predicate(p.asInstanceOf[Expression], children)
      }))
    case _ => scala.collection.JavaConversions.seqAsJavaList(List(p))
  }
  
}
