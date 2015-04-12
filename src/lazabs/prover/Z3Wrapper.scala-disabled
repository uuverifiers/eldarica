/**
 * Copyright (c) 2011-2014 Hossein Hojjat. All rights reserved.
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
import z3.scala._


object Z3Wrapper {
  var timeout: Option[Int] = None 
  def setTimeout(timeout: Option[Int]) = {this.timeout = timeout}
  /**
   * The z3 context that is used through the program
   */
  def createContext = {
    val z3 = if(timeout.isDefined) new Z3Context(new Z3Config("MODEL" -> false, "SOFT_TIMEOUT" -> timeout.getOrElse(0))) else new Z3Context(new Z3Config("MODEL" -> false)) 
    //toggleWarningMessages(false)
    toggleWarningMessages(false)
    z3
  }
  def toZ3Type(t: Type, z3: Z3Context): Z3Sort = t match {
    case IntegerType() => z3.mkIntSort
    case BooleanType() => z3.mkBoolSort
    case ArrayType(lt)  => z3.mkArraySort(z3.mkIntSort, toZ3Type(lt, z3))
    case SetType(lt)  => z3.mkSetSort(toZ3Type(lt, z3))
    case _ =>
      println("unsupported type " + t + " in Z3 conversion")
      sys.exit(0)
      z3.mkIntSort
  }
  def mkZ3Expr( e: Expression, z3: Z3Context): Z3AST = e match {
    case Not(e) => z3.mkNot(mkZ3Expr(e, z3))
    case Minus(e) => z3.mkUnaryMinus(mkZ3Expr(e, z3))
    case Disjunction(e1,e2) => z3.mkOr(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case Conjunction(e1,e2) => z3.mkAnd(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case Equality(e1,e2) => z3.mkEq(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case Iff(e1,e2) => z3.mkIff(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))    
    case Inequality(e1,e2) => z3.mkNot(z3.mkEq(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3)))
    case LessThan(e1,e2) => z3.mkLT(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case LessThanEqual(e1,e2) => z3.mkLE(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case GreaterThan(e1,e2) => z3.mkGT(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case GreaterThanEqual(e1,e2) => z3.mkGE(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case Addition(e1,e2) if (e1.stype == SetType(IntegerType()) && e2.stype == IntegerType()) => z3.mkSetAdd(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))    
    case Addition(e1,e2) => z3.mkAdd(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case Subtraction(e1,e2) if (e1.stype == SetType(IntegerType()) && e2.stype == IntegerType()) => z3.mkSetDel(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))    
    case Subtraction(e1,e2) => z3.mkSub(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case Multiplication(e1,e2) => z3.mkMul(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case Division(e1,e2) => z3.mkDiv(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case Modulo(e1,e2) => z3.mkMod(mkZ3Expr(e1, z3),mkZ3Expr(e2, z3))
    case ArraySelect(e1,e2) => z3.mkSelect(mkZ3Expr(e1,z3),mkZ3Expr(e2,z3))
    case ScArray(Some(aName), _) => mkZ3Expr(aName,z3)
    case ArrayUpdate(array, index, value) => z3.mkStore(mkZ3Expr(array, z3), mkZ3Expr(index, z3), mkZ3Expr(value, z3))
    case ScArray(None, aLength) if (e.stype == ArrayType(ArrayType(IntegerType()))) => z3.mkConstArray(z3.mkIntSort, z3.mkConstArray(z3.mkIntSort, z3.mkInt(0, z3.mkIntSort)))
    case ScArray(None, aLength) if (e.stype == ArrayType(IntegerType())) => z3.mkConstArray(z3.mkIntSort, z3.mkInt(0, z3.mkIntSort))
    case ScSet(None) if (e.stype == SetType(IntegerType())) => z3.mkEmptySet(z3.mkIntSort)
    case SetIntersect(e1,e2) => z3.mkSetIntersect(mkZ3Expr(e1,z3),mkZ3Expr(e2,z3))
    case SetUnion(e1,e2) => z3.mkSetUnion(mkZ3Expr(e1,z3),mkZ3Expr(e2,z3))      
    case SetDifference(e1,e2) => z3.mkSetDifference(mkZ3Expr(e1,z3),mkZ3Expr(e2,z3))
    case SetDelete(e1,e2) => z3.mkSetDel(mkZ3Expr(e1,z3),mkZ3Expr(e2,z3))    
    case SetContains(e1,e2) => z3.mkSetMember(mkZ3Expr(e2,z3),mkZ3Expr(e1,z3))
    case SetSubset(e1,e2) => z3.mkSetSubset(mkZ3Expr(e1,z3),mkZ3Expr(e2,z3))
    case SetConst(elems) => elems.map(mkZ3Expr(_,z3)).foldLeft(z3.mkEmptySet(toZ3Type(IntegerType(),z3)))((a,b) => z3.mkSetAdd(a,b))
    case Universal(v, qe) =>
     //val rear = z3.mkConst(z3.mkStringSymbol("rear"), z3.mkArraySort(z3.mkIntSort, z3.mkIntSort))
     //val boundVar = z3.mkBound(0, z3.mkIntSort)
     //val pattern: Z3Pattern = z3.mkPattern(z3.mkSelect(rear,boundVar))
      z3.mkQuantifier(true, 0, List(), List((z3.mkStringSymbol(v.name), toZ3Type(v.stype, z3))), mkZ3Expr(qe, z3))
    case Existential(v, qe) => z3.mkQuantifier(false, 0, List(), List((z3.mkStringSymbol(v.name), toZ3Type(v.stype, z3))), mkZ3Expr(qe, z3))    
    case Variable(name,None) => z3.mkConst(z3.mkStringSymbol(name), toZ3Type(e.stype, z3))
    case Variable(name,Some(i)) => z3.mkBound(i, toZ3Type(e.stype, z3))
    case NumericalConst(num) => z3.mkInt(num.intValue, z3.mkIntSort)
    case BoolConst(v) if v => z3.mkTrue
    case BoolConst(v) if (!v) => z3.mkFalse
    case _ =>
     println("Error in Z3 conversion " + lazabs.viewer.ScalaPrinter(e))
     z3.mkFalse
  }
  
  /**
   * inputs a formula and determines if it is satisfiable
   * @param e the input formula
   */
  def isSatisfiable(e: Expression): Option[Boolean] = {
    val z3 = createContext
    val formula = mkZ3Expr(e, z3)
    z3.assertCnstr(formula)
    var answer: Option[Boolean] = z3.check
    //var (answer,model) = z3.checkAndGetModel
    answer match {
      case None => println("Failure in theorem prover: " + z3.getSearchFailure.message)
      //case Some(true) => println("The model: " + model) 
      case _ => 
    }
    z3.delete
    Prover.increaseTheoremProverConsultation 
    answer
  }
}