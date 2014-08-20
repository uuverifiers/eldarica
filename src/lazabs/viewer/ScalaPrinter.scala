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

package lazabs.viewer

import lazabs.ast.ASTree._
import lazabs.ast._
import lazabs.types._
import lazabs.cfg._

object ScalaPrinter {
  def apply( o: Sobject): String = "object " + o.name + " {\n" + o.defs.map(apply).mkString("\n") + "}" 
  def apply( e: Expression): String = e match {
    case Block(declList) => "{\n" + declList.map(apply).mkString("\n") + "}"
    case FunctionCall(funcName, exprList) if(funcName.startsWith("sc_")) => funcName.drop(3) + exprList.map(apply).mkString("(", ",", ")") 
    case FunctionCall(funcName, exprList) => funcName + exprList.map(apply).mkString("(", ",", ")")
    case ArraySelect(arr, ind) => this(arr) + "(" + this(ind) + ")"
    case ScArray(None, aLength) => "Array()"
    case ScArray(Some(aName), aLength) => this(aName)     
    case IfThenElse(cond, conseq, altern) => "if( " + this(cond) + ")" + this(conseq) + " else " + this(altern)
    case WhileLoop(cond, body) => "while( " + this(cond) + ")" + this(body)
    case ArrayConst(l) => "Array" + l.map(apply).mkString("(", ",", ")")
    case SetConst(l) => "Set" + l.map(apply).mkString("(", ",", ")")
    case SetSize(s) => "size(" + this(s) + ")"
    case ArrayUpdate(array, index, value) => this(array) + ".update(" + this(index) + "," + this(value) + ")"
    case CreateObject(cName, cArgs) => "new " + cName + cArgs.map(apply).mkString("(", ",", ")")
    case Existential(v, qe) => "(EX " + this(v) + ". " + this(qe) + ")"
    case Universal(v, qe) => "(ALL " + this(v) + ". " + this(qe) + ")"
    case BinderVariable(name) if(name.startsWith("sc_")) => name.drop(3)
    case BinderVariable(name) => name
    case BinaryExpression(e1, op, e2) => op.st match {
      case "if" => "if( " + this(e1) + ")" + this(e2)
      case _ => "(" + this(e1) + " " + op.st + " " + this(e2) + ")"
    }
    case lazabs.nts.NTSCall(callee, actualParameters, returnVars, havoc) => // added just for NTS files
      "NTSCall(" + actualParameters.map(apply).mkString("(", ",", ")") + " : " + returnVars.map(apply).mkString(",") 
    case Variable(name,_) if(name.startsWith("sc_")) => name.drop(3)
    case Variable(name,_) => name
    case NumericalConst(num) => num.toString
    case BoolConst(v: Boolean) if (v == true) => "true"
    case BoolConst(v: Boolean) if (v == false) => "false"
    case UnaryExpression(op, e) => op.st + this(e)
    case _ => ""
  }
  def apply( d: Declaration):String = d match {
    case FunctionDefinition(funcName, ps, t, e, None) =>
      "def " + funcName + ps.map(apply).mkString("(", ",", ")") +  " : " + this(t) + " = " + this(e)
    case FunctionDefinition(funcName, ps, t, e, Some(post)) =>
      "def " + funcName + ps.map(apply).mkString("(", ",", ")") +  " : " + this(t) + " = " + this(e) + " ensuring(" + this(post._1) + "=>" + this(post._2) + ")"      
    case VarDeclaration(name, t, value) =>
      "var " + name + " : " + this(t) + " = " + this(value)
    case SingletonActorDeclaration(name, ds) =>  
      "var " + name + " : Actor = actor {\n " + ds.map(apply).mkString("\n") + "}"
    case _ => ""
  }
  
  def apply( t: ASTree):String = t match {
    case e: Expression => apply(e)
    case d: Declaration => apply(d)
    case r: ReactBlock => apply(r)
    case c: CaseClause => apply(c)
    case p: Pattern => apply(p)
    case _ => ""
  }
  
  def apply(r: ReactBlock): String = r match {
    case ReactBlock(cases) => "react {\n" + cases.map(apply).mkString("\n") + "}"
    case _ => ""
  }

  def apply(c: CaseClause): String = c match {
    case CaseClause(p, BoolConst(true), e)  => "case " + this(p) + " => " + this(e)
    case CaseClause(p, cond, e)  => "case " + this(p) + " if " + this(cond ) + " => " + this(e)
    case _ => ""    
  }
  
  def apply(p : Pattern): String = p match {
    case Pattern(v) => apply(v)
    case _ => ""
  }

  def apply(t: Type): String = t match {
    case AnyType() => "Any"
    case UnitType() => "Unit"
    case IntegerType() => "Int"
    case StringType() => "String"
    case BooleanType() => "Boolean"   
    case ArrayType(t) => "Array[" + this(t) + "]"
    case _ => t.toString
  }
  def apply(d: Parameter): String = d.name + " : " + this(d.typ)  
  
  def apply(t: Label): String  = t match {
    case Assume(p) => "[" + ScalaPrinter(p) + "]"
    case Transfer(t) => "[" + ScalaPrinter(t) + "]"
    case TransitiveClosure(t,_) => "Trans(" + t.map(apply) + ")"
    case Assign(lhs, rhs) => ScalaPrinter(lhs) + "=" + ScalaPrinter(rhs)
    case Havoc(v) => "havoc(" + ScalaPrinter(v) + ")"
    case Sequence(l1,l2) => "(" + ScalaPrinter(l1) + ") ; (" + ScalaPrinter(l2) + ")"
    case Choice(l1,l2) => "(" + ScalaPrinter(l1) + ") || (" + ScalaPrinter(l2) + ")"
    case _ => ""
  } 
}