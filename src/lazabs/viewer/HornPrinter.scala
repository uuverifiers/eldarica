/**
 * Copyright (c) 2011-2019 Hossein Hojjat. All rights reserved.
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
import lazabs.horn.global._
import lazabs.horn.parser.HornReader

object HornPrinter {
  /*def apply(system: Seq[HornClause]): String =  system.toList.sortWith((x, y) => (x.head,y.head) match {
    case (RelVar(varId1, _),RelVar(varId2, _)) => (varId1 < varId2)
    case (RelVar(varId1, _),_) => true
    case (_,RelVar(varId1, _)) => false
    case (_,_) => true
  }).map(print).mkString("\n")*/

  def apply(system: Seq[HornClause]): String =  system.map(print).mkString("\n")
  /**
   * gets the alphabetic character corresponding to an int 
   */
  def getAlphabeticChar(i :Int): String = {
    val alpha = i / 26
    ((i % 26 + 65).toChar + (if(alpha > 0) alpha.toString else "")).toString
  }
  /**
   * printing a horn clause
   */
  def print(h: HornClause): String = {
    var varMap = Map[String,Int]().empty
    var curVarCounter = -1
    def getNewVarCounter: Int = {
      curVarCounter = curVarCounter + 1
      curVarCounter
    }
    def printHornLiteral(hl: HornLiteral): String = hl match {
      case Interp(v) => printExp(v)
      case RelVar(varName, params) =>
        val removePrefix = if(varName.startsWith("_")) {  // for string that begins with underline or capital letter      
          (0 until varName.prefixLength(_ == '_')).map(_ => "und").mkString + varName.dropWhile(_ == '_')
        } else varName
        removePrefix.toLowerCase + (if(params.isEmpty) "" else ("(" + params.map(printParameter).mkString(",") + ")"))
    }
    def printParameter(p: Parameter): String = varMap.get(p.name) match {
      case Some(i) => getAlphabeticChar(i)
      case None => 
        val newIndex = getNewVarCounter
        varMap += (p.name -> newIndex)
        getAlphabeticChar(newIndex)
    }


    def printExp(e: Expression): String = e match {
      case Existential(v, qe) =>
        "EX " + getAlphabeticChar(0) + " (" + printExp(qe) + ")"
      case Universal(v, qe) =>
        "ALL " + getAlphabeticChar(0) + " (" + printExp(qe) + ")"
      case Conjunction(e1, e2) => "(" + printExp(e1) + ", " + printExp(e2) + ")"
      case Disjunction(e1, e2) => "(" + printExp(e1) + "; " + printExp(e2) + ")"

      // special handling of the tester predicates of ADTs
      case e@Equality(ADTtest(adt, sortNum, expr), NumericalConst(num)) =>
        "is-" + adt.getCtorPerSort(sortNum, num.toInt).name +
        "(" + printExp(expr) + ")"

      case Equality(e1, e2) => "(" + printExp(e1) + " = " + printExp(e2) + ")"
      case Inequality(e1, e2) => "\\" + "+(" + printExp(e1) + " = " + printExp(e2) + ")"
      case LessThanEqual(e1, e2) => "(" + printExp(e1) + " =< " + printExp(e2) + ")"
      case Modulo(e1, e2) => 
        "(" + printExp(e1) + " mod " + printExp(e2) + ")"
      case ArraySelect(ar, ind) =>
        "select(" + printExp(ar) + ", " + printExp(ind) + ")"
      case ArrayUpdate(ar, ind, value) =>
        "store(" + printExp(ar) + ", " + printExp(ind) + ", " + printExp(value) + ")"
      case BinaryExpression(e1, op, e2) => "(" + printExp(e1) + " " + op.st + " " + printExp(e2) + ")"
      case ADTctor(adt, name, exprList) =>
        name + "(" + exprList.map(printExp).mkString(", ") + ")"
      case ADTsel(adt, name, exprList) =>
        name + "(" + exprList.map(printExp).mkString(", ") + ")"
      case ADTsize(adt, _, v) =>
        "_size(" + printExp(v) + ")"
      case Not(e) => "\\" + "+(" + printExp(e) + ")"
      case UnaryExpression(op, e) => op.st + "(" + printExp(e) + ")"
      case Variable(name,None) => varMap.get(name) match {
        case Some(i) => getAlphabeticChar(i)
        case None =>
          val newIndex = getNewVarCounter
          varMap += (name -> newIndex)
          getAlphabeticChar(newIndex)
      }
      // TODO: ??
      case Variable(_,Some(index)) => 
        getAlphabeticChar(index)  // variable from Princess
      case NumericalConst(num) => num.toString
      case BoolConst(v) => "" + v
      case BVconst(bits, v) => "" + v
      case _ =>
        throw new Exception("Invalid expression")
        ""
    }
    printHornLiteral(h.head) + " :- " + h.body.map(printHornLiteral).mkString(",") + "."
  }
  /**
   * printing the Horn clause without fancy modifications for debugging
   */
  def printDebug(lit: HornLiteral): String = lit match {
    case Interp(f) => lazabs.viewer.ScalaPrinter(f)
    case RelVar(name,params) => name + "(" + params.map(p => (if(p.name.startsWith("sc_")) p.name.drop(3) else p.name)).mkString(",") + ")"
  }
  def printDebug(h: HornClause): String = printDebug(h.head) + " :- " + h.body.map(printDebug(_)).mkString(" , ")
}
