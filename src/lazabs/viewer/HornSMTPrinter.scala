/**
 * Copyright (c) 2011-2014 Hossein Hojjat, Filip Konecny, Philipp Ruemmer.
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

package lazabs.viewer

import lazabs.ast.ASTree._
import lazabs.horn.global._
import lazabs.horn.parser.HornReader

object HornSMTPrinter {

  def apply(system: Seq[HornClause]): String =
    "(set-info :origin \"NTS benchmark converted to SMT-LIB2 using Eldarica (http://lara.epfl.ch/w/eldarica)\")\n" +
    "(set-logic HORN)\n" +
    system.map(Horn.getRelVarArities(_)).flatten.distinct
      .map(rv => "(declare-fun " + rv._1 + " " + (0 until rv._2).map(_ => "Int").mkString("("," ",")") + " Bool)").mkString("\n") + "\n" +
      system.map(print).mkString("\n") + "\n(check-sat)"

  /**
   * gets the alphabetic character corresponding to an int 
   */
  def getAlphbeticChar(i :Int): String = {
    val alpha = i / 26
    /*"?" +*/ ((i % 26 + 65).toChar + (if(alpha > 0) alpha.toString else "")).toString
  }
  /**
   * printing a horn clause
   */
  def print(h: HornClause): String = printFull(h, false)
  def printFull(h: HornClause, asDefineFun : Boolean): String = {
    var varMap = Map[String,Int]().empty
    var curVarCounter = -1
    def getNewVarCounter: Int = {
      curVarCounter = curVarCounter + 1
      curVarCounter
    }

    def printHornLiteral(hl: HornLiteral): String = hl match {
      case Interp(v) => printExp(v)
      case RelVar(varName, params) =>
        if(params.isEmpty) varName else
        "(" + varName + " " + (params.map(printParameter).mkString(" ") ) + ")"        
    }

    def printParameter(p: Parameter): String = varMap.get(p.name) match {
      case Some(i) => getAlphbeticChar(i)
      case None => 
        val newIndex = getNewVarCounter
        varMap += (p.name -> newIndex)
        getAlphbeticChar(newIndex)
    }

    def printExp(e: Expression): String = e match {
      case Existential(v, qe) =>
        "(exists " + printExp(qe) + ")"
      case Universal(v, qe) =>
        "(forall " + printExp(qe) + ")"
      case Conjunction(e1, e2) => "(and " + printExp(e1) + " " + printExp(e2) + ")"
      case Disjunction(e1, e2) => "(or " + printExp(e1) + " " + printExp(e2) + ")"
      case Equality(e1, e2) => "(= " + printExp(e1) + " " + printExp(e2) + ")"
      case Inequality(e1, e2) => printExp(Not(Equality(e1,e2)))
      case LessThan(e1, e2) => "(< " + printExp(e1) + " " + printExp(e2) + ")"
      case LessThanEqual(e1, e2) => "(<= " + printExp(e1) + " " + printExp(e2) + ")"
      case GreaterThan(e1, e2) => "(> " + printExp(e1) + " " + printExp(e2) + ")"
      case GreaterThanEqual(e1, e2) => "(>= " + printExp(e1) + " " + printExp(e2) + ")"
      case Modulo(e1, e2) => "(mod " + printExp(e1) + " " + printExp(e2) + ")"
      case Addition(e1, e2) => "(+ " + printExp(e1) + " " + printExp(e2) + ")"
      case Subtraction(e1, e2) => "(- " + printExp(e1) + " " + printExp(e2) + ")"
      case Multiplication(e1, e2) => "(* " + printExp(e1) + " " + printExp(e2) + ")"
      case Division(e1, e2) => "(div " + printExp(e1) + " " + printExp(e2) + ")"
      case Not(e) => "(not " + printExp(e) + ")"
      case Minus(e) => "(- " + printExp(e) + ")"
      case Variable(name,None) => varMap.get(name) match {
        case Some(i) => getAlphbeticChar(i)
        case None =>
          val newIndex = getNewVarCounter
          varMap += (name -> newIndex)
          getAlphbeticChar(newIndex)
      }
      case Variable(_,Some(index)) => getAlphbeticChar(index)
      case NumericalConst(num) =>
        if (num<0) {
          "(- "+(num.abs)+")"
        } else {
          num.toString
        }
      case BoolConst(v) => v.toString
      case _ =>
        throw new Exception("Invalid expression " + e)
        ""
    }
    val head = printHornLiteral(h.head)
    val body = h.body.size match{
      case 0 => ""
      case 1 => printHornLiteral(h.body.head) 
      case _ => h.body.map(printHornLiteral).reduceLeft((a,b) => ("(and " + a + " " + b + ")")) 
    }
    val boundVars = (0 until varMap.size).map(v => "(" + getAlphbeticChar(v) + " Int)").mkString(" ")

    if (asDefineFun) {
      val RelVar(name, _) = h.head
      "(define-fun " + name + " (" + boundVars + ") Bool " + body + ")"
    } else {
      h.head match{
        case Interp(BoolConst(false)) => "(assert (not (exists (" + boundVars + ")" + body + ")))" 
        case _ => 
          if (boundVars.length() != 0) {
            "(assert (forall (" + boundVars + ")" + "(=> " + body + " " + head + ")))"
          } else {
            "(assert" + "(=> " + body + " " + head + "))"
          }
      }
    }
  }
}
