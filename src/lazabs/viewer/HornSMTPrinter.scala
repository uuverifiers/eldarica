/**
 * Copyright (c) 2011-2019 Hossein Hojjat, Filip Konecny, Philipp Ruemmer.
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

import lazabs.types._
import lazabs.ast.ASTree._
import lazabs.horn.global._
import lazabs.horn.parser.HornReader

import ap.parser.SMTLineariser

object HornSMTPrinter {

  import SMTLineariser.quoteIdentifier

  def apply(system: Seq[HornClause]): String =
    "(set-info :origin \"Horn problem converted to SMT-LIB2 using Eldarica (https://github.com/uuverifiers/eldarica)\")\n" +
    "(set-logic HORN)\n" +
    system.map(Horn.getRelVarArities(_)).flatten.distinct
      .map(rv => "(declare-fun " + quoteIdentifier(rv._1) +
                 " " + (0 until rv._2).map(_ => "Int").mkString("("," ",")") +
                 " Bool)").mkString("\n") + "\n" +
      system.map(print).mkString("\n") + "\n(check-sat)"

  /**
   * gets the alphabetic character corresponding to an int 
   */
  def getAlphabeticChar(i :Int): String = {
    val alpha = i / 26
    /*"?" +*/ ((i % 26 + 65).toChar + (if(alpha > 0) alpha.toString else "")).toString
  }
  
  def type2String(t: Type) = t match {
    case AdtType(s) => s.name
    case BooleanType() => "Bool"
    case BVType(n) => "(_ BitVec " + n + ")"
    case ArrayType(IntegerType()) => "(Array Int Int)"
    case _ => "Int"
  }
  
  /**
   * printing a horn clause
   */
  def print(h: HornClause): String = printFull(h, false)
  def printFull(h: HornClause, asDefineFun : Boolean): String = {    
    var varMap = Map[String,(Int,Type)]().empty
    var curVarCounter = -1
    def getNewVarCounter: Int = {
      curVarCounter = curVarCounter + 1
      curVarCounter
    }

    def printHornLiteral(hl: HornLiteral): String = hl match {
      case Interp(v) => printExp(v)
      case RelVar(varName, params) =>
        if(params.isEmpty) quoteIdentifier(varName) else
        "(" + quoteIdentifier(varName) + " " +
        (params.map(printParameter).mkString(" ") ) + ")"        
    }

    def printParameter(p: Parameter): String = varMap.get(p.name) match {
      case Some(i) => getAlphabeticChar(i._1)
      case None => 
        val newIndex = getNewVarCounter
        varMap += (p.name -> (newIndex,p.typ))
        getAlphabeticChar(newIndex)
    }

    def printExp(e: Expression): String = e match {
      case Existential(v, qe) =>
        // TODO: this is not going to work for nested quantifiers
        "(exists ((" + getAlphabeticChar(0) + " " + type2String(v.stype) +
        ")) " + printExp(qe) + ")"
      case Universal(v, qe) =>
        // TODO: this is not going to work for nested quantifiers
        "(forall ((" + getAlphabeticChar(0) + " " + type2String(v.stype) +
        ")) " + printExp(qe) + ")"
      case Conjunction(e1, e2) => "(and " + printExp(e1) + " " + printExp(e2) + ")"
      case Disjunction(e1, e2) => "(or " + printExp(e1) + " " + printExp(e2) + ")"

      // special handling of the tester predicates of ADTs
      case e@Equality(ADTtest(adt, sortNum, expr), NumericalConst(num)) =>
        "(is-" + adt.getCtorPerSort(sortNum, num.toInt).name +
        " " + printExp(expr) + ")"

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
      case ADTctor(adt, name, exprList) =>
        if (exprList.isEmpty)
          name
        else
          "(" + name + " " + exprList.map(printExp).mkString(" ") + ")"
      case ADTsel(adt, name, exprList) =>
        "(" + name + " " + exprList.map(printExp).mkString(" ") + ")"
      case ADTsize(adt, _, v) =>
        "(_size " + printExp(v) + ")"
      case ArraySelect(ar, ind) =>
        "(select " + printExp(ar) + " " + printExp(ind) + ")"
      case ArrayUpdate(ar, ind, value) =>
        "(store " + printExp(ar) + " " + printExp(ind) + " " + printExp(value) + ")"
      case Not(e) => "(not " + printExp(e) + ")"
      case Minus(e) => "(- " + printExp(e) + ")"
      case v@Variable(name,None) => varMap.get(name) match {
        case Some(i) => getAlphabeticChar(i._1)
        case None =>
          val newIndex = getNewVarCounter
          varMap += (name -> (newIndex,v.stype))
          getAlphabeticChar(newIndex)
      }
      case Variable(_,Some(index)) => getAlphabeticChar(index)
      case NumericalConst(num) =>
        if (num<0) {
          "(- "+(num.abs)+")"
        } else {
          num.toString
        }
      case BoolConst(v) => quoteIdentifier(v.toString)
      case BVconst(bits, v) => "(_ bv" + v + " " + bits + ")"
      case _ =>
        throw new Exception("Invalid expression " + e)
        ""
    }
    val head = printHornLiteral(h.head)
    val body = h.body.size match {
      case 0 => ""
      case 1 => printHornLiteral(h.body.head) 
      case _ => {
        // print first the relation variables, then constraints
        val (relVars, other) = h.body partition (_.isInstanceOf[RelVar])
        val strings = (relVars ++ other) map (printHornLiteral _)
        "(and " + (strings mkString " ") + ")"
      }
    }
    
    if (asDefineFun) {
      val RelVar(name, params) = h.head

      val args = (for (p <- params) yield {
        val (ind, t) = varMap(p.name)
        "(" + getAlphabeticChar(ind) + " " +
          type2String(varMap(p.name)._2) + ")"
      }) mkString " "

      "(define-fun " + quoteIdentifier(name) +
      " (" + args + ") Bool " + body + ")"
    } else {
      val boundVars =
        varMap.values.toSeq.sortWith(_._1 < _._1)
              .map(v => "(" + getAlphabeticChar(v._1) + " " +
                        type2String(v._2) + ")")
              .mkString(" ")

      h.head match{
        case Interp(BoolConst(false)) =>
          if (boundVars.isEmpty) {
            "(assert (=> " + body + " false))"
          } else {
            "(assert (forall (" + boundVars + ") (=> " + body + " false)))"
          }
        case _ => 
          if (boundVars.isEmpty) {
            "(assert" + "(=> " + body + " " + head + "))"
          } else {
            "(assert (forall (" + boundVars + ") " +
            "(=> " + body + " " + head + ")))"
          }
      }
    }
  }
}
