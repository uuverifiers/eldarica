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

package lazabs.nts

import lazabs.ast.ASTree._
import lazabs.types._
import lazabs.utils.Manip._

// imports related to nts
import nts.interf._
import nts.interf.base._
import nts.interf.expr._
import nts.parser._
import nts.parser.ASTWithoutToken._

// imports related to Flata
import verimag.flata_backend.AccelerationInput
import verimag.flata_backend.BackEnd
import verimag.flata_backend.Closure
import verimag.flata_backend.Loop

object AccelerationStrategy extends Enumeration {
  type AccelerationStrategy = Value
  val PRECISE, UNDER_APPROX, OVER_APPROX = Value
}

object FlataWrapper {
  def Eldarica2Nts(sce: Expression): (nts.parser.Expr,Set[String]) = {
    var variables: Set[String] = Set()
    def e2n(ex: Expression): nts.parser.Expr = ex match {
      case Not(e) => exNot(e2n(e))
      case Minus(e) => exUnaryMinus(e2n(e))
      case Disjunction(e1,e2) => exOr(e2n(e1),e2n(e2))
      case Conjunction(e1,e2) => exAnd(e2n(e1),e2n(e2))
      case Equality(e1,e2) => exEq(e2n(e1),e2n(e2))
      case Iff(e1,e2) => exEquiv(e2n(e1),e2n(e2))    
      case Inequality(e1,e2) => exNeq(e2n(e1),e2n(e2))
      case LessThan(e1,e2) => exLt(e2n(e1),e2n(e2))
      case LessThanEqual(e1,e2) => exLeq(e2n(e1),e2n(e2))
      case GreaterThan(e1,e2) => exGt(e2n(e1),e2n(e2))
      case GreaterThanEqual(e1,e2) => exGeq(e2n(e1),e2n(e2))   
      case Addition(e1,e2) => exPlus(e2n(e1),e2n(e2))   
      case Subtraction(e1,e2) => exMinus(e2n(e1),e2n(e2))
      case Multiplication(e1,e2) => exMult(e2n(e1),e2n(e2))
      case Division(e1,e2) => exDivide(e2n(e1),e2n(e2))
      case Modulo(e1,e2) => exRemainder(e2n(e1),e2n(e2))
      case Variable(name,None) =>        
        variables += name.stripSuffix("'")
        accessBasic(name)
      case NumericalConst(num) => litInt(num.intValue)
      case BoolConst(v) => litBool(v)
      case _ =>
        println("Error in Flata conversion " + lazabs.viewer.ScalaPrinter(sce))
        litBool(false)
    }
    val result = e2n(sce)
    (result,variables)
  }
  import AccelerationStrategy._
  /**
   * if the method input is PRECISE only the acceleration is returned
   * if the acceleration input is APPROXIMATE it first try precise acceleration (isOctagon) and only if unsuccessful it will try approximation 
   */
  def accelerate(exps: List[List[Expression]], method: AccelerationStrategy, prefix: List[Expression] = List(BoolConst(true))): Any = {
    //println("\n\n\n" + exps.map(x => x.map(lazabs.viewer.ScalaPrinter(_)).mkString(" \n ")).mkString("\n------------\n") + "\n\n\n")
    verimag.flata.Main.initActions
    var table = new nts.parser.VarTable(null)
    val ntsForms = exps.map(ll => ll.map(Eldarica2Nts(_)))
    val variables = ntsForms.map(x => x.map(_._2)).reduceLeft(_++_).reduceLeft(_++_)
    val disjunctive = scala.collection.JavaConversions.seqAsJavaList(ntsForms.map(x => (new Loop(scala.collection.JavaConversions.seqAsJavaList(x.map(_._1)))).asInstanceOf[acceleration.ILoop]))
    val prefixForms = prefix.map(Eldarica2Nts(_))
    val prefixVars = prefixForms.map(_._2).reduceLeft(_++_)
    val pref = scala.collection.JavaConversions.seqAsJavaList(prefixForms.map(_._1).map(_.asInstanceOf[nts.interf.base.IExpr]))
    (variables ++ prefixVars).foreach {declareInt(table,_)}
    ntsForms.map(x => x.map(_._1)).reduceLeft(_++_).foreach(_.semanticChecks(table))
    prefixForms.map(_._1).foreach(_.semanticChecks(table))
    var ai: AccelerationInput = new AccelerationInput(pref,disjunctive,table)
    val backend = new BackEnd
    val transitiveClosure = (method,backend.isOctagon(ai)) match {
      case (AccelerationStrategy.PRECISE,true)  => Some(lazabs.nts.NtsWrapper.Nts2Eldarica(backend.closure(ai).getClosure,List()))
      case (AccelerationStrategy.PRECISE,false) => None
      case (AccelerationStrategy.OVER_APPROX,true) => (lazabs.nts.NtsWrapper.Nts2Eldarica(backend.closure(ai).getClosure,List()),true)
      case (AccelerationStrategy.OVER_APPROX,false) => (lazabs.nts.NtsWrapper.Nts2Eldarica(backend.closureOverapprox(ai).getClosure,List()),false)
      case (AccelerationStrategy.UNDER_APPROX,true) => (lazabs.nts.NtsWrapper.Nts2Eldarica(backend.closure(ai).getClosure,List()),true)
      case (AccelerationStrategy.UNDER_APPROX,false) => (lazabs.nts.NtsWrapper.Nts2Eldarica(backend.closureUnderapprox(ai).getClosure,List()),false)
      case _ => throw new UnsupportedOperationException
    }
    verimag.flata_backend.BackEnd.finalActions     // FLATA makes some final actions (terminating Yices)
    transitiveClosure
  }  
}