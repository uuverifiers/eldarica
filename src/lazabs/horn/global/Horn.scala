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

package lazabs.horn.global

import lazabs.ast.ASTree._
import lazabs.types._ 

/**
 * definitions related to Horn clauses
 */
sealed abstract class HornLiteral
case class RelVar(val varName: String, val params: List[Parameter]) extends HornLiteral
case class Interp(val value: Expression) extends HornLiteral
case class HornClause(val head: HornLiteral, val body: List[HornLiteral]) {
  override def toString() = "("+head.toString()+","+body.toString+")"
}


object Horn {
  /**
   * returns a fresh variable name
   */
  private var curVarID = -1
  def freshName: String = {
    curVarID = curVarID + 1
    "a" + curVarID
  }
 
  /**
   * replacing the variables in the expression with fresh names
   */
  def replaceFreshVariable(e: Expression, currentMap: Map[String,String]) : (Expression,Map[String,String]) = e match {
    case TernaryExpression(op, e1, e2, e3) =>
      val (replaced1,newreps1) = replaceFreshVariable(e1,currentMap)
      val (replaced2,newreps2) = replaceFreshVariable(e2,currentMap ++ newreps1)
      val (replaced3,newreps3) = replaceFreshVariable(e2,currentMap ++ newreps1 ++ newreps2)
      (TernaryExpression(op, replaced1, replaced2, replaced3).stype(e.stype), currentMap ++ newreps1 ++ newreps2 ++ newreps3) 
    case BinaryExpression(e1, op, e2) =>
      val (replaced1,newreps1) = replaceFreshVariable(e1,currentMap)
      val (replaced2,newreps2) = replaceFreshVariable(e2,currentMap ++ newreps1)
      (BinaryExpression(replaced1, op, replaced2).stype(e.stype), currentMap ++ newreps1 ++ newreps2)
    case UnaryExpression(op, e) =>
      val (replaced,newreps) = replaceFreshVariable(e,currentMap)
      (UnaryExpression(op, replaced).stype(e.stype), currentMap ++ newreps)
    case Variable(name,None) if (currentMap.contains(name)) =>
      (Variable(currentMap.getOrElse(name,"")).stype(e.stype),currentMap)
    case Variable(name,None) if !(currentMap.contains(name)) =>
      val fresh = freshName
      (Variable(fresh).stype(e.stype),currentMap + (name -> fresh))
    case v@Variable(name,Some(_)) => (v,currentMap)
    case NumericalConst(_) => (e,currentMap)
    case BoolConst(_) => (e,currentMap)
    case ScSet(None) => (e,currentMap)
    case _ =>
      throw new Exception("Expression not supported in replacement " + e)
  }
  
  /**
   * replacing a list of parameters with fresh name
   */
  def replaceFreshVariable(parameters: List[Parameter], currentMap: Map[String,String]) : (List[Parameter],Map[String,String]) = {
    var newMap = currentMap
    parameters.foreach{p =>
      if(!currentMap.contains(p.name))
        newMap += (p.name -> freshName)
    }
    (parameters.map(param => Parameter(newMap.getOrElse(param.name,""),param.typ)),newMap)
  }
  
  /**
   * replacing the parameters in the relation variable with fresh names
   */
  def replaceFreshVariable(r: RelVar, currentMap: Map[String,String]) : (RelVar,Map[String,String]) = {
    val (newParams,newMap) = replaceFreshVariable(r.params, currentMap)
    (RelVar(r.varName,newParams),newMap)
  }
  
  /**
   * replacing the variables in an expression with fresh names
   */
  def replaceFreshVariable(i: Interp, currentMap: Map[String,String]) : (Interp,Map[String,String]) = {
    val (freshExpr,newMap) = replaceFreshVariable(i.value,currentMap)
    (Interp(freshExpr),newMap)    
  }
  
  def replaceFreshVariable(literals: List[HornLiteral]) : List[HornLiteral] = {
    var freshMap = Map[String,String]().empty
    literals.map{l => l match {
      case r@RelVar(i,params) =>
        val (nl,nm) = replaceFreshVariable(r,freshMap)
        freshMap ++= nm
        nl
      case i@Interp(func) =>
        val (nl,nm) = replaceFreshVariable(i,freshMap)
        freshMap ++= nm
        nl 
    }}
  }
  
  /**
   * determines if a Horn clause is recursive
   */
  def isRecursive(hc: HornClause): Boolean = hc.head match {
    case RelVar(varName,_) =>
      val bodyVarNames = hc.body.filter(_ match {
        case RelVar(_,_) => true
        case _ => false
      }).asInstanceOf[List[RelVar]].map(_.varName)
      bodyVarNames.contains(varName)
    case _ => false
  }
    
  /**
   * makes all the variables used in a Horn clause fresh
   */
  def fresh(hc: HornClause): HornClause = {
    val lits = replaceFreshVariable(hc.head :: hc.body)
    HornClause(lits.head,lits.tail)
  }
  
  /**
   * return all the relation variable arities in a Horn clause
   */
  def getRelVarArities(hc: HornClause): Map[String,Int] = {
    var result = collection.mutable.Map[String,Int]().empty
    (hc.head :: hc.body).foreach{_ match {
      case RelVar(relName, params) => result += (relName -> params.size)
      case _ =>
    }}
    Map() ++ result
  }
  
  /**
   * replaces the arguments of a relation symbol with distinct names
   */
  def discriminateRelVarArguments(hc: HornClause): HornClause = {
    var unifiers = Set[(String,String)]()
    var pars = Set[String]()
    def replace(lit: HornLiteral): HornLiteral = lit match {
      case RelVar(name,params) =>
        val newParams = params.map{p =>
          if(pars.contains(p.name)) {
            val newParamName = freshName
            unifiers += ((newParamName,p.name))
            Parameter(newParamName,IntegerType()) 
          }
          else {
            pars += p.name
            p
          }
        }
        RelVar(name, newParams)
      case Interp(_) => lit
    }
    val head = replace(hc.head)
    val body = hc.body.map(replace)
    HornClause(head,body ++ unifiers.map(u => Interp(Equality(Variable(u._1).stype(IntegerType()),Variable(u._2).stype(IntegerType())))))
  }
}