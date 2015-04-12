/**
 * Copyright (c) 2011-2015 Hossein Hojjat and Philipp Ruemmer.
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


object TheoremProver extends Enumeration {
  type TheoremProver = Value
  val Z3, PRINCESS = Value
}

object Prover {
  import lazabs.prover.TheoremProver._
  private var prover: TheoremProver = PRINCESS
  var theoremProverConsultation = 0
  var interpolationConsultation = 0
  def getTheoremProverConsultation = theoremProverConsultation  
  def increaseTheoremProverConsultation {
    theoremProverConsultation += 1
  }
  def getInterpolationConsultation = interpolationConsultation  
  def increaseInterpolationConsultation {
    interpolationConsultation += 1
  }  
  def setProver(p: TheoremProver) {
    prover = p
  }
  
/*  def standardName(sx: Expression): String = {
    var counter = 0
    var varName = Map[Variable,Variable]().empty
    def varRename(ex: Expression): Expression = ex match {
      case v1@Variable(name,deBruijn)  if (name.endsWith("'") && ex.stype == lazabs.types.IntegerType()) => varName.get(Variable(name.stripSuffix("'"),deBruijn)) match {
        case Some(Variable(name2,deBruijn2)) => Variable(name2 + "'",deBruijn2)
        case None =>
          val newVar = Variable("x" + counter + "'",deBruijn)
          varName += (Variable(name.stripSuffix("'"),deBruijn) -> Variable("x" + counter,deBruijn))
          counter += 1
          newVar
      }        
      case v1@Variable(name,deBruijn) if(ex.stype == lazabs.types.IntegerType()) => varName.get(v1) match {
        case Some(v2) => v2
        case None =>
          val newVar = Variable("x" + counter,deBruijn)
          counter += 1
          varName += (v1 -> newVar)
          newVar
      }
      case TernaryExpression(op, e1, e2, e3) =>
        TernaryExpression(op, varRename(e1), varRename(e2), varRename(e3)).stype(ex.stype)
      case BinaryExpression(e1, op, e2) =>
        BinaryExpression(varRename(e1), op, varRename(e2)).stype(ex.stype)
      case UnaryExpression(op, e) =>
        UnaryExpression(op, varRename(e)).stype(ex.stype)
      case _ =>
        ex
    }
    lazabs.viewer.ScalaPrinter(varRename(sx))
  } */
  
  def standardPrint(sx: Expression): String = {
    val out = new StringBuilder
    val varMap = new scala.collection.mutable.HashMap[String, String]
    def printEx(ex: Expression): Unit = ex match {
      case Variable(name, None)
        if (ex.stype == lazabs.types.IntegerType()) =>
          out.append(varMap.getOrElseUpdate(name, "x" + varMap.size))
      case Variable(_, Some(index)) => {
        out.append("db"); out.append(index)
      }
      case TernaryExpression(op, e1, e2, e3) => {
        out.append('(')
        out.append(op.st)
        out.append(' ')
        printEx(e1)
        out.append(' ')
        printEx(e2)
        out.append(' ')
        printEx(e3)
        out.append(')')
      }
      case BinaryExpression(e1, op, e2) => {
        out.append('(')
        out.append(op.st)
        out.append(' ')
        printEx(e1)
        out.append(' ')
        printEx(e2)
        out.append(')')
      }
      case UnaryExpression(op, e) => {
        out.append('(')
        out.append(op.st)
        out.append(' ')
        printEx(e)
        out.append(')')
      }
      case Existential(_, qe) => {
        out.append("(EX ")
        printEx(qe)
        out.append(')')
      }
      case Universal(_, qe) => {
        out.append("(ALL ")
        printEx(qe)
        out.append(')')
      }
      case BoolConst(x) =>
        out.append(x)
      case NumericalConst(x) =>
        out.append(x)
      case Variable(x,y) =>
        out.append(x,y)
      case _ => {
        throw new Exception("Don't know how to print " + ex)
      }
    }
    printEx(sx)
    out.toString
  }

  val cache = scala.collection.mutable.HashMap[String,Option[Boolean]]().empty
  private var hitCount = 0
  def hit {
    hitCount += 1 
  }
  def getHitCount = hitCount 
  
  
  /**
   * inputs a formula and determines if it is satisfiable
   * @param e the input formula
   */
  def isSatisfiable(e: Expression): Option[Boolean] = {
    val stan = standardPrint(e)
    cache.get(stan) match {
      case Some(r) =>
        hit
        r
      case None =>
        val result = prover match {
          case Z3 =>
//            Z3Wrapper.isSatisfiable(e)
            throw new Exception("Z3 support is currently disabled")
          case PRINCESS =>
            /*
             val res1 = PrincessWrapper.isSatisfiable(e)
             val res2 = Z3Wrapper.isSatisfiable(e)
             if (res1 != res2)
               println("Z3 and Princess give different result for: " + e)
             res1
             */
            PrincessWrapper.isSatisfiable(e)
        }
        cache += (stan -> result)
        result
    }
  }
}
