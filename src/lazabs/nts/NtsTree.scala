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
import lazabs.viewer.NTSPrinter._
import lazabs.types._

case class Nts(
  val name: String,
  val globalVars: List[Variable],
  val systems: List[NtsSubsystem]  
)
case class NtsTransition(
  val source: Int, 
  val target: Int, 
  val formula: Expression
){
  import NtsSubsystem._
  override def toString: String = 
    VertexToString(source) + " -> " + VertexToString(target) + " {" + lazabs.viewer.ScalaPrinter(formula).replaceAll("==", "=") + "}"
}
case class NtsSubsystem(
  val name: String,
  val transitions: List[NtsTransition],
  val inputVars: List[Variable],
  val outputVars: List[Variable],
  val vars: List[Variable],            // local variables + input variables + outputvariables + global variables
  val initStates: List[Int],
  val finalStates: List[Int],
  val errorStates: List[Int]
){  
  def toNTSType(t: Type): String = t match {
    case IntegerType() => "int"
    case BooleanType() => "bool"
    case ArrayType(lt)  => "" // TO-DO
    case SetType(lt)  => "" // "TO-DO
    case _ =>
      println("unsupported type " + t + " in NTS conversion")
      sys.exit(0)
  }
  override def toString: String = {
    val varsString = vars.groupBy(_.stype).map{ x =>
      x._2.map(lazabs.viewer.ScalaPrinter(_)).mkString(",") + " : " + toNTSType(x._1) + ";"
      }.foldLeft(List[String]()) { case (lst,x) => x :: lst }  
    name + " {\n" +
      (if (varsString.isEmpty) "" else (varsString.mkString("\n") + "\n")) + 
      "initial " + initStates.map(VertexToString(_)).mkString(",") + 
      ";\n" + "error se;\n" +
      transitions.map(_.toString).mkString("\n") +  
      "}"
  }
}
case class NTSCall( 
  val calleeName: String,
  val actualParameters: List[Expression],
  val returnVars: List[Variable],
  val havoc: Option[List[Variable]]
) extends Expression

object VertexToString {
  def apply(v: Int): String = v match {
    case -1 => "se"
    case i@_ => "s" + i
  }
}