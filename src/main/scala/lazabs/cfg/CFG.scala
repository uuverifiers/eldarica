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

package lazabs.cfg

import lazabs.ast.ASTree._

/**
 * The transitions in the control flow graph consists of assumes and assignments 
 */
sealed abstract class Label
case class Assume(p: Expression) extends Label
case class Assign(lhs: Expression, rhs: Expression) extends Label
case class Havoc(v: Variable) extends Label
// the following labels are used in large block encoding
case class Sequence(l1: Label, l2: Label) extends Label
case class Choice(l1: Label, l2: Label) extends Label
// the following label is later accelerated
// qs are the intermediate states which will later get predicates
case class TransitiveClosure(ls: List[Label],qs: List[CFGVertex]) extends Label
// the following label is used for nts files
case class Transfer(t: Expression) extends Label

/**
 * control flow graph
 * each vertex has an id - the vertex with id = -1 is an error state.
 * predicate can have a set of parents
 */
case class CFGVertex(id: Int) {
  def getId = id
}

object FreshCFGStateId {
  private var curStateCounter = -1
  def apply: Int = {
    curStateCounter = curStateCounter + 1
    curStateCounter
  }
}

case class CFGAdjacent(label: Label, to: CFGVertex)

case class CFG(start: CFGVertex, 
    transitions: Map[CFGVertex,Set[CFGAdjacent]],                  // transition relation 
    parent: Map[CFGVertex,Set[CFGAdjacent]],                       // parent relation 
    predicates: Map[CFGVertex,List[(Expression,List[Int])]],       // predicates defined at each program point. The order of the predicates is important
    variables: Map[CFGVertex,Set[Variable]],                       // variables defined at each program point 
    formulas: Map[(CFGVertex,CFGVertex),Expression],               // formula corresponding to a label in the control flow graph 
    freshVars: Map[(CFGVertex,CFGVertex),Set[Variable]],           // set of fresh variables corresponding to a label in the control flow graph 
    sobject: Option[Sobject]) {                                    // the AST of the original Scala program (if any)
  def update(start: CFGVertex                                        = start,
             transitions: Map[CFGVertex,Set[CFGAdjacent]]            = transitions,
             parent: Map[CFGVertex,Set[CFGAdjacent]]                 = parent,
             predicates: Map[CFGVertex,List[(Expression,List[Int])]] = predicates,
             variables: Map[CFGVertex,Set[Variable]]                 = variables,
             formulas: Map[(CFGVertex,CFGVertex),Expression]         = formulas,
             freshVars: Map[(CFGVertex,CFGVertex),Set[Variable]]     = freshVars,
             sobject: Option[Sobject]                                = sobject): CFG =
  CFG(start,transitions,parent,predicates,variables,formulas,freshVars,sobject)
  /**
   * gets a formula between two CFG vertices
   * replaces the variables which are supposed to be fresh with fresh variables in each call 
   */
  import lazabs.utils.Manip._
  def getFormula(start: CFGVertex, end: CFGVertex, label: Label): Expression = this.formulas.get(start,end) match {
    case Some (af) =>
      val fvs = this.freshVars.getOrElse((start,end),List())
      fvs.foldLeft(af)((a,b) => substitute(a,Map(b -> freshVariable(b.stype))))
    case None =>
      val vars = if(end.getId == start.getId) this.variables.getOrElse(start, Set()) else this.variables.getOrElse(start, Set()) // Scala programs with global vars
      (if(sobject.isDefined) transFormula(label,vars)._1 else transFormulaElim(label,vars)._1) 
  }
}