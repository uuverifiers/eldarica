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

/**
 * definitions related to Abstract Reachability Graph
 */

sealed abstract class ARGNode(val id: Int)
case class RelVarNode(override val id: Int, val relName:String, abstraction: Set[Expression]) extends ARGNode(id)
case class InterpNode(override val id: Int, func: Expression) extends ARGNode(id)

/**
 * @param   params: the parameters used in the AND transition
 * @param   children: the set of the children in the AND transition  
 */
case class AndTransition(val clause: HornClause,val children: Seq[ARGNode])

case class ARGraph(
  var startNode:       ARGNode,                                               // start node
  var transitions:     Map[ARGNode, Set[AndTransition]],                      // transition relation
  var or:              Map[ARGNode, Set[RelVarNode]],                         // transition relation
  var subsumption:     Map[RelVarNode,Set[RelVarNode]]){                      // the subsumption relation

  def reportSolution: Map[String,Expression] = {
    var predMap = scala.collection.Map[String,Expression]().empty
    for(RelVarNode(_, relName, absSet) <- this.transitions.keySet; if !absSet.isEmpty) {
      val absFormula = if(absSet.size == 1) absSet.head else absSet.reduceLeft(Conjunction(_,_))
      predMap += (predMap.get(relName) match {
        case Some(prevAbs) => (relName -> Disjunction(prevAbs,absFormula))
        case None => (relName -> absFormula)
      })
    }
    Map() ++ predMap.mapValues(f => lazabs.prover.PrincessWrapper.simplify(lazabs.utils.Manip.dischargeVariables(f)))
  }
}

object FreshNodeID {
  /**
   * each node in the ARG has a unique ID
   */
  private var curNodeID = -1
  def apply: Int = {
    curNodeID = curNodeID + 1
    curNodeID
  }
}