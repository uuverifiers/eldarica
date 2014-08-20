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

package lazabs.upp

import lazabs.ast.ASTree._
import lazabs.horn.global._

object UppAst {
  case class Uppaal(
    val clocks: List[String], 
    val chans: List[String],
    val intVars: List[String],
    val functions: Map[String,(String,String,List[Variable],Seq[HornClause])], // function_name -> (start_name, end_name, variables, horn_clauses)
    val automata: Seq[UppAutomaton],
    val automatonToNum: Map[String,Int]
  )
  case class UppAutomaton(
    val name: String,
    val localClocks: List[String],
    val localIntVars: List[String],
    //val localFunctions: Map[String,(String,String,List[Variable],Seq[HornClause])], // function_name -> (start_name, end_name, variables, horn_clauses)
    val initial: UppVertex,
    val errors: Set[UppVertex],
    val states: Set[UppVertex],
    val invariants: Map[UppVertex,Expression],
    val transitions: Map[UppVertex,Set[UppTransition]],
    val stateToNum: Map[UppVertex,Int]
  )
  /**
   * Transitions in Automaton
   */
  case class UppTransition(
    val dest: UppVertex, 
    val act: Option[UppSynchAction], 
    val assign: Either[List[Expression],FunctionCall],
    val guard: Expression
  )
  /**
   * Synchronization actions
   */
  sealed abstract class UppSynchAction(val act: String)
  case class UppSendAction(override val act: String) extends UppSynchAction(act) 
  case class UppReceiveAction(override val act: String) extends UppSynchAction(act)

  case class UppVertex(val name: String)
}

