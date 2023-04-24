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
import lazabs.horn.global._
import lazabs.utils.Manip._
import lazabs.types._

object NtsHorn {
  /**
   * Unify all the final states into a single state
   */
  def unifyFinalStates(nts: Nts): Nts = {
    Nts(nts.name,nts.globalVars,nts.systems.map {system =>
      var result = system
      //system.getVars)
      val finalState = if(system.finalStates.size > 1) {
        val freshFinal = lazabs.cfg.FreshCFGStateId.apply
        NtsWrapper.stateNameMap += (freshFinal -> (system.name + "_ufinal"))
        val frame = if(result.vars == 0) BoolConst(true) else {
          val frameAssign = result.vars.zip(result.vars.map(prime(_))).map(o => Equality(o._1,o._2))
          if(frameAssign.size == 1) frameAssign.head else frameAssign.reduceLeft(Conjunction(_,_))
        }
        result = result.copy(transitions = result.finalStates.map(fstate => NtsTransition(fstate,freshFinal,frame)) ::: 
            result.transitions, finalStates = List(freshFinal))
        freshFinal
      }
      result
    })
  }
  
  /**
   * Getting the NTS name for a state
   */
  def getNtsName(i: Int, prefix: String): String = NtsWrapper.stateNameMap.get(i) match{
    case Some(name) => name
    case None => (prefix + i.toString)
  }
  
  /**
   * converts a set of equations to conjunction
   */
  def assignmentsToConjunction(assigns: List[Expression]): Expression = assigns.size match {
    case 0 => BoolConst(true)
    case 1 => assigns.head
    case _ => assigns.reduceLeft(Conjunction(_,_))
  } 

  /**
   * Gets an Nts and generates the corresponding horn constraints 
   */
  def apply(initNts: Nts): Seq[HornClause] = {
    val nts = unifyFinalStates(initNts)
    val systemGlobalVars = nts.globalVars.filter(v => v.name != "sc_tid")
    var result: Seq[HornClause] = List()
    nts.systems.foreach {system =>
      val variables = system.vars  // initialize variables to the variables defined in the subsystem
      system.transitions.foreach(nt => {
        // Relation Variable of source
        val source: HornLiteral = RelVar(getNtsName(nt.source,system.name), variables.map(v => Parameter(("x1") + v.name,v.stype)) ::: variables.map(v => Parameter(("x2") + v.name,v.stype)))
        if(system.initStates.contains(nt.source) && system.name == "main") {
          val keepInitial = (variables.map(v => Variable(("x1") + v.name).stype(v.stype)).zip(variables.map(v => Variable(("x2") + v.name).stype(v.stype)))).map(o => Equality(o._1,o._2))
          result +:= HornClause(source, List(Interp(assignmentsToConjunction(keepInitial))))
        }
        nt.formula match {
          //--------------------------------------The label is a call--------------------------------------          
          case NTSCall(calleeName,actualParameters,returnVars,havoc) =>
            if (!nts.systems.exists(_.name == calleeName)) 
              throw new Exception("No matching call: " + calleeName)
            val callee = nts.systems.find(_.name == calleeName).head
            val paramAssign = (callee.inputVars ::: systemGlobalVars)
              .map(v => Variable(("x3") + v.name).stype(v.stype)).zip(actualParameters.map(putVersion(_,2,true)) ::: systemGlobalVars.map(v => (Variable(("x2") + v.name).stype(v.stype)).asInstanceOf[Expression]))
              .map(ia => Equality(ia._1,ia._2))
            val argumentRelation = Interp(assignmentsToConjunction(paramAssign))
            val calleeVisibleVars = (callee.outputVars ::: callee.inputVars ::: systemGlobalVars)
            val calleeRelVar = callee.finalStates match {
              case fin :: _ => RelVar(getNtsName(fin,system.name), 
                calleeVisibleVars.map(v => Parameter(("x3") + v.name,v.stype)) ::: 
                calleeVisibleVars.map(v => Parameter(("x4") + v.name,v.stype)))
              case Nil => Interp(BoolConst(false))
            }
            val returnAssign = (callee.outputVars ::: systemGlobalVars).map(v => Variable(("x4") + v.name).stype(v.stype))
              .zip(returnVars.map(v => Variable(("x5") + v.name.dropRight(1)).stype(v.stype)) ::: systemGlobalVars.map(v => Variable(("x5") + v.name).stype(v.stype))).map(o => Equality(o._1,o._2))
            val returnRelation = Interp(assignmentsToConjunction(returnAssign))
            val frameRelation = havoc match {
              case Some(hvars) =>
                val keptVars = variables.filterNot(v => hvars.contains(v) || systemGlobalVars.contains(v))
                if(keptVars.size == 0) Interp(BoolConst(true)) else {
                  val frameAssign = keptVars.map(v => Variable(("x2") + v.name).stype(v.stype)).zip(keptVars.map(v => Variable(("x5") + v.name).stype(v.stype))).map(o => Equality(o._1,o._2))
                  if(frameAssign.size == 1) Interp(frameAssign.head) else Interp(frameAssign.reduceLeft(Conjunction(_,_)))
                }
              case None =>
                Interp(BoolConst(true))
            }
            // ********* clause for calling function *********
            val callHead = if(system.errorStates.contains(nt.target)) Interp(BoolConst(false)) else {
              if(system.finalStates.contains(nt.target)) {
                val visibleVariables = system.outputVars ::: system.inputVars ::: systemGlobalVars
                RelVar(getNtsName(nt.target,system.name), visibleVariables.map(v => Parameter(("x1") + v.name,v.stype)) ::: visibleVariables.map(v => Parameter(("x5") + v.name,v.stype)))                
              } else              
                RelVar(getNtsName(nt.target,system.name), variables.map(v => Parameter(("x1") + v.name,v.stype)) ::: variables.map(v => Parameter(("x5") + v.name,v.stype)))
            }
            val callBody = 
                List(source) ::: 
                (if(argumentRelation != Interp(BoolConst(true))) List(argumentRelation) else List()) :::
                List(calleeRelVar) :::
                (if(returnRelation != Interp(BoolConst(true))) List(returnRelation) else List()) ::: 
                (if(frameRelation != Interp(BoolConst(true))) List(frameRelation) else List())
            // ********* clause for identity *********
            val identityHead = callee.initStates match {
              case init :: _ => 
                RelVar(
                  getNtsName(init,system.name), 
                  callee.vars.map(v => Parameter(("x3") + v.name,v.stype)) ::: 
                  callee.vars.map(v => Parameter(("x4") + v.name,v.stype))
                )
              case Nil => throw new Exception("I cannot find the initial state of the system " + callee.name)
            }
            val identityBody = 
                List(source) ::: 
                (if(argumentRelation != Interp(BoolConst(true))) List(argumentRelation) else List()) :::
                List(
                  Interp(
                    assignmentsToConjunction(
                      callee.vars.map(v => Variable(("x3") + v.name).stype(v.stype))
                      .zip(callee.vars.map(v => Variable(("x4") + v.name).stype(v.stype)))
                      .map(o => Equality(o._1,o._2)))
                  )
                )
            result ++= List(HornClause(callHead,callBody),HornClause(identityHead,identityBody))
          //-----------------------------------------------------------------------------------------------
          case _ =>
            val transfer = Interp(putVersion(nt.formula,2,true))
            val head = if(system.errorStates.contains(nt.target))
              Interp(BoolConst(false))
            else {
              if(system.finalStates.contains(nt.target)) {
                val visibleVariables = system.outputVars ::: system.inputVars ::: systemGlobalVars
                RelVar(getNtsName(nt.target,system.name), visibleVariables.map(v => Parameter(("x1") + v.name,v.stype)) ::: visibleVariables.map(v => Parameter(("x3") + v.name,v.stype)))
              } else
                RelVar(getNtsName(nt.target,system.name), variables.map(v => Parameter(("x1") + v.name,v.stype)) ::: variables.map(v => Parameter(("x3") + v.name,v.stype)))
            }
            result +:= HornClause(head, List(source,transfer))
        }
      })
    }
    result
  }
}