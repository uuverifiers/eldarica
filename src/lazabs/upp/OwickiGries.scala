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

import lazabs.horn.global._
import UppAst._
import lazabs.ast.ASTree._
import lazabs.utils.Manip._
import HornUpp._
import lazabs.horn.bottomup.HornPredAbs.{RelationSymbol}
import lazabs.horn.abstractions.{AbsLattice, TermSubsetLattice, ProductLattice}


object OwickiGries {
  var fileName = ""
  lazy val uppaal = if(fileName != "") promoteLocalVars(parser.UppReader(fileName)) else throw new Exception("Error in Uppaal file")
  def owickiClauses: (Seq[HornClause]) = {
    //############# different type of Horn clauses #############
    var synchCls      = List[HornClause]()        //  hand-shaking clauses
    var owckCls       = List[HornClause]()        //  Owicki-Gries  clauses
    //##########################################################
    uppaal.automata.foreach{aut =>
      aut.states.foreach{vertex =>
        aut.transitions.getOrElse(vertex,Set()).foreach{ _ match {
          case UppTransition(dest, None, assign, guard) => // local transitions
            val (clockAssign,dataAssign) = assign match {
              case Left(aList) => 
                val (clock,data) = (for(Assignment(Variable(vName,_),e) <- aList) yield (vName,e)).partition(v => uppaal.clocks.contains(v._1))
                (clock.toMap,if(!data.isEmpty) List(Left(data.toMap)) else List())
              case Right(aCall) => 
                (Map[String,Expression]().empty,List(Right(aCall)))
            }
            
            // Owicki-Gries interference clauses
            uppaal.automata.filter(_.name != aut.name).foreach {otherAutomaton =>
                owckCls ++= instantaneousTransition(uppaal,
                  otherAutomaton,
                  UppVertex(""),
                  List((otherAutomaton,UppVertex("")),(aut,vertex)),
                  Map(
                    uppaal.automatonToNum(aut.name) -> aut.stateToNum(dest)//,
                    //uppaal.automatonToNum(otherAutomaton.name) -> otherAutomaton.stateToNum(otherAutomaton.states.head)
                  ),
                  clockAssign,
                  dataAssign,
                  guard, 
                  aut.invariants.getOrElse(dest, BoolConst(true)))
            }

          case UppTransition(sndDestVertex, Some(UppSendAction(sendAction)), sndAssign, sndGuard) => // hand-shaking
            val handShakeTrans = uppaal.automata.filter(_.name != aut.name).map(a => (for((source,trans) <- a.transitions) yield (a,source,trans.filter(_.act match {
              case Some(UppReceiveAction(receiveAction)) => sendAction == receiveAction
              case _ => false
            })))).flatten.filter(!_._3.isEmpty)
            handShakeTrans.foreach{
              case (recAutomaton,recSrcVertex,recTrans) => recTrans.foreach {
                case UppTransition(recDestVertex, Some(UppReceiveAction(receiveAction)), recAssign, recGuard) =>
                  val (recClockAssign,recDataAssign) = separateDataClock(recAssign,uppaal.clocks)
                  val (sndClockAssign,sndDataAssign) = separateDataClock(sndAssign,uppaal.clocks)
                  val handShakeConstraint = shortCircuit(Conjunction(sndGuard,recGuard))
                  val destinationInvConstraint = shortCircuit(Conjunction(
                    aut.invariants.getOrElse(recDestVertex,BoolConst(true)),
                    aut.invariants.getOrElse(sndDestVertex,BoolConst(true))
                  ))

                  // synchronization clauses
                  synchCls ++= 
                    // clause for the sender automaton
                    instantaneousTransition(uppaal,
                      aut,                                             // headAutomaton
                      sndDestVertex,                                   // headState
                      List((aut,vertex),(recAutomaton,recSrcVertex)),  // bodyRelVars
                      Map(
                        uppaal.automatonToNum(aut.name)->aut.stateToNum(sndDestVertex),
                        uppaal.automatonToNum(recAutomaton.name)->recAutomaton.stateToNum(recDestVertex)
                      ),
                      recClockAssign ++ sndClockAssign,
                      sndDataAssign ++ recDataAssign,
                      handShakeConstraint,
                      destinationInvConstraint) ++
                    // clause for the receiver automaton
                    instantaneousTransition(uppaal,
                      recAutomaton,                                    // headAutomaton
                      recDestVertex,                                   // headState
                      List((aut,vertex),(recAutomaton,recSrcVertex)),  // bodyRelVars
                      Map(
                        uppaal.automatonToNum(aut.name)->aut.stateToNum(sndDestVertex),
                        uppaal.automatonToNum(recAutomaton.name)->recAutomaton.stateToNum(recDestVertex)
                      ),
                      recClockAssign ++ sndClockAssign,
                      sndDataAssign ++ recDataAssign,
                      handShakeConstraint,
                      destinationInvConstraint)
                  
                  // Owicki-Gries interference clauses
                  uppaal.automata.filterNot(a => a == aut || a == recAutomaton).foreach { otherAutomaton =>
                      owckCls ++= instantaneousTransition(uppaal,
                        otherAutomaton,
                        UppVertex(""),
                        List((otherAutomaton,UppVertex("")),(aut,vertex),(recAutomaton,recSrcVertex)),
                        Map(uppaal.automatonToNum(aut.name)->aut.stateToNum(sndDestVertex),
                          uppaal.automatonToNum(recAutomaton.name)->recAutomaton.stateToNum(recDestVertex)//,
                          //uppaal.automatonToNum(otherAutomaton.name)->otherAutomaton.stateToNum(otherState)
                        ),
                        recClockAssign ++ sndClockAssign,
                        sndDataAssign ++ recDataAssign,
                        handShakeConstraint, 
                        destinationInvConstraint
                      )
                  }

                case _ =>
              }
            }
          case UppTransition(dest, Some(UppReceiveAction(sendAction)), assigns, guard) => // hand-shaking              
        }} // transitions
      } // vertex
    }
    //println(owckCls.map(lazabs.viewer.HornPrinter.printDebug(_)).mkString("\n\n"))
    synchCls ++ owckCls    
  }
  def apply(fileName: String, toAbs: Boolean = false): (Seq[HornClause], Option[Map[String, AbsLattice]]) = {
    this.fileName = fileName
    val (individual, absMap) = individualClauses(uppaal, toAbs)
    val costs = if (toAbs) Some(absMap) else None
    (individual ++ uppaal.functions.values.map(_._4).flatten ++ owickiClauses, costs)
    //println(p.map(lazabs.viewer.HornPrinter.printDebug(_)).mkString("\n\n"))
  }
}
