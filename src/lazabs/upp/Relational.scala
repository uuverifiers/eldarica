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
import lazabs.types._
import HornUpp._
import lazabs.horn.bottomup.{HornClauses, HornPredAbs, DagInterpolator}
import lazabs.horn.concurrency._
import lazabs.horn.concurrency.ParametricEncoder._
import lazabs.horn.abstractions.{AbsLattice, TermSubsetLattice, ProductLattice}
import lazabs.horn.bottomup.HornTranslator


object Relational {
  val translator = new HornTranslator
  import translator._

  var fileName = ""
  lazy val uppaal = if(fileName != "") parser.UppReader(fileName) else throw new Exception("Error in Uppaal file")
  
  def init(uppaal: Uppaal, aut: UppAutomaton): HornClause = 
    HornClause(RelVar(aut.name, Parameter("c",IntegerType()) ::
        uppaal.clocks.map(Parameter(_,IntegerType())) ++
        uppaal.intVars.map(Parameter(_,IntegerType())) ++
        aut.localClocks.map(Parameter(_,IntegerType())) ++
        aut.localIntVars.map(Parameter(_,IntegerType())) ++                
        List(Parameter("t",IntegerType()))),

        (uppaal.clocks  ++ aut.localClocks).map(cl => Interp(Equality(Variable(cl).stype(IntegerType()),  Variable("c").stype(IntegerType()) ))) ++
        (uppaal.intVars ++ aut.localIntVars).map(v => Interp(Equality(Variable(v).stype(IntegerType()), NumericalConst(0) ))) ++
        List(Interp(Equality(Variable("t").stype(IntegerType()),NumericalConst(aut.stateToNum(aut.initial)) )))
    )

  
  /**
   * prepares the arguments for the relational encoding
   */
  def adjustParams(h: HornClause, uppaal: Uppaal, aut: UppAutomaton): HornClause = {
    def adjust(hl: HornLiteral): HornLiteral  = hl match {
      case RelVar(varName,params) =>
        val reorderedParams = (params.take(1 + uppaal.clocks.size) ++
            params.slice(1 + uppaal.clocks.size + aut.localClocks.size, 1 + uppaal.clocks.size + aut.localClocks.size + uppaal.intVars.size) ++
            params.slice(1 + uppaal.clocks.size, 1 + uppaal.clocks.size + aut.localClocks.size) ++
            params.slice(1 + uppaal.clocks.size + aut.localClocks.size + uppaal.intVars.size, 1 + uppaal.clocks.size + aut.localClocks.size + uppaal.intVars.size + aut.localIntVars.size) ++
            params.takeRight(uppaal.automata.size).filter(param => !param.name.startsWith("t")) )
        RelVar(varName,reorderedParams)
      case ip@Interp(_) => ip
    }
    HornClause(
      adjust(h.head),
      h.body.map(adjust)
    )
  }
  
  val channels = scala.collection.mutable.Map[String,CommChannel]()
  def getChannel(ch: String): CommChannel = channels.get(ch) match {
    case Some(channel) => channel
    case None =>
      val newChannel = new CommChannel("c")
      channels += (ch -> newChannel)
      newChannel
  }
  
  def apply(fileName: String, log: Boolean) = {
    
    this.fileName = fileName
    
    val system = uppaal.automata.map{ aut => {
      val uppGlobal = uppaal.copy(
        clocks  = uppaal.clocks  ++ aut.localClocks,
        intVars = uppaal.intVars ++ aut.localIntVars
      )

      //println(lazabs.viewer.HornPrinter.printDebug(init(uppaal,aut)))

      val communicationCls: Seq[(HornClauses.Clause, Synchronisation)] = (aut.states.map{ vertex => 
        aut.transitions.getOrElse(vertex,Set()).map{ _ match {

          case UppTransition(dest, Some(sync), assign, guard) => // local transitions
            val (clockAssign,dataAssign) = separateDataClock(assign,uppaal.clocks)
            val syncTransition = adjustParams(instantaneousTransition(
                uppGlobal,
                aut,
                dest,
                List((aut,vertex)),
                Map(uppaal.automatonToNum(aut.name) -> aut.stateToNum(dest)),
                clockAssign,
                dataAssign,
                guard,
                aut.invariants.getOrElse(dest,BoolConst(true))
              ).head,uppaal,aut)
              
            if (log) println("Synchronization: " + lazabs.viewer.HornPrinter.printDebug(syncTransition))  

            List((transform(syncTransition),

              sync match {
                case UppSendAction(act) => Send(getChannel(act))
                case UppReceiveAction(act) => Receive(getChannel(act))
              }
            ))

        case UppTransition(dest, None, assigns, guard) =>
          List()

      }}.flatten.toList
      }.toList.flatten)

      val localCls: Seq[(HornClauses.Clause, Synchronisation)] = { 
        val l = autLocalCls(uppGlobal,aut)
        if(log) println("Local Transition: " + l.map(lazabs.viewer.HornPrinter.printDebug(_)).mkString("\n"))
        (l.map(cl => (transform(adjustParams(cl,uppaal,aut)),ParametricEncoder.NoSync)))
      }

      ( 
         ( transform(init(uppaal,aut)), ParametricEncoder.NoSync) +: (communicationCls ++ localCls)
      ,
         (if(aut.localIntVars.contains("upp_" + aut.name + "_id")) 
           ParametricEncoder.Infinite else 
             ParametricEncoder.Singleton)
      )
      
    }  // aut
    }
   
    val timeInvs: Seq[HornClause] = uppaal.automata.map{aut => aut.invariants.map {inv =>
      val uppGlobal = uppaal.copy(
        clocks  = uppaal.clocks  ++ aut.localClocks,
        intVars = uppaal.intVars ++ aut.localIntVars
      )
      
      HornClause(Interp(BoolConst(false)),

        RelVar(aut.name,Parameter("c",IntegerType()) ::
        uppaal.clocks.map(Parameter(_,IntegerType())) ++
        uppaal.intVars.map(Parameter(_,IntegerType())) ++
        aut.localClocks.map(Parameter(_,IntegerType())) ++
        aut.localIntVars.map(Parameter(_,IntegerType())) ++
          List(Parameter("t",IntegerType()))
        ) :: 

        Interp(Not(offset(inv._2,Variable("c").stype(IntegerType()),uppGlobal.clocks))) ::

        List(Interp(Equality(
          Variable("t").stype(IntegerType()),
          NumericalConst(aut.stateToNum(inv._1))
        )))
      )
    }}.flatten

    val assertions: Seq[HornClause] = uppaal.automata.map{aut =>
        aut.errors.map{ errState =>
        HornClause(Interp(BoolConst(false)),
          List(
            RelVar(aut.name,Parameter("c",IntegerType()) ::
              (uppaal.clocks  ++ aut.localClocks).map(Parameter(_,IntegerType())) ++
              (uppaal.intVars ++ aut.localIntVars).map(Parameter(_,IntegerType())) ++
              List(Parameter("t",IntegerType()))
            ),
            Interp(Equality(
              Variable("t").stype(IntegerType()),
              NumericalConst(aut.stateToNum(errState)))
            )
          )
        )
      }
    }.flatten
    
    val paraAssertions = assertions map transform

    val paraSystem = ParametricEncoder.System(
           system,
           uppaal.intVars.size + 1,             // global variables + clock 
           None,
           ParametricEncoder.DiscreteTime(0),
           timeInvs.map(transform),
           paraAssertions)

    if (log) {
      println("# Global variables: " + (uppaal.intVars.size + 1))
      println("Process clauses: " + system)
      println("Assertion clauses: " + paraAssertions)
      println("Time invariants: " + paraSystem.timeInvariants)
    }

    new VerificationLoop(paraSystem)
  }
}

/*
ParametricEncoder(system : ParametricEncoder.System,
                  globalVarNum : Int,
                  backgroundAxioms : Option[Seq[ITerm] => IFormula],
                  timeSpec : ParametricEncoder.TimeSpec,
                  timeInvariants : Seq[HornClauses.Clause],
                  assertions : Seq[HornClauses.Clause],
                  invariants : Seq[Seq[Int]]
)
*/
