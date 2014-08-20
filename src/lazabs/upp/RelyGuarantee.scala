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
import lazabs.types._
import HornUpp._
//import lazabs.horn.bottomup.HornPredAbs._
import ap.parser.{ITerm, IExpression, IFormula, IBoolLit}
import lazabs.horn.abstractions.{TermSubsetLattice, TermExtendingLattice, AbsLattice}

object RelyGuarantee {
  var fileName = ""
  lazy val uppaal = if(fileName != "") {
    val ul = promoteLocalVars(parser.UppReader(fileName))
    ul.copy(intVars = ul.intVars ++ ul.chans)  // putting the channels in the global variables section 
  } else throw new Exception("Error in Uppaal file")

  var absMap        = collection.mutable.Map[String, AbsLattice]()

  def createAbstractionEnv(clkSize : Int, varSize : Int, locSize : Int) : AbsLattice = {
    var offset = 0
    val gclk = List(IExpression.v(0) -> 10)
    offset = 1

    val gclkDiff = (for(i <- offset until ((clkSize * 2) + offset))
                    yield (IExpression.v(0) - IExpression.v(i) -> 3))
//    val clocks = (for (i <- offset until ((clkSize * 2) + offset) by 2)
//                  yield (IExpression.v(i) -> 5))
    val clkDiff = (for (i <- offset until ((clkSize * 2) + offset) by 2)
                   yield (IExpression.v(i) - IExpression.v(i + 1) -> 1))
    offset = offset + (clkSize * 2)

    val intVars = (for (i <- offset until ((varSize * 2) + offset))
                   yield (IExpression.v(i) -> 7))
    val varDiff = (for (i <- offset until ((varSize * 2) + offset) by 2)
                   yield (IExpression.v(i) - IExpression.v(i + 1) -> 1)).toMap

    offset = offset + (varSize * 2)
    val locVars = (for (i <- offset until ((locSize * 2) + offset))
                   yield (IExpression.v(i) -> 10))
    val locDiff = (for (i <- offset until ((locSize * 2) + offset) by 2)
                   yield (IExpression.v(i) - IExpression.v(i + 1) -> 8)).toMap

    //val clkDiff = (for ( l <- clocks.unzip._1) yield ((l(0) - l(1)) -> 4)).toMap
    //val varDiff = (for ( l <- intVars.unzip._1.combinations(2).toList) yield ((l(0) - l(1)) -> 4)).toMap

    val terms = gclk ++ /* clocks ++ */ intVars ++ locVars ++ locDiff ++ gclkDiff ++ clkDiff
    TermExtendingLattice(TermSubsetLattice(terms.unzip._1, terms.toMap))
  }
  
  /**
   * adding the required clauses to set channel variables in a C function 
   */
  def funcWithSync: (Seq[HornClause]) = {
    var newCls = Seq[HornClause]()
    // the case of having both a data assignment and a function call on the same transition 
    uppaal.automata.foreach{ aut =>
      aut.transitions.values.flatten.foreach {
        case UppTransition(dest, Some(UppReceiveAction(sync)), Right(FunctionCall(funcName, args)), guard) => 
            uppaal.functions.get(funcName) match {
              case Some((startName, endName, variables, cls)) =>
                val newStartName = "rcv_" + sync + "_" + startName
                val newEndName = "rcv_" + sync + "_" + endName
                val newVariables = Variable(sync).stype(IntegerType()) :: variables
                // adjusting the end state
                newCls :+= HornClause(RelVar(newEndName,
                       newVariables.map(v => Parameter(version(v.name,1),IntegerType()))
                    ++ newVariables.map(v => Parameter(version(v.name,2),IntegerType()))
                  ),
                  List(RelVar(endName,
                       variables.map(v => Parameter(version(v.name,1),IntegerType()))
                    ++ variables.map(v => Parameter(version(v.name,2),IntegerType()))
                    ),
                       Interp(Equality(Variable(version(sync,2)),NumericalConst(0)))
                  )
                )

                // adjusting the start state
                newCls :+= HornClause(RelVar(startName,
                       variables.map(v => Parameter(version(v.name,1),IntegerType()))
                    ++ variables.map(v => Parameter(version(v.name,2),IntegerType()))
                  ),
                  List(RelVar(newStartName,
                       newVariables.map(v => Parameter(version(v.name,1),IntegerType()))
                    ++ newVariables.map(v => Parameter(version(v.name,2),IntegerType()))
                    )
                  )
                )
              case None =>
                throw new Exception("Function " + funcName + " not found")
            }
        case UppTransition(dest, Some(UppSendAction(sync)), Right(FunctionCall(funcName, args)), guard) => 
            uppaal.functions.get(funcName) match {
              case Some((startName, endName, variables, cls)) =>
                val newStartName = "snd_" + sync + "_" + startName
                val newEndName = "snd_" + sync + "_" + endName
                val newVariables = Variable(sync).stype(IntegerType()) :: variables
                // adjusting the end state
                newCls :+= HornClause(RelVar(newEndName,
                       newVariables.map(v => Parameter(version(v.name,1),IntegerType()))
                    ++ newVariables.map(v => Parameter(version(v.name,2),IntegerType()))
                  ),
                  List(RelVar(endName,
                       variables.map(v => Parameter(version(v.name,1),IntegerType()))
                    ++ variables.map(v => Parameter(version(v.name,2),IntegerType()))
                    ),
                       Interp(Equality(Variable(version(sync,2)),NumericalConst(uppaal.automatonToNum(aut.name) + 1)))
                  )
                )
                // adjusting the start state
                newCls :+= HornClause(RelVar(startName,
                       variables.map(v => Parameter(version(v.name,1),IntegerType()))
                    ++ variables.map(v => Parameter(version(v.name,2),IntegerType()))
                  ),
                  List(RelVar(newStartName,
                       newVariables.map(v => Parameter(version(v.name,1),IntegerType()))
                    ++ newVariables.map(v => Parameter(version(v.name,2),IntegerType()))
                    )
                  )
                )
              case None => 
                throw new Exception("Function " + funcName + " not found")
            }
        case _ => 
      }
    }
    newCls.distinct
  }
  
  /**
   * creating local clauses
   */
  def getLocalClauses(toAbs: Boolean) : (Seq[HornClause], Map[String, AbsLattice]) = {
    val newFunctions: Map[String,(String,String,List[Variable],Seq[HornClause])]  = uppaal.automata.map{_.transitions.values.flatten}.flatten.map{ trans => trans match {
      case UppTransition(dest, Some(UppReceiveAction(sync)), Right(FunctionCall(funcName, args)), guard) =>
        uppaal.functions.get(funcName) match {
          case Some((startName, endName, variables, cls)) =>
            List((("rcv_" + sync + "_" + funcName) , ("rcv_" + sync + "_" + startName,"rcv_" + sync + "_" + endName,Variable(sync).stype(IntegerType()) :: variables,cls)))            
          case _ => 
            throw new Exception("Global Function " + funcName + " not found")
        }
      case UppTransition(dest, Some(UppSendAction(sync)), Right(FunctionCall(funcName, args)), guard) =>
        uppaal.functions.get(funcName) match {
          case Some((startName, endName, variables, cls)) =>
            List((("snd_" + sync + "_" + funcName) , ("snd_" + sync + "_" + startName,"snd_" + sync + "_" + endName,Variable(sync).stype(IntegerType()) :: variables,cls)))            
          case _ => 
            throw new Exception("Global Function " + funcName + " not found")
        }
      case _ => List()
    }}.flatten.toMap
    val newAutomata = uppaal.automata.map{ aut =>
      val chansGuard = uppaal.chans.map(ch => 
        Equality(Variable(ch).stype(IntegerType()),NumericalConst(0)))
        .foldLeft[Expression](BoolConst(true))(Conjunction(_,_))

      aut.copy(transitions = aut.transitions.mapValues(trans => trans.map {
        case UppTransition(dest, Some(UppReceiveAction(sync)), Left(assigns), guard) =>
            UppTransition(dest, None, Left(Assignment(Variable(sync).stype(IntegerType()),NumericalConst(0)) :: assigns), 
              shortCircuit(Conjunction(
                guard,
                Conjunction(
                  Inequality(
                    Variable(version(sync,1)).stype(IntegerType()),
                    NumericalConst(0)
                  ),
                  Inequality(
                    Variable(version(sync,1)).stype(IntegerType()),
                    NumericalConst(uppaal.automatonToNum(aut.name) + 1)
                  )
                )
              ))
            )
        case UppTransition(dest, Some(UppSendAction(sync)), Left(assigns), guard) =>
            UppTransition(dest, None, Left(Assignment(Variable(sync).stype(IntegerType()),NumericalConst(uppaal.automatonToNum(aut.name) + 1)) :: assigns), 
            shortCircuit(Conjunction(
              guard,
              Equality(
                Variable(version(sync,1)).stype(IntegerType()),
                NumericalConst(0))
              )
            ))
        //-------------------------- function call with synchronization -------------------------- 
        case UppTransition(dest, Some(UppReceiveAction(sync)), Right(FunctionCall(funcName, args)), guard) =>
            UppTransition(dest, None, Right(FunctionCall("rcv_" + sync + "_" + funcName, args)),
              shortCircuit(Conjunction(
                guard,
                Conjunction(
                  Inequality(
                    Variable(version(sync,1)).stype(IntegerType()),
                    NumericalConst(0)
                  ),
                  Inequality(
                    Variable(version(sync,1)).stype(IntegerType()),
                    NumericalConst(uppaal.automatonToNum(aut.name) + 1)
                  )
                )
              ))
            )
        case UppTransition(dest, Some(UppSendAction(sync)), Right(FunctionCall(funcName, args)), guard) =>
            UppTransition(dest, None, Right(FunctionCall("snd_" + sync + funcName, args)),
            shortCircuit(Conjunction(guard,Equality(Variable(version(sync,1)).stype(IntegerType()),NumericalConst(0)))))
        //----------------------------------------------------------------------------------------
        case UppTransition(dest, action, assigns, guard) =>
            UppTransition(dest, action, assigns, shortCircuit(Conjunction(chansGuard,guard)))
      }))
    }
    individualClauses(uppaal.copy(automata = newAutomata, functions = uppaal.functions ++ newFunctions), toAbs)
  }

  
  /**
   * creating rely clauses
   */
  def getRelyClauses(toAbs : Boolean): (Seq[HornClause]) = uppaal.automata.map{ 
    aut => {
      if(toAbs)
        absMap += (("E" + aut.name) -> createAbstractionEnv(uppaal.clocks.size, 
                                                            uppaal.intVars.size,
                                                            uppaal.automata.size))
      HornClause(
        RelVar(aut.name, 
          Parameter("c",IntegerType()) :: uppaal.clocks.toList.map(
            cl => Parameter(version(cl,2),IntegerType())
          ) ++
          uppaal.intVars.toList.map(gv => Parameter(version(gv,2), IntegerType())) ++
          (0 until uppaal.automata.size).map(i => Parameter("t" + i + "2",IntegerType()))
        ),

        RelVar(aut.name,
          Parameter("c",IntegerType()) :: uppaal.clocks.toList.map(
            cl => Parameter(version(cl,1),IntegerType())
          ) ++
          uppaal.intVars.toList.map(gv => Parameter(version(gv,1),IntegerType())) ++
          (0 until uppaal.automata.size).map(
            i => Parameter("t" + i + "1",IntegerType())))

        ::

        (RelVar("E" + aut.name,
           Parameter("c",IntegerType()) ::
           uppaal.clocks.toList.map(
             cl => List(Parameter(version(cl,1),IntegerType()),
                     Parameter(version(cl,2),IntegerType()))
           ).flatten ++
           uppaal.intVars.toList.map(
             gv => List(
               Parameter(version(gv,1),IntegerType()),
               Parameter(version(gv,2),IntegerType()))
           ).flatten ++
           (0 until uppaal.automata.size).map(
             i => List(Parameter("t" + i + "1",IntegerType()),
                    Parameter("t" + i + "2",IntegerType())
                  )
           ).flatten)
        )

        ::

        List(Interp(Equality(Variable("t" + uppaal.automatonToNum(aut.name) + "1").stype(IntegerType()),
               Variable("t" + uppaal.automatonToNum(aut.name) + "2").stype(IntegerType())))
        )
      )
    }
  }

  /**
   * creating guarantee clauses
   */
  def guarantee: (Seq[HornClause]) = uppaal.automata.map{ aut =>
    aut.states.map{ vertex =>
      aut.transitions.getOrElse(vertex, Set()).map{ transition =>

        // Getting map of modified vars/clocks
        val assignMap = transition.assign match {
          case Left(assigns) => (for(Assignment(Variable(vName,_),e) <- assigns) 
                             yield (vName,e)).toMap
          case _ => Map[String,Expression]()
        }


        // Adding invariant to guard
        val localGuard = aut.invariants.get(transition.dest) match {
          case Some(invDestin) =>
            Conjunction(
              substitute(offset(transition.guard,Variable("c").stype(IntegerType()),uppaal.clocks),
                (uppaal.clocks ++ uppaal.intVars).map(v =>
                (Variable(v).stype(IntegerType()),
                 Variable(version(v,1)).stype(IntegerType()))).toMap
              ),
              substitute(offset(invDestin,Variable("c").stype(IntegerType()),uppaal.clocks),
                (uppaal.clocks ++ uppaal.intVars).map(v =>
                (Variable(v).stype(IntegerType()),
                 Variable(version(v,2)).stype(IntegerType()))).toMap
              )
            )
          case None =>
            substitute(
              offset(transition.guard,Variable("c").stype(IntegerType()),uppaal.clocks),
              (uppaal.clocks ++ uppaal.intVars).map(v =>
                (Variable(v).stype(IntegerType()),
                 Variable(version(v,1)).stype(IntegerType()))).toMap
            )
        }

        // Guard with global clock offset
        val lGuards: List[HornLiteral] =  if (localGuard == BoolConst(true)) List() else List(Interp(localGuard))
            
        // Head
        val head = RelVar("E" + aut.name,
          Parameter("c", IntegerType()) ::
          uppaal.clocks.toList.map {
            cl => List(Parameter(version(cl,1), IntegerType()), 
              Parameter((if(assignMap.contains(cl)) version(cl,2) else version(cl,1)),
                IntegerType()
              )
            )
          }.flatten ++

          uppaal.intVars.toList.map{
            gv => List(
              Parameter(version(gv,1),IntegerType()), 
              Parameter(
                (if(assignMap.contains(gv) || transition.assign.isRight) version(gv,2) else 
                  transition.act match {
                    case Some(x) =>
                      if (x.act == gv) version(gv,2) else version(gv,1)
                    case None => version(gv,1)
                  }
                ), 
                IntegerType()
              )
            )
          }.flatten ++
 
          (0 until uppaal.automata.size).map(
            i => List(Parameter("t" + i + "1",IntegerType()),
              Parameter("t" + i + 
              (if(uppaal.automatonToNum(aut.name) == i) "2" else "1"),
                IntegerType())
            )
          ).flatten
        )

        // local automaton state
        val localState = RelVar(aut.name, 
          Parameter("c", IntegerType()) ::
            uppaal.clocks.toList.map(
              cl => Parameter(version(cl,1), IntegerType())
            ) ++
          uppaal.intVars.toList.map(
              gv => Parameter(version(gv,1), IntegerType())
          ) ++
          (0 until uppaal.automata.size).map(
              i => Parameter("t" + i + "1", IntegerType())
          )
        )

        // Transition
        val trans: List[HornLiteral] = (Interp(
          Equality(
            Variable("t" + 
              uppaal.automatonToNum(aut.name).toString + "1").stype(IntegerType()),
              NumericalConst(aut.stateToNum(vertex))
          )
        )
        
        ::
        
        Interp(Equality(Variable("t" + uppaal.automatonToNum(aut.name).toString + "2").stype(
          IntegerType()),
          NumericalConst(aut.stateToNum(transition.dest)))
        )

        ::

        (transition match {
          case UppTransition(dest, Some(UppReceiveAction(sync)), Right(FunctionCall(funcName, args)), guard) =>
            uppaal.functions.get(funcName) match {
              case Some((startName, endName, variables, cls)) =>            
                List(RelVar("rcv_" + sync + "_" + endName,
                       (Variable(sync).stype(IntegerType()) :: variables).map(v => Parameter(version(v.name,1),IntegerType()))
                    ++ (Variable(sync).stype(IntegerType()) :: variables).map(v => Parameter(version(v.name,2),IntegerType()))
                ))
              case None =>
                throw new Exception("Function " + funcName + " not found")
            }
          case UppTransition(dest, Some(UppSendAction(sync)), Right(FunctionCall(funcName, args)), guard) =>
            uppaal.functions.get(funcName) match {
              case Some((startName, endName, variables, cls)) =>            
                List(RelVar("snd_" + sync + "_" + endName,
                       (Variable(sync).stype(IntegerType()) :: variables).map(v => Parameter(version(v.name,1),IntegerType()))
                    ++ (Variable(sync).stype(IntegerType()) :: variables).map(v => Parameter(version(v.name,2),IntegerType()))
                ))
              case None =>
                throw new Exception("Function " + funcName + " not found")
            }
          case _ =>
            List()
        }) :::
        assignMap.toList.map{
          case (v,e) if (uppaal.intVars.contains(v) || uppaal.clocks.contains(v)) => 
            Interp(offset(
              Equality(
                if(uppaal.clocks.contains(v)) 
                  Subtraction(Variable("c").stype(IntegerType()),Variable(version(v,2)).stype(IntegerType())) 
                else Variable(version(v,2)).stype(IntegerType()),

                substitute(e,
                  assignMap.map(x => 
                    (Variable(x._1).stype(IntegerType()),
                     Variable(version(x._1,1)).stype(IntegerType()))
                  ).toMap
                )
              ),
              Variable("c").stype(IntegerType()),uppaal.clocks 
            ))
          case (v,e) =>
            Interp(Equality(Subtraction(Variable("c").stype(IntegerType()),Variable(v).stype(IntegerType())),e))
        })
        
 
        // Hand-shake 
        transition.act match {
          case Some(act) => 
            val actVal = ( act match {
                   case UppReceiveAction(receiveAction) =>
                     Interp(
                       Conjunction(
                         Conjunction(Inequality(Variable(version(receiveAction,1)).stype(IntegerType()), NumericalConst(0)), 
                                     Inequality(Variable(version(receiveAction,1)).stype(IntegerType()), NumericalConst(uppaal.automatonToNum(aut.name) + 1))
                         ),
                                       Equality(Variable(version(receiveAction,2)).stype(IntegerType()), NumericalConst(0))
                         
                       )
                     )
                   case UppSendAction(sendAction) =>
                     Interp(
                       Conjunction(Equality(Variable(version(sendAction,1)).stype(IntegerType()), NumericalConst(0)),
                                   Equality(Variable(version(sendAction,2)).stype(IntegerType()), NumericalConst(uppaal.automatonToNum(aut.name) + 1))
                       )
                     )
            })
            
            uppaal.automata.filter(_.name != aut.name).map(otherAut => 
              HornClause(head.copy(varName = "E" + otherAut.name), actVal::(localState::trans) ++ (lGuards))
            )
          case None =>
            val indexedGuard = lGuards match{
              case Nil => List()
              case Interp(g) :: Nil =>
                List(Interp(substitute(g,
                (uppaal.intVars ++ uppaal.clocks).zip(uppaal.intVars ++ uppaal.clocks)
                  .map(v => (Variable(v._1).stype(IntegerType()),Variable(version(v._2,1)).stype(IntegerType()))).toMap)))
              case _ => List()
            }
            
            uppaal.automata.filter(_.name != aut.name).map(otherAut => 
              HornClause(head.copy(varName = "E" + otherAut.name), localState::trans ++ (indexedGuard))
            )
        }
      }.foldLeft(Set[HornClause]())(_++_) // Transitions
    }.flatten // States
  }.flatten // Automata

  def apply(fileName: String, toAbs : Boolean = false): (Seq[HornClause], Option[Map[String, AbsLattice]]) = {
    this.fileName = fileName
   // println((local ++ rely ++ guarantee).map(lazabs.viewer.HornPrinter.printDebug(_)).mkString("\n\n"))
    val (localc, absMaplocal) = getLocalClauses(toAbs)
    val rely = getRelyClauses(toAbs) // side effects, builds absMap
    val costs =  if (toAbs){ 
                   val maps = collection.immutable.Map() ++ absMap ++ absMaplocal
                   assert(!maps.isEmpty)
                   Some(maps) 
                 }
                 else None

    (localc ++ uppaal.functions.values.map(_._4).flatten ++ funcWithSync ++ rely ++ guarantee, costs)
  }
}
