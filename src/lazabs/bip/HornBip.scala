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

package lazabs.bip

import lazabs.horn.global._
import lazabs.ast.ASTree._
import lazabs.types._
import BipAst._
import ujf.verimag.bip.Core._
import scala.collection.JavaConversions._


object HornBip {
  
  def formula2Eldarica(t: Behaviors.Action): Expression = {
    if(t == null)
      return BoolConst(true)
    t match {
      case asgn: ActionLanguage.Actions.AssignmentAction =>
        Assignment(formula2Eldarica(asgn.getAssignedTarget),formula2Eldarica(asgn.getAssignedValue))
      case bin : ActionLanguage.Expressions.BinaryExpression =>        
        bin.getOperator match {
          case ActionLanguage.Expressions.BinaryOperator.GREATER_THAN_OR_EQUAL =>
            GreaterThanEqual(formula2Eldarica(bin.getLeftOperand),formula2Eldarica(bin.getRightOperand))
          case ActionLanguage.Expressions.BinaryOperator.GREATER_THAN =>
            GreaterThan(formula2Eldarica(bin.getLeftOperand),formula2Eldarica(bin.getRightOperand))
          case ActionLanguage.Expressions.BinaryOperator.ADDITION =>
            Addition(formula2Eldarica(bin.getLeftOperand),formula2Eldarica(bin.getRightOperand))
          case ActionLanguage.Expressions.BinaryOperator.EQUALITY =>
            Equality(formula2Eldarica(bin.getLeftOperand),formula2Eldarica(bin.getRightOperand))
          case ActionLanguage.Expressions.BinaryOperator.INEQUALITY => 
            Inequality(formula2Eldarica(bin.getLeftOperand),formula2Eldarica(bin.getRightOperand))
          case ActionLanguage.Expressions.BinaryOperator.LESS_THAN =>
            LessThan(formula2Eldarica(bin.getLeftOperand),formula2Eldarica(bin.getRightOperand))
          case ActionLanguage.Expressions.BinaryOperator.LESS_THAN_OR_EQUAL =>
            LessThanEqual(formula2Eldarica(bin.getLeftOperand),formula2Eldarica(bin.getRightOperand))
          case ActionLanguage.Expressions.BinaryOperator.LOGICAL_AND =>
            Conjunction(formula2Eldarica(bin.getLeftOperand),formula2Eldarica(bin.getRightOperand))
          case ActionLanguage.Expressions.BinaryOperator.LOGICAL_OR =>
            Disjunction(formula2Eldarica(bin.getLeftOperand),formula2Eldarica(bin.getRightOperand))
          case ActionLanguage.Expressions.BinaryOperator.SUBSTRACTION =>
            Subtraction(formula2Eldarica(bin.getLeftOperand),formula2Eldarica(bin.getRightOperand))
          case _ =>
            println("This binary expression is not yet implemented: " + bin)
            BoolConst(true)
        }
      case vr: ActionLanguage.Expressions.VariableReference =>
        Variable(vr.getTargetVariable.getName)
      case int: ActionLanguage.Expressions.IntegerLiteral =>
        NumericalConst(int.getIValue)
      case _ =>
        println("This expression is not yet implemented: " + t)
        BoolConst(true)
    }
  }
  
  def BipReader(fileName: String): BModule = {
    val err = new ujf.verimag.bip.cmdline.CmdLineError()
    val includeDirectories = new java.util.ArrayList[String]()
    val libFullNames = scala.collection.mutable.HashMap[String,String]()
    try {
      ujf.verimag.bip.parser.actions.Parser.parse(fileName, includeDirectories, libFullNames, err)(0) match {
        case s: Modules.System =>
          s.getRoot.getType match {
            case ct: Interactions.impl.CompoundTypeImpl =>
              
              val atomicTypes: Map[String,BAtomicType] = ct.getSubcomponent.toList.map{comp => comp.getType match {
                case at: Behaviors.impl.AtomTypeImpl =>

                  (comp.getType.getName,
                  //////////// atomic type ////////////
                  BAtomicType(
                    at.getPortDefinition.toList.map{pd =>
                      BParameter(pd.getName,pd.getType.getName)
                    },

                    at.getBehavior match {
                      case pet: Behaviors.impl.PetriNetImpl =>
                        pet.getState.toList.map(_.getName).zipWithIndex.toMap
                    },

                    at.getBehavior match {
                      case pet: Behaviors.impl.PetriNetImpl =>
                        pet.getInitialState.get(0).getName
                    },
                    
                    at.getBehavior match {
                      case pet: Behaviors.impl.PetriNetImpl => pet.getTransition.toList.map{ tran =>

                        val guard = tran.getGuard
                        val action = tran.getAction

                        BTransition(
                          tran.getOrigin.get(0).getName,
                          tran.getTrigger match {
                            case pdr: Behaviors.impl.PortDefinitionReferenceImpl =>
                              BParameter(pdr.getTarget.getName,pdr.getTarget.getType.getName)
                          },
                          if(guard == null) None else Some(formula2Eldarica(guard)),
                          if(action == null) None else Some(formula2Eldarica(action)),
                          tran.getDestination.get(0).getName
                        )
                      }
                    }
                  )
                  /////////////////////////////////////
                  )

              }}.distinct.toMap
              
              val components = ct.getSubcomponent.toList.map{comp =>
                BComponent(
                  comp.getName,
                  atomicTypes(comp.getType.getName)
                )
              }
              
              val compToNum = components.map(_.cName).zipWithIndex.toMap 
              
              val connectors = ct.getConnector.toList.map{con =>
                BConnector(
                  con.getName,
                  con.getType.getName,
                  con.getActualPort.toList.map{ap => ap match {
                    case inp: Interactions.impl.InnerPortReferenceImpl =>
                      BPortReference(inp.getTargetInstance.getTargetPart.getName, inp.getTargetPort.getName)
                  }}
                )
              }
              
              val connectorTypes = ct.getConnector.toList.map{con =>
                BConnectorType(
                  con.getType.getName,
                  con.getType.getPortParameter.toList.map(pp => BParameter(pp.getName,pp.getType.getName))
                )
              }.distinct
              
          BModule(
            connectorTypes,
            BCompoundType(
              connectors,
              compToNum,
              components
            )
          )

          }
      }
    }
    catch {  // parser error
      case e: Exception =>
        println(e.getMessage())
        System.exit(0)
          BModule(
            List(),
            BCompoundType(
              List(),
              Map().empty,
              List()
            )
          )
    }
  }
  
  /**
   * mapping states to numbers
   */
  /*def stateToNum(module: BModule): Map[String,Int] = module.compoundType.components.map{cmp =>
    cmp.cType.places.map{p =>
      (cmp.cName,p)        
    }
  }.flatten.zipWithIndex.toMap*/

  
  def apply(fileName: String) = {
    
    val bipModule = BipReader(fileName)
    
    //println(bipModule)
    
    val transitions = bipModule.compoundType.components.map{comp =>
      comp.cType.transitions.map{tran =>
        HornClause(RelVar(comp.cName, List(
          Parameter("r" + comp.cType.placeToNum(tran.dest),IntegerType()))),

          List(Interp(Equality(Variable("r" + comp.cType.placeToNum(tran.dest)).stype(IntegerType()),
                               NumericalConst(comp.cType.placeToNum(tran.dest)))))
        )
      }
    }.flatten
    
    println(transitions.map(lazabs.viewer.HornPrinter.printDebug(_)))
    

/*

  val l = for (i <- 0 to 8) yield (new Predicate("l" + i, 2 + 1))
  val sync = new ConstantTerm("sync")
  val X = new ConstantTerm("X")
  val C = new ConstantTerm("C")
  val t1 = new ConstantTerm("t1")
  val t2 = new ConstantTerm("t2")
  val th = new ConstantTerm("th")

  val barrier = new SimpleBarrier("barrier",
                                  List(Set(l(1), l(2), l(3)),
                                       Set(l(4), l(5), l(6)),
                                       Set(l(7), l(8))))
  
//        sync:
//        2    -> { rest1, heat }
//        3    -> { rest2, heat }
//        4    -> { cool1, cool }
//        5    -> { cool2, cool }

  val Rod1 = List(
    (l(3)(C, sync, C) :- true,
     NoSync),
    (l(2)(C, sync, t1) :- (l(3)(C, sync, t1), sync === 4),
     BarrierSync(barrier)),
    (l(2)(C, sync, t1) :- (l(1)(C, sync, t1), sync === 4, C - t1 >= 3600),
     BarrierSync(barrier)),
    (l(1)(C, sync, C) :- (l(2)(C, sync, t1), sync === 2),
     BarrierSync(barrier)),

    (l(1)(C, sync, t1) :- (l(1)(C, sync, t1), (sync === 3) | (sync === 5)),
     BarrierSync(barrier)),
    (l(2)(C, sync, t1) :- (l(2)(C, sync, t1), (sync === 3) | (sync === 5)),
     BarrierSync(barrier)),
    (l(3)(C, sync, t1) :- (l(3)(C, sync, t1), (sync === 3) | (sync === 5)),
     BarrierSync(barrier))
  )

  val Rod2 = List(
    (l(6)(C, sync, C) :- true,
     NoSync),
    (l(5)(C, sync, t2) :- (l(6)(C, sync, t2), sync === 5),
     BarrierSync(barrier)),
    (l(5)(C, sync, t2) :- (l(4)(C, sync, t2), sync === 5, C - t2 >= 3600),
     BarrierSync(barrier)),
    (l(4)(C, sync, C) :- (l(5)(C, sync, t2), sync === 3),
     BarrierSync(barrier)),

    (l(4)(C, sync, t2) :- (l(4)(C, sync, t2), (sync === 2) | (sync === 4)),
     BarrierSync(barrier)),
    (l(5)(C, sync, t2) :- (l(5)(C, sync, t2), (sync === 2) | (sync === 4)),
     BarrierSync(barrier)),
    (l(6)(C, sync, t2) :- (l(6)(C, sync, t2), (sync === 2) | (sync === 4)),
     BarrierSync(barrier))
  )

  val Controller = List(
    (l(7)(C, sync, C) :- true,
     NoSync),
    (l(8)(C, sync, C) :- (
       l(7)(C, sync, th), (sync === 4) | (sync === 5), C - th === 900),
     BarrierSync(barrier)),
    (l(7)(C, sync, C) :- (
       l(8)(C, sync, th), (sync === 2) | (sync === 3), C - th === 450),
     BarrierSync(barrier)),

    (l(7)(C, X, th) :- l(7)(C, sync, th),
     NoSync),
    (l(8)(C, X, th) :- l(8)(C, sync, th),
     NoSync)
  )

  val timeInvs = List(
    (C - th <= 900) :- l(7)(C, sync, th),
    (C - th <= 450) :- l(8)(C, sync, th)
  )

  val system =
    System(List((Rod1, Singleton),
                (Rod2, Singleton),
                (Controller, Singleton)),
           2, None, DiscreteTime(0), timeInvs)

  val assertions =
//    List(((C - th >= 0) & (C - th <= 900)) :- l(7)(C, sync, th))
    List(false :- (
           l(1)(C, sync, t1), l(4)(C, sync, t2), l(7)(C, sync, th),
           C - th === 900, C - t1 < 3600, C - t2 < 3600))

  new VerificationLoop(system, assertions)
  }

  
 */
    
    
    
    
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


