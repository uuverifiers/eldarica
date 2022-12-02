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
import lazabs.types._
import lazabs.utils.Manip._
import UppAst._
import lazabs.horn.bottomup._
import ap.parser.{ITerm, IExpression, IFormula, IBoolLit}
import HornPredAbs._
import ap.terfor.preds.{Predicate, Atom}
import lazabs.horn.abstractions.{AbsLattice, TermSubsetLattice, ProductLattice,
                                 TermExtendingLattice}


object HornUpp {
  /**
   * Inputs an expression and replaces all the variable usages by offsets to global clock
   */
  def offset(e: Expression, globalClock: Variable, clocks: List[String]): Expression = e match {
    case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, offset(e1,globalClock,clocks), offset(e2,globalClock,clocks), offset(e3,globalClock,clocks)) 
    case BinaryExpression(e1, op, e2) => BinaryExpression(offset(e1,globalClock,clocks), op, offset(e2,globalClock,clocks))
    case UnaryExpression(op, e) => UnaryExpression(op, offset(e,globalClock,clocks))
    case Variable(name,None) =>
      if(clocks.contains(name))
        Subtraction(globalClock,e)
      else e
    case NumericalConst(_) => e
    case BoolConst(_) => e
    case _ =>
      throw new Exception("Expression not supported in clock offset " + e)
  }
  
  /**
   * returns all the functions 
   */
  /*def allFunctions(uppaal: Uppaal): Seq[HornClause] = {
    (uppaal.globalFunctions.values.map(_._4).flatten ++ uppaal.automata.map(aut => aut.localFunctions.values.map(_._4).flatten).flatten).toSeq
  }*/
  
  def version(v: String, n: Int): String = "v_" + n + "_" + v
  
  /**
   * Transition that not advances the global time
   */
  def instantaneousTransition(
    uppaal:          Uppaal,
    headAutomaton:   UppAutomaton,
    headState:       UppVertex,
    bodyRelVars:     List[(UppAutomaton,UppVertex)],
    stateChange:     Map[Int,Int],
    clockAssignment: Map[String,Expression],
    dataAssignment:  List[Either[Map[String,Expression],FunctionCall]],
    preGuard:        Expression,
    postGuard:       Expression
  ): List[HornClause] = {

      val preGuardCondition = (if(preGuard == BoolConst(true)) List() else 
        List(Interp(substitute(
          offset(preGuard,Variable("c").stype(IntegerType()),uppaal.clocks),
          (uppaal.intVars ++ clockAssignment.keySet).map{ v =>
            (Variable(v).stype(IntegerType()),Variable(version(v,1)).stype(IntegerType()))
          }.toMap
        )))
      )
      
      val postGuardCondition = (if(postGuard == BoolConst(true)) List() else
        List(Interp(substitute(
          offset(postGuard,Variable("c").stype(IntegerType()),uppaal.clocks),
          (
            uppaal.intVars.map{ v =>
              (Variable(v).stype(IntegerType()),Variable(version(v,dataAssignment.size + 1)).stype(IntegerType()))
            }.toMap ++
            (clockAssignment.keySet).map{ v =>
              (Variable(v).stype(IntegerType()),Variable(version(v,2)).stype(IntegerType()))
            }.toMap
          )
        )))
      )
      
      val bodyRelSymbols = bodyRelVars.map{ case (bAutomaton,bState) =>
        RelVar(bAutomaton.name, Parameter("c",IntegerType()) ::
          uppaal.clocks.map(cl => Parameter(if(!clockAssignment.contains(cl)) cl else (version(cl,1)),IntegerType())) ++
          uppaal.intVars.map(cl => Parameter(version(cl,1),IntegerType())) ++
          (0 until uppaal.automatonToNum.size).map{ i =>
            (bodyRelVars.find(bv => uppaal.automatonToNum(bv._1.name) == i)) match {
              case Some((oa,os)) => oa.stateToNum.get(os) match {
                case Some(snum) => 
                  Parameter("r" + snum,IntegerType())
                case None =>
                  Parameter("t" + i,IntegerType())
              }
              case None => Parameter("t" + i,IntegerType())
            } 
          })
      }
      
      var funcInitCondition = List[HornClause]()
      
        // r0 = 0, r1 = 1, ... valuation for automata places
      val positionVals =
        ((headAutomaton.stateToNum.get(headState) match {
          case Some(snum) =>
            List((Interp(Equality(Variable("r" + headAutomaton.stateToNum(headState)).stype(IntegerType()),NumericalConst(
              headAutomaton.stateToNum(headState))))))
          case None =>
            List()
        }) ++
        (bodyRelVars.map {
          case (oa,os) => oa.stateToNum.get(os) match {
            case Some(snum) => List(Interp(Equality(Variable("r" + snum).stype(IntegerType()),NumericalConst(snum))))
            case None => List()
          }
        }.flatten) ++
        stateChange.toList.map{
          case (_,ns) => Interp(Equality(Variable("r" + ns).stype(IntegerType()),NumericalConst(ns)))
        }).distinct
        
        // Assignments to data variables
      val dataCondition = dataAssignment.zipWithIndex.map { 
        case (Left(aMap),ver) => aMap.map{ case (v,e) =>
            Interp(Equality(
              Variable(version(v,ver + 2)).stype(IntegerType()),
              substitute(
                e,
                uppaal.intVars.map{v =>
                  (Variable(v).stype(IntegerType()),Variable(version(v,ver + 1)).stype(IntegerType()))
                }.toMap
              )
            ))
          } ++
          (uppaal.intVars.diff(aMap.keys.toList)).toList.map{v =>
            Interp(Equality(
              Variable(version(v,ver + 1)).stype(IntegerType()),
              Variable(version(v,ver + 2)).stype(IntegerType())
            ))
          }
        case (Right(FunctionCall(funcName, exprList)),ver) =>
          uppaal.functions.get(funcName) match {
            case Some((startName, endName, variables, _)) =>
              //////////  activating start state of function //////////
              funcInitCondition ::= HornClause(
                RelVar(startName, 
                  variables.map(v => Parameter(version(v.name,1),IntegerType())) ++ 
                  variables.map(v => Parameter(version(v.name,2),IntegerType()))
                ),
                bodyRelSymbols ++
                preGuardCondition ++
                postGuardCondition ++
                // Assignments to clocks
                clockAssignment.toList.map{ case (v,e) =>
                  Interp(Equality(
                    Subtraction(
                      Variable("c").stype(IntegerType()),
                      Variable(version(v,2)).stype(IntegerType())
                    ),
                    offset(e,Variable("c").stype(IntegerType()),uppaal.clocks)
                  ))
                } ++
                variables.map(v => Interp(
                  Equality(
                    Variable(version(v.name,2)).stype(IntegerType()),
                    Variable(version(v.name,1)).stype(IntegerType())
                  )
                )) ++
                positionVals
              )
              /////////////////////////////////////////////////////////
              List(
                RelVar(endName, 
                  variables.map(v => Parameter(version(v.name, (ver + 1)),IntegerType())) ++ 
                  variables.map(v => Parameter(version(v.name, (ver + 2)),IntegerType()))
                )
              )
            case None => 
              throw new Exception("Function " + funcName + " not found")
          }
        case _ => List()
      }.flatten ++                         // Assignment to data variables 
      (if(dataAssignment.isEmpty)
        uppaal.intVars.map{v =>
          Interp(Equality(
            Variable(version(v,1)).stype(IntegerType()),
            Variable(version(v,2)).stype(IntegerType())
          ))
        }
      else List())
      
      // head of the Horn clause
      val head = RelVar(headAutomaton.name, Parameter("c",IntegerType()) :: 
        uppaal.clocks.map(cl => Parameter(if(!clockAssignment.contains(cl)) cl else (version(cl,2)),IntegerType())) ++
        uppaal.intVars.map(cl => Parameter(version(cl,2),IntegerType())) ++
        (0 until uppaal.automatonToNum.size).map{i => stateChange.get(i) match {
          case Some(newState) => Parameter("r" + newState,IntegerType())  
          case None => Parameter("t" + i,IntegerType())
        }})

      val body = bodyRelSymbols ++
        preGuardCondition ++
        postGuardCondition ++
        // Assignments to clocks
        clockAssignment.toList.map{ case (v,e) => 
          Interp(Equality(
            Subtraction(
              Variable("c").stype(IntegerType()),
              Variable(version(v,2)).stype(IntegerType())
            ),
            offset(e,Variable("c").stype(IntegerType()),uppaal.clocks)
          ))
        } ++
        dataCondition ++
        positionVals

      List(HornClause(head,body)) ++ funcInitCondition
  }

  /*def createRelation(name :String, arity : Int) : RelationSymbol = {
    implicit val sf = new SymbolFactory
    RelationSymbol(new ap.terfor.preds.Predicate(name, arity))
  }*/

  // global clock
  // Clocks have lowest cost
  // Then variables
  // Then locations

  def createAbstractionPredicate(clkSize : Int, varSize : Int, locSize : Int, selfLoc : Int) : AbsLattice = {
    var offset = 0
    val gclk = List(IExpression.v(0) -> 10)
    offset = 1
    val gclkDiff = (for(i <- offset until clkSize+offset) yield (IExpression.v(0) - IExpression.v(i) -> 1))
    val clocks =  (for (i <- offset until clkSize + offset) yield (IExpression.v(i) -> 2))
    offset = offset + clkSize
    val intVars = (for (i <- offset until varSize + offset) yield (IExpression.v(i) -> 2))
    offset = offset + varSize
    val locVars = (for (i <- offset until locSize + offset) yield (IExpression.v(i) -> 9) )

    val clkDiff = (for ( l <- clocks.unzip._1.combinations(2).toList) yield ((l(0) - l(1)) -> 1))
    val varDiff = (for ( l <- intVars.unzip._1.combinations(2).toList) yield ((l(0) - l(1)) -> 1))

    val terms = gclk ++ /* clocks ++ */ intVars ++ locVars ++ gclkDiff ++ varDiff ++ clkDiff 
    TermExtendingLattice(TermSubsetLattice(terms.unzip._1, terms.toMap))
  }

  def createAbstractionPredicateSelf(clkSize : Int, varSize : Int, locSize : Int, selfLoc : Int) : AbsLattice = {
    var offset = 0
    val gclk = List(IExpression.v(0) -> 10)

    offset = 1
    val gclkDiff = (for(i <- offset until clkSize+offset) yield (IExpression.v(0) - IExpression.v(i) -> 1))
    val clocks =  (for (i <- offset until clkSize + offset) yield (IExpression.v(i) -> 6))
    offset = offset + clkSize
    val intVars = (for (i <- offset until varSize + offset) yield (IExpression.v(i) -> 6))
                                             
    offset = offset + varSize
    val locVars = (for (i <- offset until locSize + offset) yield if (i == offset + selfLoc) (IExpression.v(i) -> 2) else (IExpression.v(i) -> 9) )

    val clkDiff = (for ( l <- clocks.unzip._1.combinations(2).toList) yield ((l(0) - l(1)) -> 1))
    val varDiff = (for ( l <- intVars.unzip._1.combinations(2).toList) yield ((l(0) - l(1)) -> 1))

    val terms = gclk ++ /* clocks ++ */ intVars ++ locVars ++ gclkDiff ++ varDiff ++ clkDiff 
    TermExtendingLattice(TermSubsetLattice(terms.unzip._1, terms.toMap))
  }

  /** 
   * separates data from clock in the assignments on transitions  
   */
  def separateDataClock(assign: Either[List[Expression],FunctionCall], clocks: List[String]): 
    (Map[String,Expression],List[Either[Map[String,Expression],FunctionCall]]) = assign match {
      case Left(aList) =>
        val (clock,data) = (for(Assignment(Variable(vName,_),e) <- aList) yield (vName,e)).partition(v => (clocks).contains(v._1))
        (clock.toMap,if(!data.isEmpty) List(Left(data.toMap)) else List())
      case Right(aCall) =>
        (Map[String,Expression]().empty,List(Right(aCall)))
  }
  
  /**
   * Promoting local variables to the global scope for the sake of completeness
   */
  def promoteLocalVars(uppaal: Uppaal): Uppaal = uppaal.copy(
    clocks  = uppaal.clocks  ++ uppaal.automata.map(_.localClocks).flatten,
    intVars = uppaal.intVars ++ uppaal.automata.map(_.localIntVars).flatten
  )
  
  /**
   * initializes the variables to default values
   * - 0 for data variables
   * - global clock (c) for clock variables
   * - initial states of automata for positions 
   */
  def autInitClause(uppaal: Uppaal, aut: UppAutomaton): HornClause = {
    val initialStates = uppaal.automata.map{aut =>
      (uppaal.automatonToNum(aut.name),aut.stateToNum(aut.initial))
    }.toMap
    HornClause(RelVar(aut.name, Parameter("c",IntegerType()) :: 
      uppaal.clocks.map(Parameter(_,IntegerType())) ++
      uppaal.intVars.map(Parameter(_,IntegerType())) ++
      (0 until uppaal.automata.size).map(i => Parameter("t" + i,IntegerType()))),
        
      uppaal.clocks.map(cl => Interp(Equality(Variable(cl).stype(IntegerType()),  Variable("c").stype(IntegerType()) ))) ++
      uppaal.intVars.map(v => Interp(Equality(Variable(v).stype(IntegerType()), NumericalConst(0) ))) ++
      (0 until uppaal.automata.size).map(i => Interp(Equality(Variable("t" + i).stype(IntegerType()),NumericalConst(initialStates(i)) )))
      )
  }

  
  def initCls(uppaal: Uppaal): Seq[HornClause] = uppaal.automata.map{ aut =>
    autInitClause(uppaal, aut)
  }
  
  
  /**
   * clauses corresponding to assertions
   */
  def assertCls(uppaal: Uppaal): Seq[HornClause] = uppaal.automata.map{ aut =>
      aut.errors.map{ errState =>
        HornClause(Interp(BoolConst(false)),
          uppaal.automata.map(automaton => 
            RelVar(automaton.name,Parameter("c",IntegerType()) ::
              uppaal.clocks.map(Parameter(_,IntegerType())) ++
              uppaal.intVars.map(Parameter(_,IntegerType())) ++
              (0 until uppaal.automata.size).map(i => Parameter("t" + i,IntegerType())))
          ).toList :+ 
          Interp(Equality(
            Variable("t" + uppaal.automatonToNum(aut.name)).stype(IntegerType()),
            NumericalConst(aut.stateToNum(errState)))
          )
        )
      }
    }.flatten
  
  /**
   * local transitions of an automaton
   */
  def autLocalCls(uppaal: Uppaal, aut: UppAutomaton) : Seq[HornClause] = aut.states.map{ vertex =>
      aut.transitions.getOrElse(vertex,Set()).map{ _ match {
        case UppTransition(dest, None, assign, guard) => // local transitions
          val (clockAssign,dataAssign) = separateDataClock(assign,uppaal.clocks)
          instantaneousTransition(
            uppaal,
            aut,
            dest,
            List((aut,vertex)),
            Map(uppaal.automatonToNum(aut.name) -> aut.stateToNum(dest)),
            clockAssign,
            dataAssign,
            guard,
            aut.invariants.getOrElse(dest,BoolConst(true))
          )
        case UppTransition(dest, Some(_), assigns, guard) => // concurrency
          List()
      }}.flatten
    }.flatten.toList
    
  /**
   * local transitions of all the automata in the system
   */
  def localCls(uppaal: Uppaal): Seq[HornClause] = uppaal.automata.map{ aut => autLocalCls(uppaal, aut)}.flatten

  
  def individualClauses(uppaal: Uppaal, toAbs: Boolean = false): (Seq[HornClause], collection.immutable.Map[String, AbsLattice]) = {
    //############# different type of Horn clauses #############     
    var delayCls      = List[HornClause]()        //  delay clauses
    var invariantCls  = List[HornClause]()        //  invariant clauses
    var absMap        = collection.mutable.Map[String, AbsLattice]()
    var selfLoc       = 0

    //##########################################################
    uppaal.automata.foreach{aut =>
      //val ar = 1 + uppaal.clocks.size + uppaal.intVars.size + uppaal.automata.size
      //val rb = createRelation(aut.name, 1 + uppaal.clocks.size + uppaal.intVars.size + uppaal.automata.size)
      //println("\n\nAut: " + uppaal.automatonToNum(aut.name))

      if(toAbs)
        absMap += (aut.name -> createAbstractionPredicate(uppaal.clocks.size, uppaal.intVars.size, uppaal.automata.size, selfLoc))

      selfLoc += 1

      val delayHead = RelVar(aut.name, Parameter("c2",IntegerType()) :: 
        uppaal.clocks.map(Parameter(_,IntegerType())) ++
        uppaal.intVars.map(Parameter(_,IntegerType())) ++
        (0 until uppaal.automata.size).map(i => Parameter("t" + i,IntegerType())))
      if(aut.invariants.isEmpty){
        delayCls ::= HornClause(delayHead,
          List(
            Interp(GreaterThanEqual(Variable("c2").stype(IntegerType()),Variable("c1").stype(IntegerType()))),
              RelVar(aut.name, Parameter("c1",IntegerType()) :: 
              uppaal.clocks.map(Parameter(_,IntegerType())) ++
              uppaal.intVars.map(Parameter(_,IntegerType())) ++
              (0 until uppaal.automata.size).map(i => Parameter("t" + i,IntegerType())))
          )
        )
      }

      aut.states.foreach{vertex =>
        if(!aut.invariants.isEmpty) aut.invariants.get(vertex) match {
          case Some(inv) => 
            invariantCls ::= HornClause(delayHead,
              List(
                Interp(GreaterThanEqual(Variable("c2").stype(IntegerType()),Variable("c1").stype(IntegerType()))),
                Interp(offset(inv,Variable("c2").stype(IntegerType()),uppaal.clocks)),
                Interp(Equality(Variable("t" + uppaal.automatonToNum(aut.name)).stype(IntegerType()),NumericalConst((aut.stateToNum(vertex))))),
                RelVar(aut.name, Parameter("c1",IntegerType()) :: 
                  uppaal.clocks.map(Parameter(_,IntegerType())) ++
                  uppaal.intVars.map(Parameter(_,IntegerType())) ++
                  (0 until uppaal.automata.size).map(i => Parameter("t" + i,IntegerType())))
              )
            )
          case None =>
            if(!aut.errors.contains(vertex)) 
              delayCls ::= HornClause(delayHead,
                List(
                  Interp(GreaterThanEqual(Variable("c2").stype(IntegerType()),Variable("c1").stype(IntegerType()))),
                  Interp(Equality(Variable("t" + uppaal.automatonToNum(aut.name)).stype(IntegerType()),NumericalConst(aut.stateToNum(vertex)))),
                  RelVar(aut.name, Parameter("c1",IntegerType()) :: 
                    uppaal.clocks.map(Parameter(_,IntegerType())) ++
                    uppaal.intVars.map(Parameter(_,IntegerType())) ++
                    (0 until uppaal.automata.size).map(i => Parameter("t" + i,IntegerType())))
                )
              )
        }
      }  // vertex
    }
    
    val costs = if (toAbs) collection.immutable.Map() ++ absMap else collection.immutable.Map[String, AbsLattice]()
    //println("### These are the assertion transitions: ###\n" + assertCls(uppaal).map(lazabs.viewer.HornPrinter.printDebug(_)).mkString("\n\n") + "\n######")
    ( (initCls(uppaal) ++                    //  Initialization clauses
    localCls(uppaal)  ++                     //  local transition clauses      
    assertCls(uppaal) ++                     //  Assertion clauses
    (delayCls ++ invariantCls).map{cl => 
      HornClause(cl.head,
        cl.body ++ uppaal.intVars.intersect(uppaal.chans).map{chan =>
          Interp(Equality(Variable(chan).stype(IntegerType()),NumericalConst(0)))
        }
      )
    }), costs )
  }
}
