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
import lazabs.cfg._


object NtsCFG {
  var nts:Nts = Nts("",List(),List[NtsSubsystem]()) 
  var adjMap = Map[CFGVertex,Set[CFGAdjacent]]().empty
  var varsMap = Map[CFGVertex,Set[Variable]]().empty
  var formulas = Map[(CFGVertex,CFGVertex),Expression]().empty
  var predicates = Map[CFGVertex,List[(Expression,List[Int])]]().empty
  /**
   The variables in the system in which all the called subsystems are inlined 
   */
  var allVariables = List[Variable]()
  
  // each time a method is inlined its states should get fresh ids 
  // smap is a mapping from the (original state id * inline number)  --> fresh number
  def freshState(i: Int, inlineNum: Int, smap: Map[(Int,Int),Int]): (Int,Map[(Int,Int),Int]) = {
    if(i == -1) (i,smap) else smap.get(i,inlineNum) match {
      case Some(v) => (v,smap)
      case None => 
        val fresh = FreshCFGStateId.apply
        NtsWrapper.stateNameMap += (fresh -> (NtsWrapper.stateNameMap.getOrElse(i,"") + "_" + inlineNum + "_"))
        (fresh,smap + ((i,inlineNum) -> fresh))
    }
  }
  /**
   * puts the current inline number after the variable name 
   */
  def putInlineNum(e: Expression, inlineNum: Int): Expression = e match {
    case v@Variable(name,d) if (name.endsWith("'") && !nts.globalVars.contains(removePrime(v))) =>
      Variable((if(name.startsWith("sc_")) name.init.drop(3) else name.init) + inlineNum + "'",d).stype(e.stype)
    case v@Variable(name,d) if (!nts.globalVars.contains(removePrime(v))) =>
      Variable((if(name.startsWith("sc_")) name.drop(3) else name) + inlineNum,d).stype(e.stype)
    case UnaryExpression(op, e) => UnaryExpression(op, putInlineNum(e,inlineNum)).stype(e.stype)
    case BinaryExpression(e1, op, e2) => BinaryExpression(putInlineNum(e1,inlineNum), op, putInlineNum(e2,inlineNum)).stype(e.stype)
    case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, putInlineNum(e1,inlineNum), putInlineNum(e2,inlineNum), putInlineNum(e3,inlineNum)).stype(e.stype)
    case _ => e
  }
  
  /**
   * removes prime from the variable 
   */
  def removePrime(v: Variable): Variable = v match {
    case Variable(name,d) if (name.endsWith("'")) => Variable(name.init).stype(v.stype)
    case _ => v
  }
  
  def inline(call: NTSCall, funCallSource: Int, funCallTarget: Int, inlineNum: Int) {
    inlineCount += 1
    if (!nts.systems.exists(_.name == call.calleeName)) {
      println("No matching call: " + call.calleeName)
      sys.exit(0)
    }
    val callee = nts.systems.find(_.name == call.calleeName).head
    var stateIdFresh = Map[(Int,Int),Int]().empty
    allVariables ++=  callee.vars.diff(nts.globalVars).map(x => (putInlineNum(x,inlineNum).asInstanceOf[Variable]))
    val inputf = if (callee.inputVars.size > 0) (allVariables.diff(callee.inputVars.map(putInlineNum(_,inlineNum)))).zip(allVariables.diff(callee.inputVars.map(putInlineNum(_,inlineNum))).map(lazabs.utils.Manip.prime(_))).map(x => Equality(x._1,x._2))
        .foldLeft(callee.inputVars.map(x => lazabs.utils.Manip.prime(putInlineNum(x,inlineNum).asInstanceOf[Variable])).zip(call.actualParameters).map(x => Equality(x._1,x._2)).reduceLeft(Conjunction(_,_)))((a,b) => Conjunction(a,b))
    else
      (allVariables.zip(allVariables.map(lazabs.utils.Manip.prime(_))).map(x => Equality(x._1,x._2))).reduceLeft(Conjunction(_,_))
    val outputf = if (callee.outputVars.size > 0) Conjunction(call.returnVars.map(_.stype(lazabs.types.IntegerType())).zip(callee.outputVars.map(putInlineNum(_,inlineNum).asInstanceOf[Variable])).map(x => Equality(x._1,x._2)).reduceLeft(Conjunction(_,_)),
      (call.havoc match {
        case Some (h) => (allVariables.diff(call.returnVars.map(removePrime) ++ h.map(putInlineNum(_,inlineNum).asInstanceOf[Variable])).zip(allVariables.diff(call.returnVars.map(removePrime) ++ h.map(putInlineNum(_,inlineNum).asInstanceOf[Variable])).map(lazabs.utils.Manip.prime(_)))).map(x => Equality(x._1,x._2)).reduceLeft(Conjunction(_,_))
        case None => (allVariables.diff(call.returnVars.map(removePrime))).zip(allVariables.diff(call.returnVars.map(removePrime)).map(lazabs.utils.Manip.prime(_))).map(x => Equality(x._1,x._2)).reduceLeft(Conjunction(_,_))
      }))
    else
      (allVariables.zip(allVariables.map(lazabs.utils.Manip.prime(_))).map(x => Equality(x._1,x._2))).reduceLeft(Conjunction(_,_))
    // entrance to the inlined function  
    callee.initStates.foreach{init => 
      val (s,m) = freshState(init,inlineNum, stateIdFresh) // the source
      stateIdFresh  = m
      adjMap = addMultiMap(adjMap,(CFGVertex(funCallSource) -> CFGAdjacent(Transfer(inputf), CFGVertex(s))))
      formulas += ((CFGVertex(funCallSource),CFGVertex(s)) -> inputf)
      predicates += (CFGVertex(s) -> List((BoolConst(false),List()),(Variable("sc_LBE"),List())))
    }
    // exit from the inlined function
    callee.finalStates.foreach{fin =>
      val (t,m) = freshState(fin,inlineNum, stateIdFresh) // the target
      stateIdFresh  = m
      adjMap = addMultiMap(adjMap,(CFGVertex(t) -> CFGAdjacent(Transfer(outputf), CFGVertex(funCallTarget))))
      formulas += ((CFGVertex(t),CFGVertex(funCallTarget)) -> outputf)
      predicates += (CFGVertex(t) -> List((BoolConst(false),List()),(Variable("sc_LBE"),List())))
    }
    callee.transitions.foreach{cat =>
      val (s,m1) = freshState(cat.source,inlineNum, stateIdFresh) // the source
      stateIdFresh  = m1
      val (t,m) = freshState(cat.target,inlineNum, stateIdFresh) // the target
      stateIdFresh  = m
      cat.formula match {
      case n@NTSCall(cName, actualParameters, returnVars, havoc) =>
        inline(NTSCall(cName, actualParameters.map(putInlineNum(_,inlineNum)), returnVars.map(putInlineNum(_,inlineNum).asInstanceOf[Variable]), (havoc match {
          case Some(l) => Some(l.map(putInlineNum(_,inlineNum).asInstanceOf[Variable]))
          case None => None
        })), s, t,inlineCount)
      case _ =>
        val locallyChangableVariables = callee.vars.map(putInlineNum(_,inlineNum).asInstanceOf[Variable])
        val localf = (allVariables.diff(locallyChangableVariables).zip(allVariables.diff(locallyChangableVariables)
            .map(lazabs.utils.Manip.prime(_)))).map(x => Equality(x._1,x._2)).foldLeft[Expression](putInlineNum(cat.formula,inlineNum))(Conjunction(_,_))
        adjMap = addMultiMap(adjMap,(CFGVertex(s) -> CFGAdjacent(Transfer(localf), CFGVertex(t))))
        formulas += (CFGVertex(s),CFGVertex(t)) -> (formulas.get((CFGVertex(s),CFGVertex(t))) match {
          case Some(pv) => Disjunction(localf,pv)
          case None => localf
        })
        varsMap += (CFGVertex(s) -> (Set() ++ allVariables))
        varsMap += (CFGVertex(t) -> (Set() ++ allVariables))
        predicates += (CFGVertex(s) -> List((BoolConst(false),List()),(Variable("sc_LBE"),List())))
        predicates += (CFGVertex(t) -> List((BoolConst(false),List()),(Variable("sc_LBE"),List())))
      }
    }
    allVariables =  allVariables filterNot (callee.vars.diff(nts.globalVars).map(x => (putInlineNum(x,inlineNum).asInstanceOf[Variable])) contains)
  }
  
  /**
   * count the number of inlining 
   */
  var inlineCount = 0
  
  /**
   * adding two multi-maps and returning the result
   */
  def addMultiMap(l:Map[CFGVertex,Set[CFGAdjacent]], r:Tuple2[CFGVertex,CFGAdjacent]):Map[CFGVertex,Set[CFGAdjacent]] = l.get(r._1) match {
    case Some(s) =>
      (s.find(_.to == r._2.to)) match{
        case Some(adj) => l.updated(r._1,s.filter(_.to != r._2.to) + CFGAdjacent(Transfer(Disjunction(adj.label.asInstanceOf[Transfer].t,r._2.label.asInstanceOf[Transfer].t)),r._2.to))
        case None => l.updated(r._1,s + r._2)
      }
    case None => l + (r._1 -> Set(r._2))
  }
  
  /**
   * Gets an Nts and generates the control flow graph for the main function 
   */
  def apply(nts: Nts, lbe: Boolean, accelerate: Boolean): CFG = {
    this.nts = nts
    if (!nts.systems.exists(_.name == "main")) {
      println("No main method in NTS")
      sys.exit(0)
    }
    val mainSystem = nts.systems.find(_.name == "main").head
    allVariables = mainSystem.vars  // initialize allVariables to the variables defined in the main subsystem
    mainSystem.transitions.foreach(nt => {
      nt.formula match {
        case n@NTSCall(_,_,_,_) =>
          inline(n, nt.source, nt.target,inlineCount)
        case _ =>
          val f = allVariables.diff(mainSystem.vars).zip(allVariables.diff(mainSystem.vars).map(lazabs.utils.Manip.prime(_))).map(x => Equality(x._1,x._2))
            .foldLeft(nt.formula)((a,b) => Conjunction(a,b))
          adjMap = addMultiMap(adjMap,(CFGVertex(nt.source) -> CFGAdjacent(Transfer(f), CFGVertex(nt.target))))
          formulas += (CFGVertex(nt.source),CFGVertex(nt.target)) -> (formulas.get((CFGVertex(nt.source),CFGVertex(nt.target))) match {
            case Some(pv) =>
              Disjunction(f,pv)
            case None => f
          })
      }
      varsMap += (CFGVertex(nt.source) -> (Set() ++ allVariables))
      varsMap += (CFGVertex(nt.target) -> (Set() ++ allVariables))
      predicates += (CFGVertex(nt.source) -> List((BoolConst(false),List()),(Variable("sc_LBE"),List())))
      predicates += (CFGVertex(nt.target) -> List((BoolConst(false),List()),(Variable("sc_LBE"),List())))
    })
    if(lbe) CFGTransform(CFG(CFGVertex(mainSystem.initStates.head),adjMap,MakeCFG.makeParentMap(adjMap),predicates,varsMap,formulas,Map.empty,None),false,accelerate)
    else
      CFG(CFGVertex(mainSystem.initStates.head),adjMap,MakeCFG.makeParentMap(adjMap),predicates,varsMap,formulas,Map.empty,None)
  }
}