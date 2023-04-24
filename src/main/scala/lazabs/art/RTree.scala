/**
 * Copyright (c) 2011-2015 Hossein Hojjat, Philipp Ruemmer. All rights reserved.
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

package lazabs.art

import scala.reflect._
import scala.beans.BeanProperty

import lazabs.ast.ASTree._
import lazabs.cfg._
import lazabs.types._
import lazabs.utils.Manip._
import lazabs.prover.Prover._


object SearchMethod extends Enumeration {
  type SearchMethod = Value
  val DFS, BFS, PRQ, RND = Value
}
case class RNode(id:Int, cfgId: Int, abstraction: Set[Expression]) {	
  def getAbstraction = abstraction
  def getId = id
  def getCfgId = cfgId
}
case class RAdjacent(label: Label, to: RNode)
class RTree{
  @BeanProperty var start:RNode = _
  @BeanProperty var transitions:collection.mutable.Map[RNode,Set[RAdjacent]] = collection.mutable.Map.empty
  @BeanProperty var parent: Map[RNode,(RNode,Label)] = Map.empty   
  @BeanProperty var blockedNodes:Set[RNode] = Set()
  @BeanProperty var errorNodes:Set[RNode] = Set()
  @BeanProperty var cacheSubsumedNodes:Set[RNode] = Set()
  @BeanProperty var subsumptionRelation:Map[RNode,Set[RNode]] = Map.empty   // map from the weaker node to the set of stronger nodes it subsumes
}

object RTreeMethods {  
  /**
   * used for calculating the total time of computation
   */
  var timeStart: Long = 0
  var timeFinish: Long = 0
  var started = false
  def startTimer {
    if(started == false) {
      started = true
      timeStart = System.currentTimeMillis
    }
  }
  
  def stopTimer {
    timeFinish = System.currentTimeMillis
  }
  
  /**
   * each node in the reachability tree has a unique ID
   */
  private var curNodeID = -1
  def freshNodeID = {
    curNodeID = curNodeID + 1
    curNodeID
  }
  
  /**
   * converts a set of expression to an expression
   */
  def exprSetToFormula(se: Set[Expression]): Expression = se.size match {
    case 0 => BoolConst(true)
    case 1 => se.head
    case _ => if(se.contains(BoolConst(false))) BoolConst(false) else 
      se.reduceLeft[Expression](Conjunction(_,_))
  }
  
  /**
   * Determines if abs1 is a subset of abs2
   */  
  def subset(abs1: List[Boolean], abs2: List[Boolean]): Boolean = abs1.zip(abs2).map(x => (!x._1 || x._2)).foldLeft(true)((a,b) => a && b)
  
  /**
   * determines if the new state is subsumed with a previous one
   * there are two levels of checking
   * 1- syntactic: subset checking
   * 2- semantic: checking the logical implication
   * @param node the current vertex
   * @param abs the new abstraction
   * @return the node that subsumes abs (if any) 
   */
  def alreadyExplored(node: CFGVertex, nodeHash: collection.mutable.Map[CFGVertex,Set[RNode]], abs: Set[Expression]): Option[RNode] = nodeHash.get(node) match {
    case Some(as) =>
      val syntatic = as.find(a => a.getAbstraction.subsetOf(abs))
      if(syntatic.isDefined) syntatic else {
        // semantic check is the reverse of the syntactic check
        // the implication p /\ q --> p is correct since {p} \in {p,q}. 
        as.zip(as.map(a => (isSatisfiable(Conjunction(exprSetToFormula(abs),Not(exprSetToFormula(a.getAbstraction))))))).find(_._2 == Some(false)) match {
          case Some(ar) => Some(ar._1)
          case None => None
        }
      }
    case None => None
  }
  
  /**
   * inputs a vertex and prints its invariant
   */
  def printInvariant(vertex: CFGVertex, nodeHash: collection.mutable.Map[CFGVertex,Set[RNode]]) = nodeHash.get(vertex) match {
    case Some(fs) => println("The loop invariant " + lazabs.viewer.ScalaPrinter(fs.map(x => exprSetToFormula(x.getAbstraction)).reduceLeft(Disjunction(_,_))))
    case None => 
  }  
  
  /**
   * gets a predicate abstraction and returns its corresponding predicates
   */
  def absToPredSet(abst: List[Boolean], predicates: List[Expression]): Set[Expression] = {
    val raw = abst.zip(predicates).filter(e => e._1).map(_._2)
    val ps = if(raw.contains(BoolConst(false))) Set(BoolConst(false)) else raw  
    if(!ps.isEmpty) Set() ++ (ps.map(shortCircuit)) else Set()
  }
  
  def report {
    println("Total time for constructing the reachability tree: " + (timeFinish - timeStart) + " milli-seconds")  
    println("Total number of theorem prover consultation for constructing the reachability tree: " + getTheoremProverConsultation)
    println("Total number of theorem prover consultation for refining the abstraction: " + getInterpolationConsultation)
    println("Hit rate in formula cache: " + ((getHitCount * 100) / (getHitCount + getTheoremProverConsultation)) + " percent")
    println("Hit rate in state cache: " + ((MakeRTreeInterpol.cacheReuse  * 100) / curNodeID))
    if(MakeRTreeInterpol.accelerate) println("Successful exact approximation: " + getExactAccelerationCount)
    if(MakeRTreeInterpol.accelerate) println("Successful overapproximation: " + getsuccessfulOverAcceleration)
    if(MakeRTreeInterpol.accelerate) println("Unsuccessful overapproximation: " + getunsuccessfulOverAcceleration)
    //println("Number of states in reachability tree: " + (curNodeID + 1))
  }
  
  def report(loops: List[CFGVertex], nodeHash: collection.mutable.Map[CFGVertex,Set[RNode]]) {
    loops.foreach(printInvariant(_,nodeHash))
    report
  }
  
  /**
   * counting the number of exact accelerations
   */
  private var exactAcceleration = 0
  def exactAcc {
    exactAcceleration += 1
  }
  def getExactAccelerationCount = exactAcceleration
  
  /**
   * counting the number of successful over-approximated accelerations
   */
  private var successfulOverAcceleration = 0
  def successfulOverAcc {
    successfulOverAcceleration += 1
  }
  def getsuccessfulOverAcceleration = successfulOverAcceleration
  
  /**
   * counting the number of unsuccessful over-approximated accelerations
   */
  private var unsuccessfulOverAcceleration = 0
  def unsuccessfulOverAcc {
    unsuccessfulOverAcceleration += 1
  }
  def getunsuccessfulOverAcceleration = unsuccessfulOverAcceleration  
  
  /**
   * finds the path to root
   */
  def pathToRoot(node: RNode, parent: Map[RNode,(RNode,Label)]): List[(RNode,Label)] = {
    var path: List[(RNode,Label)] = List()
    def recur(n: RNode) { parent.get(n) match {
      case Some((pNode,label)) =>
        path ::= (pNode,label)
        recur(pNode)
      case None =>
    }}
    recur(node)
    path
  }
  
  /**
   * determines if a counter-example is spurious
   * returns the smallest infeasible suffix of the path
   */
  def isSpurious(errorNode: RNode, parent: Map[RNode,(RNode,Label)], getFormula: (RNode,RNode,Label) => Expression , init: List[(Variable,Expression)]): (Boolean,List[(RNode,Label)]) = {
    var path: List[(RNode,Label)] = List()
    var height = 0 // versions of the variables for NTS files
    def spur(node: RNode, condition: Expression): Boolean = parent.get(node) match {
      case Some((pNode,label)) =>
        //println("The predicate " + lazabs.viewer.ScalaPrinter(wp(condition, label)) + " label " + lazabs.viewer.ScalaPrinter(label))
        isSatisfiable(Not(condition)) match {
          case Some(false) =>
            return true   // the state cannot reach error
          case _ =>
            path ::= (pNode,label)
            val fm = getFormula(pNode,node,label)
            val v = putVersion(fm, height, false)
            height += 1
            spur(pNode, Disjunction(Not(v),condition))
          }
      case None =>
        //println("The last formula for checking " + lazabs.viewer.ScalaPrinter(init.map(x => lazabs.cfg.Assign(x._1,x._2): Label).foldLeft(condition)((a,b) => wp(a, b))))
        if(!init.isEmpty) {
          path ::= (RNode(-1, -1, Set[Expression]()),init.map(x => lazabs.cfg.Assign(x._1, x._2)).reduceLeft[Label]((a,b) => Sequence(a,b)))
          val vInit = putVersion(init.map(x => Equality(Variable(x._1.name + "'",None).stype(x._1.stype),x._2)).reduceLeft(Conjunction(_,_)), height, false)
          isSatisfiable(Conjunction(vInit,Not(condition))) match {
            case Some(false) => return true   // the state cannot reach error
            case _ =>
          }
        }
        isSatisfiable(Not(condition)) match {
          case Some(false) => return true   // the state cannot reach error
          case _ =>
        }
        return false
    }
    val result = spur(errorNode,BoolConst(false))
    (result,path)
  }
  
  /**
   * Given the current abstraction and the transition, computes the next abstraction
   * @param cur the current abstraction 
   * @param l the label on the CFG transition
   * @param predicates: the predicates on the next CFG vertex
   */
  def nextState(cur: Expression, predicates: List[(Expression,List[Int])], transition: Expression): List[Boolean] = {
    //println("@@@@@@@  This is the label: " + lazabs.viewer.ScalaPrinter(transition))
    var result = List[Boolean]()
    predicates.foreach( p => {
      val curPred = prime(p._1)
      val subsumption: Boolean = (if(p._2.size != 0) p._2.map(i => result(i)).reduceLeft(_||_) else false)
      result = result ::: (if(curPred == Variable("sc_LBE'",None) || subsumption) List(false) else
        lazabs.prover.Prover.isSatisfiable(Conjunction(Conjunction(cur,transition),Not(curPred))) match {      // This is the negation of: forall. curAbsFormula /\ transition -> p
          case Some(false) => List(true)
          case _ => List(false)
      })
    })
    result
  }
}

