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

package lazabs.art

import lazabs.ast.ASTree._
import lazabs.types._
import lazabs.cfg._
import lazabs.utils.Manip._
import lazabs.utils.Inline._
import lazabs.art.RTreeMethods._
import lazabs.prover.Prover._


object MakeRTree {
  var rTree: RTree = new RTree
  var cfg = CFG(CFGVertex(-1),Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,None)
  
  /**
   * The search method for exploration of reachability tree
   */
  import SearchMethod._
  var search: SearchMethod = DFS
  var shuffle: Boolean = false
  /**
   * check the counter-example for spuriousness or not 
   */
  var spuriousness = false
  /**
   * initial values of global variables
   */
  var init: List[(Variable,Expression)] = List()
  /**
   * used for calculating the total time of computation
   */
  var time: Long = 0
  
  /**
   * Gets a Scala object and generates the reachability tree for the main function
   * @param o object ast
   * @param start the beginning vertex
   * @param loops the vertices that start a loop
   * @param adj the adjacency list
   */    
  def apply(cfg: CFG, loops: List[CFGVertex], spuriousness: Boolean, search: SearchMethod, shuffle: Boolean): RTree = {
    this.cfg = cfg
    this.spuriousness = spuriousness
    this.search = search
    this.shuffle = shuffle
    startTimer
    var initialAbstraction: List[Boolean] = Nil
    cfg.sobject match {
      case Some(so) => 
        this.init = MakeCFG.initialValues(so)
        val initForm = init.map(x => Equality(x._1, x._2)).foldLeft[Expression](BoolConst(true))(Conjunction(_,_))
        MakeCFG.initialPredicates(so).head.map(_._1).foreach(p => initialAbstraction = initialAbstraction ::: (isSatisfiable(Conjunction(initForm,Not(p))) match {
          case Some(false) => List(true)
          case _ => List(false)
        }))
      case None =>
    }
    search match {
      case DFS => rTree.start = makeRTreeDFS(cfg.start, initialAbstraction)
      case _ => makeRTreeQueue(cfg.start, initialAbstraction)
    }
    checkFailedAssertion
    report(loops,nodeHash)
    rTree
  }
  /**
   * the hash of nodes
   */
  var nodeHash = collection.mutable.Map[CFGVertex,Set[RNode]]().empty  
  /**
   * Making a reachability tree for a given control flow graph with DFS method
   */  
  def makeRTreeDFS(vertex: CFGVertex, predAbs: List[Boolean]): RNode = {
    val currentPredSet = absToPredSet(predAbs, cfg.predicates.getOrElse(vertex,List()).map(_._1))
    val currentFormula = exprSetToFormula(currentPredSet)
    val node = RNode(freshNodeID, vertex.id, currentPredSet)
    if (vertex.id == -1) currentFormula match {
      case BoolConst(b) if (b == false) =>
        rTree.blockedNodes += node
        return node
      case _ =>        
        rTree.errorNodes += node
        return node
    }
    if (currentPredSet.contains(BoolConst(false))) { // the set is empty - the predicate false is true in this state
      rTree.blockedNodes += node
      return node
    }
    (alreadyExplored(vertex, nodeHash, currentPredSet) match {
      case Some(weaker) => 
        rTree.subsumptionRelation += (weaker -> (rTree.subsumptionRelation.getOrElse(weaker,Set()) + node))
        return node
      case None =>
    })
    nodeHash += (vertex -> (nodeHash.getOrElse(vertex, Set()) + node))      
    cfg.transitions.get(vertex) match {
      case Some(adjacencies) =>
        val adjs: List[CFGAdjacent] = if(shuffle) scala.util.Random.shuffle(adjacencies).toList else adjacencies.toList.sortWith((e1, e2) => (e1.to.getId < e2.to.getId))
        adjs.foreach(adj => {
          val (transition,nvars,_) = transFormula(adj.label,cfg.variables.getOrElse(adj.to, Set()))
          val childAbs: List[Boolean] = nextState(currentFormula, cfg.predicates.getOrElse(adj.to, List()), transition)
          val childNode = makeRTreeDFS(adj.to, childAbs)
          rTree.parent += (childNode -> (node,adj.label))
          rTree.transitions += (node -> (rTree.getTransitions.getOrElse(node,Set.empty) ++ Set(RAdjacent(adj.label,childNode))))
        })
        node
      case None =>
        node
    }
  }
  
  /**
   * Making a reachability tree for a given control flow graph with BFS method
   */  
  def makeRTreeQueue(startVertex: CFGVertex, startPredAbs: List[Boolean]) {
    val startPredSet = absToPredSet(startPredAbs, cfg.predicates.getOrElse(startVertex,List()).map(_._1))
    val startFormula = exprSetToFormula(startPredSet)
    rTree.start = RNode(freshNodeID, startVertex.id, startPredSet)
    var queue: List[(CFGVertex,RNode,List[Boolean])] = List((startVertex,rTree.start,startPredAbs))  // CFG vertex, Reachability node, predicate vector
    while(queue.size != 0) {
      val next = search match {
        case PRQ =>
          queue.minBy(_._3.count(identity))
          //scala.util.Random.shuffle(queue).minBy(_._3.count(identity))
        case RND =>
          scala.util.Random.shuffle(queue).head          
        case _ =>
          queue.head
      }
      cfg.transitions.get(next._1) match {
        case Some(adjacencies) =>
          val adjs: List[CFGAdjacent] = if(shuffle) scala.util.Random.shuffle(adjacencies).toList else adjacencies.toList.sortWith((e1, e2) => (e1.to.getId < e2.to.getId)) 
            adjs.foreach(adj => {
            val (transition,nvars,_) = transFormula(adj.label,cfg.variables.getOrElse(adj.to,Set()))
            val childAbs: List[Boolean] = nextState(exprSetToFormula(next._2.getAbstraction), cfg.predicates.getOrElse(adj.to, List()), transition)
            val childPredSet = absToPredSet(childAbs, cfg.predicates.getOrElse(adj.to,List()).map(_._1))
            val childFormula = childPredSet.reduceLeft[Expression](Conjunction(_,_))
            val childNode = RNode(freshNodeID, adj.to.id, childPredSet)
            if(adj.to.id == -1) childFormula match {  // assertions
              case BoolConst(false) =>
                rTree.blockedNodes += childNode
                nodeHash += (adj.to -> (nodeHash.getOrElse(adj.to, Set()) + childNode))
              case _ =>
                rTree.errorNodes += childNode
            } else alreadyExplored(adj.to, nodeHash, childPredSet) match {
              case Some(weaker) => rTree.subsumptionRelation += (weaker -> (rTree.subsumptionRelation.getOrElse(weaker,Set()) + childNode))
              case None =>
                if(childAbs.head) {  // the set is empty - the predicate false is true in this state
                //nodeHash = nodeHashUnion(nodeHash, collection.mutable.Map(adj.to -> List(childPredSet)))
                  rTree.blockedNodes += childNode
                } else {
                  nodeHash += (adj.to -> (nodeHash.getOrElse(adj.to, Set()) + childNode))
                  val dups = queue.filter(x => x._1 == adj.to)   // there is already a node for the same CFG vertex in the queue
                  if(dups.size != 0)
                    dups.foreach(d => if(subset(childAbs,dups.head._3)) queue = queue.filterNot(_ == d))              
                  queue :+= (adj.to,childNode,childAbs)
                }
            }
            rTree.transitions += (next._2  -> (rTree.transitions.getOrElse(next._2, Set.empty) ++ Set(RAdjacent(adj.label,childNode))))
            rTree.parent += (childNode -> (next._2,adj.label))
          })
        case None =>
      }
      queue = queue.filterNot(_ == next)
    }
  }
  
  def getFormula(start: RNode, end: RNode, label: Label): Expression = cfg.getFormula(CFGVertex(start.getCfgId),CFGVertex(end.getCfgId),label)  
 
  def checkFailedAssertion {
    rTree.errorNodes.foreach(f => {
      var errorMessage = "The assertion in node ERROR(" + lazabs.viewer.ScalaPrinter(exprSetToFormula(f.getAbstraction)) + ") can fail" 
      (if(spuriousness) {
        val spur = isSpurious(f, rTree.parent, getFormula, init)
        errorMessage = errorMessage + (if(spur._1) ", the counter example is spurious: more predicates required."
            else ", the counter example is genuine. The program has a bug.")
      })
      println(errorMessage)
    })
    stopTimer
  }
}