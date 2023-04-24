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

import lazabs.ast.ASTree._
import lazabs.cfg._
import lazabs.art.RTreeMethods._
import lazabs.refine._

object MakeRTreeInterpol {
  var rTree: RTree = new RTree
  var queue: List[RNode] = List()
  var cfg = CFG(CFGVertex(-1),Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,Map.empty,None)
  /**
   * The search method for exploration of reachability tree
   */
  import SearchMethod._
  var search: SearchMethod = DFS
  /**
   * Putting the interpolants in a log file
   */
  var log: Boolean = false
  /**
   * Dynamic acceleration
   */
  var accelerate: Boolean = false
  /**
   * under-approximation of loops
   */
  var underApproximate: Boolean = false  
  /**
   * use template-based refinement
   */
  var template: Boolean = false  
  /**
   * Rewriting a BAPA formula into Presburger
   */
  var bapaRewrite: Boolean = false
  /**
   * Dumping the interpolation queries into file
   */
  var dumpInterpolationQuery: Boolean = false
  def isDumpInterpolationQuery = dumpInterpolationQuery 
  /**
   * initial values of global variables
   */
  var init: List[(Variable,Expression)] = List()  
  /**
   * caching previous nodes
   */
  var reusableRoots = Set[RNode]()
  /**
   * mapping from CFG vertex to the set of predicates
   */
  var predMap = collection.mutable.Map[CFGVertex,List[(Expression,List[Int])]]().empty
  /**
   * if the program has a bug or not
   */
  var hasBug = false
 
  /**
   * Gets a control flow graph and generates the reachability tree
   * @param cfg control flow graph
   * @param loops the vertices that start a loop
   * @param log writes the abstraction information in a file when drawing reachability tree 
   */  
  def apply(cfg: CFG, loops: List[CFGVertex], search: SearchMethod, bapaRewrite: Boolean, dumpInterpolationQuery: Boolean, accelerate: Boolean, underApproximate: Boolean, template: Boolean, log: Boolean): RTree = {
    this.cfg = cfg
    this.search = search
    this.accelerate = accelerate
    this.underApproximate = underApproximate
    this.template = template
    this.log = log
    this.bapaRewrite = bapaRewrite
    this.dumpInterpolationQuery = dumpInterpolationQuery
    this.predMap = collection.mutable.Map() ++ cfg.predicates   // the predicates change during refinement
    cfg.sobject match {
      case Some(so) => init = MakeCFG.initialValues(so)
      case None =>
    }
    startTimer
    val startNode = constructARTNode(cfg.start,BoolConst(true))
    queue ::= startNode
    nodeHash += (cfg.start -> Set(startNode))
    rTree.setStart(startNode)
    makeRTree
    /*rTree.start = rTree.getTransitions.keys.find(_.cfgId == cfg.start.id) match {
      case Some(n) => n
      case None => RNode(-1,cfg.start.id,Set[Expression]().empty)
    }*/   
    checkFailedAssertion
    if(!hasBug)
      println("==================== No Error Found ====================")
    report(loops,nodeHash)
    rTree
  }
  /**
   * dumps the paths into a file
   */
  def dumpQuery(labels: List[Label]) {
    //println("The repetitive map: " + repetitivePath.map(x => lazabs.viewer.ScalaPrinter(x._2)))
//    val z3 = lazabs.prover.Z3Wrapper.createContext
//    labels.foreach {l => l match {
//      case Transfer(trans) => val formula = lazabs.prover.Z3Wrapper.mkZ3Expr(trans, z3)
      //println(z3.)
//      case TransitiveClosure(ls,_) => println("oh I have transitive closure")
//      case _ => println("Error in dumping")
//    }
      //val formula = lazabs.prover.Z3Wrapper.mkZ3Expr(e, z3)
//    }
  }
  
  /**
   * constructs a reachability node from the given vertex
   */
  def constructARTNode(st: CFGVertex, initAbs: Expression): RNode = {
    var initialAbstraction: List[Boolean] = Nil
    var currentPredicates = predMap.getOrElse(st,List((BoolConst(false),List())))
    var initForm: Expression = initAbs
    if(st == cfg.start) cfg.sobject match {
      case Some(so) =>
        initForm = init.map(x => Equality(x._1, x._2)).foldLeft[Expression](BoolConst(true))(Conjunction(_,_))
        currentPredicates = (currentPredicates ::: MakeCFG.initialPredicates(so).head).distinct
      case None =>
    }
    currentPredicates.map(_._1).foreach(p => initialAbstraction = initialAbstraction :::
      (if(p == Variable("sc_LBE",None)) List(false) else (lazabs.prover.Prover.isSatisfiable(Conjunction(initForm,Not(p))) match {
        case Some(false) => List(true)
        case _ => List(false)
    })))
    RNode(freshNodeID, st.id, absToPredSet(initialAbstraction, predMap.getOrElse(st,List()).map(_._1)))
  }
  
  var cacheReuse = 0
  /**
   * adds a subtree to the current reachability tree  
   */
  def addSubtree(root: RNode): Unit = {
    alreadyExplored(CFGVertex(root.getCfgId), nodeHash, root.getAbstraction) match {
      case Some(weaker) if(!rTree.getBlockedNodes.contains(root)) =>
        val explored = RNode(freshNodeID, root.getCfgId, root.getAbstraction)
        rTree.subsumptionRelation += (weaker -> (rTree.subsumptionRelation.getOrElse(weaker,Set()) + explored))
        rTree.getParent.get(root) match {
          case Some(papa) =>
            rTree.transitions = (rTree.transitions + (papa._1 -> (rTree.transitions.getOrElse(papa._1, Set.empty) + RAdjacent(papa._2,explored) - RAdjacent(papa._2,root)))).filterNot(_._2.size == 0)
            rTree.parent += (explored -> (papa._1,papa._2))          
          case None =>
        }
        pruneChildren(root)
        rTree.setTransitions(rTree.getTransitions - root)
        rTree.setParent(rTree.getParent - root)        
      case _ =>
        nodeHash += (CFGVertex(root.getCfgId) -> (nodeHash.getOrElse(CFGVertex(root.getCfgId), Set()) + root))
        cacheReuse += 1
        rTree.getTransitions.get(root) match {
          case Some(adjs) =>
            val cacheSubsumedAdjs = adjs.filter(adj => rTree.cacheSubsumedNodes.exists(_ == adj.to))
            if(cacheSubsumedAdjs.size != 0) {
              val cacheUnsubsumedAdjs = adjs.filterNot(adj => rTree.cacheSubsumedNodes.exists(_ == adj.to))
              rTree.transitions = (rTree.transitions + (root -> (rTree.transitions.getOrElse(root, Set.empty) -- cacheSubsumedAdjs))).filterNot(_._2.size == 0)
              cacheSubsumedAdjs.map(_.to).foreach{cSub =>
                rTree.cacheSubsumedNodes -= cSub
                rTree.parent -= cSub
              }
              cacheUnsubsumedAdjs.map(_.to).map(addSubtree)
              queue +:= root
            } else
              adjs.map(adj => addSubtree(adj.to))
          case None =>
            if(!rTree.getBlockedNodes.contains(root) && !rTree.cacheSubsumedNodes(root)) 
              queue :+= root
        }
    }
  }
  
  /**
   * the hash of nodes
   */
  var nodeHash = collection.mutable.Map[CFGVertex,Set[RNode]]().empty
  /**
   * Making a reachability tree for a given control flow graph
   */  
  def makeRTree {
    while(queue.size != 0 && rTree.errorNodes.size == 0) {
      val reusableRootsM = reusableRoots.map(_.getCfgId)
      val cur = queue.find(rr => !reusableRootsM.contains(rr.getCfgId)) match {
        case Some(n) => n
        case None => search match {
          case PRQ =>
            queue.minBy(_.getAbstraction.size)
          case RND =>
            scala.util.Random.shuffle(queue).head
          case _ =>
            queue.head
        }
      }
      cfg.transitions.get(CFGVertex(cur.getCfgId)) match {
        case Some(adjs) =>
          //val adjs: List[CFGAdjacent] = if(shuffle) scala.util.Random.shuffle(adjacencies).toList else adjacencies.toList.sortWith((e1, e2) => (e1.to.getId < e2.to.getId))
          val it = adjs.toList.iterator
          while(rTree.errorNodes.size == 0 && it.hasNext) {
            val adj = it.next
            if(rTree.transitions.get(cur) match {
                case Some(ina) => (if (ina.map(_.to.getCfgId).contains(adj.to.id)) false else true)
                case None => true}) {
              val childAbs: List[Boolean] = nextState(exprSetToFormula(cur.getAbstraction), predMap.getOrElse(adj.to, List()), cfg.getFormula(CFGVertex(cur.getCfgId),adj.to,adj.label))
              val childPredSet = absToPredSet(childAbs, predMap.getOrElse(adj.to,List()).map(_._1))
              val childFormula = exprSetToFormula(childPredSet)
              var childNode: RNode = if(childPredSet.contains(BoolConst(false))) {
                val blocked = RNode(freshNodeID, adj.to.id, childPredSet)
                rTree.blockedNodes += blocked
                nodeHash += (adj.to -> (nodeHash.getOrElse(adj.to, Set()) + blocked))
                blocked
              } else {
                if(adj.to.id == -1) {
                  val error = RNode(freshNodeID, adj.to.id, childPredSet)
                  rTree.errorNodes += error
                  error
                } else {
                  alreadyExplored(adj.to, nodeHash, childPredSet) match {
                    case Some(weaker) =>
                      val explored = RNode(freshNodeID, adj.to.id, childPredSet)
                      rTree.subsumptionRelation += (weaker -> (rTree.subsumptionRelation.getOrElse(weaker,Set()) + explored))
                      explored
                    case None =>
                      reusableRoots.find(rr => rr.getCfgId == adj.to.id && rr.getAbstraction == childPredSet) match {
                        case Some(reuse) =>
                          addSubtree(reuse)
                          reusableRoots -= reuse
                          reuse
                        case None =>
                          val unfinished = RNode(freshNodeID, adj.to.id, childPredSet)
                          nodeHash += (adj.to -> (nodeHash.getOrElse(adj.to, Set()) + unfinished))
                          val dups = queue.filter(x => x.getCfgId == adj.to.getId)   // there is already a node for the same CFG vertex in the queue
                          if(dups.size != 0) {
                            dups.foreach{d =>
                              //if(childPredSet.subsetOf(d.getAbstraction) && !(pathToRoot(cur, rTree.parent).map(_._1) :+ cur).contains(d)) { // does not work with caching
                              if(childPredSet.subsetOf(d.getAbstraction) && !(rTree.transitions.isDefinedAt(d))) {
                                queue = queue.filterNot(_ == d)
                                rTree.subsumptionRelation += (unfinished -> (rTree.subsumptionRelation.getOrElse(unfinished,Set()) + d))
                                //nodeHash = (nodeHash + (adj.to -> (nodeHash.getOrElse(adj.to,Set()) - d))).filterNot(_._2.size == 0)
                              }
                            }
                          }
                          queue :+= unfinished
                          unfinished
                      }
                  }
                }
              }
              rTree.transitions += (cur -> (rTree.transitions.getOrElse(cur, Set.empty) + RAdjacent(adj.label,childNode)))
              rTree.parent += (childNode -> (cur,adj.label))
            }
          }
        case None =>  // the node is final in the cfg
      }
      queue = queue.filterNot(_ == cur)
    }
  }
  
  /**
   * Prunes the reachability tree from the prune node
   * @post: Every children from prune are removed
   * @invariant: Does not change the subsumption relation
   */
  def pruneChildren(prune: RNode): Unit = {
    if(reusableRoots.contains(prune))
      return
    rTree.getTransitions.get(prune) match {
      case Some(s) =>
        rTree.setTransitions(rTree.getTransitions - prune)         
        s.foreach(ra => {
          queue = queue.filterNot(_ == ra.to)
          rTree.setParent(rTree.getParent - ra.to)
          //nodeHash = (nodeHash + (CFGVertex(ra.to.getCfgId) -> (nodeHash.getOrElse(CFGVertex(ra.to.getCfgId),Set()) - ra.to))).filterNot(_._2.size == 0)
          pruneChildren(ra.to)
        })
      case None =>
        rTree.setBlockedNodes(rTree.getBlockedNodes - prune)
        rTree.setErrorNodes(rTree.getErrorNodes - prune)
    }
  }
  
  /**
   * Adjusts the subsumption relation after pruning
   */
  def adjustSubsumption(mainTreeNodes: Set[RNode], cacheNodes: Set[RNode]) {
    // ############# marking the explored nodes in the cache nodes #############
    rTree.getSubsumptionRelation.map(el => (el._1,el._2.filter(cacheNodes.contains))).values.foldLeft(Set[RNode]())(_++_).foreach {cSub =>
      val os = RNode(freshNodeID, cSub.getCfgId, cSub.getAbstraction)
      rTree.cacheSubsumedNodes += os
      rTree.getParent.get(cSub) match {
        case Some(papa) =>
          rTree.transitions += (papa._1 -> (rTree.transitions.getOrElse(papa._1, Set.empty) + RAdjacent(papa._2,os) - (RAdjacent(papa._2,cSub))))
          rTree.parent += (os -> (papa._1,papa._2))
        case None =>
      }
      rTree.setTransitions(rTree.getTransitions - cSub)
      rTree.setParent(rTree.getParent - cSub)
    }
    // ############# removing those subsumed nodes in the main tree that are subsumed by the nodes in cache #############
    val mainPushBackNodes = rTree.getSubsumptionRelation.filter(el => !mainTreeNodes.contains(el._1))
      .map(el => (el._1,el._2.filter(mainTreeNodes.contains))).values.foldLeft(Set[RNode]())(_++_)
    mainPushBackNodes.foreach {mSub =>
      rTree.getParent.get(mSub) match {
        case Some(papa) =>
          rTree.transitions = (rTree.transitions + (papa._1 -> (rTree.transitions.getOrElse(papa._1, Set.empty) - (RAdjacent(papa._2,mSub))))).filterNot(_._2.size == 0)
          if(!queue.contains(papa._1))
            queue +:= papa._1
        case None =>
          sys.exit(0)
      }
      rTree.setParent(rTree.getParent - mSub)
      nodeHash = (nodeHash + (CFGVertex(mSub.getCfgId) -> (nodeHash.getOrElse(CFGVertex(mSub.getCfgId),Set()) - mSub))).filterNot(_._2.size == 0)             
    }
    rTree.setSubsumptionRelation(rTree.getSubsumptionRelation.filter(el => mainTreeNodes.contains(el._1)).map(el => (el._1,el._2.filter(mainTreeNodes.contains))).filter(_._2.size != 0))
    rTree.setSubsumptionRelation(rTree.getSubsumptionRelation.filter(el => !mainPushBackNodes.contains(el._1)).map(el => (el._1,el._2.filterNot(mainPushBackNodes.contains))).filter(_._2.size != 0))
  }
   
  /**
   * returns the roots of the directly connected subtree to the spurious path
   */
  def subtreesRoots(p: List[RNode]): Set[RNode] = p.map(rTree.getTransitions.get(_) match {
    case Some(adjs) => adjs.filterNot(x => (p.contains(x.to) || (x.to.getCfgId == -1) || (rTree.getSubsumptionRelation.values.foldLeft(Set[RNode]())(_++_).exists(_ == x.to)) || (rTree.getBlockedNodes.contains(x.to)))).map(_.to)
    case None => Set()
  }).foldLeft[Set[RNode]](Set())(_++_)
  
  /**
   * returns 
   * 1- every node in the subtree
   * 2- unfinished leaves
   */
  def allNodes(root: RNode): (Set[RNode],Set[RNode]) = rTree.getTransitions.get(root) match {
    case Some(adjs) =>
      val rest = adjs.map(adj => allNodes(adj.to))
      (Set(root) ++ rest.map(_._1).foldLeft[Set[RNode]](Set())(_ union _),
          (if(queue.contains(root)) Set(root) ++ rest.map(_._2).foldLeft[Set[RNode]](Set())(_ union _) else rest.map(_._2).foldLeft[Set[RNode]](Set())(_ union _)))
    case None =>
      if(!rTree.getBlockedNodes.contains(root) && !rTree.getSubsumptionRelation.values.foldLeft(Set[RNode]())(_++_).exists(_ == root))
        (Set(root),Set(root))
      else 
        (Set(root),Set())
  }
  
  /**
   * get formulas of a path leading to error
   */
  def getPathToErrorFormula(path: List[(RNode,Label)]): List[Expression] = {
    (path.zip(path.tail).map(el => getFormula(el._1._1,el._2._1,el._1._2)) :+ getFormula(path.last._1,rTree.errorNodes.head,path.last._2)).map(lazabs.utils.Manip.shortCircuit)    
  }
  
  def getFormula(start: RNode, end: RNode, label: Label): Expression = cfg.getFormula(CFGVertex(start.getCfgId),CFGVertex(end.getCfgId),label)
  
  def checkFailedAssertion {
    if(rTree.errorNodes.size == 0) {
      stopTimer
      return
    }
    val (spur,infeasibleSuffix) = isSpurious(rTree.errorNodes.head,rTree.parent,getFormula,init)
    val wholePath = pathToRoot(rTree.errorNodes.head,rTree.parent)
    val pathRest = wholePath.dropRight(infeasibleSuffix.size)
    (spur,accelerate,template) match {
      case (true,true,false) =>  // accelerated refinement
        val (removalPath,newPreds) = RefineAccelerate(wholePath, wholePath.size - infeasibleSuffix.size, getFormula, rTree.errorNodes.head, underApproximate, log)
        for (el <- newPreds)
          predMap = predMap + (el._1 -> ((predMap.getOrElse(el._1,List()) ::: el._2)).distinct)
        reconstructTree(removalPath)
      case (true,false,true) =>  // template based refinement 
        val newPreds = RefineTemplate(infeasibleSuffix.map(_._1).zip(getPathToErrorFormula(infeasibleSuffix)), log)
        for (el <- newPreds)
          predMap = predMap + (el._1 -> ((predMap.getOrElse(el._1,List()) ::: el._2)).distinct)
        reconstructTree(infeasibleSuffix.map(_._1))
      case (true,_,_) =>  // normal refinement
        //if(bapaRewrite) formulas = formulas.map(lazabs.bapa.BapaRewrite(_))
        //refinement((path.map(_._1)).zip(getPathToErrorFormula(path)))
        val newPreds = RefineNormal(infeasibleSuffix.map(_._1).zip(getPathToErrorFormula(infeasibleSuffix)), log)
        for (el <- newPreds)
          predMap = predMap + (el._1 -> ((predMap.getOrElse(el._1,List()) ::: el._2)).distinct)
        reconstructTree(infeasibleSuffix.map(_._1))
      case (false,_,_) =>
        stopTimer
        hasBug = true
        if(lazabs.nts.NtsWrapper.stateNameMap.size != 0) {
          def errorPath(current: RNode): List[RNode] = rTree.getParent.get(current) match {
            case Some(papa) => errorPath(papa._1) :+ current
            case None => List(current)
          }
        println("The program has a bug in the following path: " + errorPath(rTree.errorNodes.head).map(x => lazabs.nts.NtsWrapper.stateNameMap.getOrElse(x.getCfgId,"")))
      }
      else
        println("The program has a bug")        
    }
  }
  
  /**
   * reconstruct a tree after a spurious path is found
   * it should normally come after interpolation finds new predicates
   */  
  def reconstructTree(path: List[RNode]) {
    // ************** start of caching **************
    reusableRoots ++= subtreesRoots(path)
    val reusableRootChildren = reusableRoots.map(allNodes)  // all nodes in the subtree,  unfinished leaves
    val allNodesInSubtrees =
      (for (l <- reusableRootChildren.map(_._1).iterator; e <- l.iterator) yield e).toSeq
    val openNodesInSubtrees =
      (for ((_, s) <- reusableRootChildren.iterator; e <- s.iterator) yield e).toSet
    queue = queue.filterNot(openNodesInSubtrees.contains)  // removing the unfinished nodes
    //nodeHash = collection.mutable.Map().empty ++ nodeHash.mapValues(_ -- allNodesInSubtrees).filterNot(_._2.size == 0)    
    // ************** end of caching **************
    pruneChildren(path.head)
    val mainNodes: Set[RNode] = allNodes(rTree.getStart)._1
    nodeHash = collection.mutable.Map().empty ++ nodeHash.mapValues(_ intersect mainNodes).filterNot(_._2.size == 0)
    adjustSubsumption(mainNodes,(allNodesInSubtrees.toSet -- openNodesInSubtrees.toSet))
    if (path.head.getCfgId == cfg.start.getId || path.head.getId == -1) {  // path.head is -1 when there are global variables in the original Scala file
      val startNode = constructARTNode(cfg.start,BoolConst(true))
      queue ::= startNode
      nodeHash += (cfg.start -> Set(startNode))
      rTree.setStart(startNode)
      makeRTree
    }
    else {
      rTree.getParent.get(path.head) match {
        case Some(par) =>
          val newNode = constructARTNode(CFGVertex(path.head.getCfgId),exprSetToFormula(par._1.getAbstraction))
          queue :+= newNode
          rTree.transitions += (par._1 -> (rTree.transitions.getOrElse(par._1, Set.empty) + RAdjacent(par._2,newNode)))
          nodeHash += (CFGVertex(newNode.getCfgId) -> (nodeHash.getOrElse(CFGVertex(newNode.getCfgId), Set()) + newNode))
          rTree.parent += (newNode -> (par._1,par._2))          
          rTree.transitions = (rTree.transitions + (par._1 -> (rTree.transitions.getOrElse(par._1, Set.empty) - (RAdjacent(par._2,path.head))))).filterNot(_._2.size == 0)
          nodeHash = (nodeHash + (CFGVertex(path.head.getCfgId) -> (nodeHash.getOrElse(CFGVertex(path.head.getCfgId),Set()) - path.head))).filterNot(_._2.size == 0)
          rTree.transitions = rTree.getTransitions.filterNot(_._1 == path.head)
          rTree.parent -= path.head
          queue = queue.filterNot(_ == path.head)
          makeRTree
        case None =>
      }
    }
    checkFailedAssertion
  }
}
