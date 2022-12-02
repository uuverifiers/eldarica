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

package lazabs.cfg

/**
 * Transformers on CFGs 
 * @author hossein hojjat
 *
 */

import lazabs.ast.ASTree._
import lazabs.types._
import lazabs.utils.Manip._
import MakeCFG._

/**
 *  generic transformer of a CFG
 *  returns None if the rule is not applicable
 */ 
trait CFGTransformer {
  def apply(c: CFG): Option[CFG]
}
 
/**
 * applies the sequence rule of large block encoding to a control flow graph
 */
object SequenceRule extends CFGTransformer {
  def apply(cfg: CFG): Option[CFG] = {
    val singleVertices = cfg.parent.filter(_._2.size == 1).keys.filter(cfg.transitions.isDefinedAt(_))filter(sv => cfg.predicates.getOrElse(sv,List()).map(_._1).contains(Variable("sc_LBE",None))) // the vertices with just one parent
    if (singleVertices.isEmpty) return None
    val singleVertex = singleVertices.head  // singleVertex is the vertex which should be deleted
    var (parentVertex: CFGVertex, l: Label) = cfg.parent.get(singleVertex) match {    // parentVertex is the only father of singleVertex
      case Some(a) => (a.head.to,a.head.label)
      case None =>
    }
    // ################# maintain the adjacency map #################
    val singleVertexTrans: Set[CFGAdjacent] = cfg.transitions.getOrElse(singleVertex,Set())  // outgoing edges from the single Vertex
    var newAdjMap = cfg.transitions - singleVertex // removing the edge parentVertex --> singleVertex 
    newAdjMap += (parentVertex -> (cfg.transitions.getOrElse(parentVertex,Set()) ++ singleVertexTrans.map(adj => CFGAdjacent(Sequence(l,adj.label),adj.to)) - CFGAdjacent(l,singleVertex)))
    // #################   maintain the parent map  #################
    val newParentMap = singleVertexTrans.foldLeft(cfg.parent)((a,b) =>  // updating the parent transitions
      addMultiMap(subtractMultiMap(a, Map(b.to -> Set(CFGAdjacent(b.label, singleVertex)))), Map(b.to -> Set(CFGAdjacent(Sequence(l,b.label),parentVertex))))) - singleVertex
    // #################   maintain the variable map  #################      
    val newVarsMap = (cfg.variables - singleVertex).updated(parentVertex,cfg.variables.getOrElse(parentVertex,Set()) ++ cfg.variables.getOrElse(singleVertex,Set()))      
    //println("sequence rule " + singleVertex.id)
    //lazabs.viewer.DrawGraph(cfg.transitions.toList,cfg.predicates,true,None)
    //Console.readLine
    Some(cfg.update(transitions = newAdjMap, parent = newParentMap, predicates = cfg.predicates - singleVertex, variables = newVarsMap))
  }
}

/**
 * applies the choice rule of large block encoding to a control flow graph
 */
object ChoiceRule extends CFGTransformer {
  def apply(cfg: CFG): Option[CFG] = {
    var doubles = List[(CFGVertex,CFGVertex)]()
    cfg.transitions.foreach{ e => 
      val dupVertices = e._2.toList.map(_.to).diff(e._2.toList.map(_.to).distinct)   // the destinations with more than one transitions
      dupVertices.foreach(v => doubles ::= (e._1,v))
    }
    doubles = doubles.filter(dbs => {
      cfg.predicates.getOrElse(dbs._2,List()).map(_._1).contains(Variable("sc_LBE",None))
    })
    if( doubles.isEmpty) return None
    var newTrans = Map[CFGVertex,Set[CFGAdjacent]]()
    var deleteTrans = Map[CFGVertex,Set[CFGAdjacent]]()
    doubles.foreach(vv => {
      val dupAdjs = cfg.transitions.getOrElse(vv._1,Set()).filter(_.to == vv._2)
      newTrans = addMultiMap(newTrans, Map(vv._1 -> Set(CFGAdjacent(dupAdjs.map(_.label).reduceLeft(Choice(_,_)),vv._2))))
      deleteTrans = addMultiMap(deleteTrans, Map(vv._1 -> dupAdjs))
    })      
    var newParentMap = cfg.parent
    newTrans.toList.foreach(a => a._2.foreach(b => newParentMap = addMultiMap(newParentMap,Map(b.to -> Set(CFGAdjacent(b.label,a._1))))))
    deleteTrans.toList.foreach(a => a._2.foreach(b => newParentMap = subtractMultiMap(newParentMap,Map(b.to -> Set(CFGAdjacent(b.label,a._1))))))
    //println("choice rule mizanam")
    Some(cfg.update(transitions = subtractMultiMap(addMultiMap(cfg.transitions,newTrans), deleteTrans),parent = newParentMap))
  }
}

/**
 * applies the transitive closure rule of larger block encoding to a control flow graph
 */
object AccelerationRule extends CFGTransformer {
  /**
   * converts a label to disjunctive normal form
   */
  def DNF(ol: Label): Label = ol match {
    case Sequence(l1,Choice(l2,l3)) =>
      val firstArg = DNF(l1)
      val secondArg = DNF(l2)
      val thirdArg = DNF(l3)
      (firstArg,secondArg,thirdArg) match {
        case (Choice(_,_),_,_)           => Choice(DNF(Sequence(firstArg,secondArg)),DNF(Sequence(firstArg,thirdArg)))
        case (_,Choice(_,_),Choice(_,_)) => Choice(DNF(Sequence(firstArg,secondArg)),DNF(Sequence(firstArg,thirdArg)))
        case (_,Choice(_,_),_)           => Choice(DNF(Sequence(firstArg,secondArg)),Sequence(firstArg,thirdArg))
        case (_,_,Choice(_,_))           => Choice(Sequence(firstArg,secondArg),DNF(Sequence(firstArg,thirdArg)))
        case _ =>
          Choice(Sequence(firstArg,secondArg),Sequence(firstArg,thirdArg))
      }
    case Sequence(Choice(l1,l2),l3) =>
      val firstArg = DNF(l1)
      val secondArg = DNF(l2)
      val thirdArg = DNF(l3)
      (firstArg,secondArg,thirdArg) match {
        case (_,_,Choice(_,_))           => Choice(DNF(Sequence(firstArg,thirdArg)),DNF(Sequence(secondArg,thirdArg)))
        case (Choice(_,_),Choice(_,_),_) => Choice(DNF(Sequence(firstArg,thirdArg)),DNF(Sequence(secondArg,thirdArg)))
        case (Choice(_,_),_,_)           => Choice(DNF(Sequence(firstArg,thirdArg)),Sequence(secondArg,thirdArg))
        case (_,Choice(_,_),_)           => Choice(Sequence(firstArg,thirdArg),DNF(Sequence(secondArg,thirdArg)))
        case _ =>
          Choice(Sequence(firstArg,thirdArg),Sequence(secondArg,thirdArg))
      }
    case Choice(l1,l2) => Choice(DNF(l1),DNF(l2))
    case Sequence(l1,l2) =>
      val firstArg = DNF(l1)
      val secondArg = DNF(l2)
      (firstArg,secondArg) match {
        case (Choice(_,_),_) => DNF(Sequence(firstArg,secondArg))
        case (_,Choice(_,_)) => DNF(Sequence(firstArg,secondArg))
        case _ => Sequence(DNF(l1),DNF(l2))
      }      
    case l@_ => l
  }
  /**
   * flattens a sequence of labels to a list of expressions
   */
  def flattenSequence(ol: Label): List[Expression] = ol match {
    case Sequence(l1,l2) => flattenSequence(l1) ::: flattenSequence(l2)
    case Choice(l1,l2) =>
      println("Bug in DNF conversion")
      sys.exit(0)
    case Transfer(t) => List(t)
    case _ => List()
  }
  /**
   * converts a given lable to a two-dimensional list which is preferred by Flata
   */
  def label2lists(ol: Label): List[List[Expression]] = {
    def recur(l: Label): List[List[Expression]] = l match {
      case Sequence(l1,l2) => List(flattenSequence(l))
      case Choice(l1,l2) => recur(l1) ::: recur(l2)
      case Transfer(t) => List(List(t))
      case _ =>
        println("edge is not supported in acceleration " + l)
        sys.exit(0)
    }
    recur(DNF(ol))
  }
  def apply(cfg: CFG): Option[CFG] = {
    val selfLoop = cfg.transitions.map(e => (e._1,e._2.filter(_.to == e._1))).find(_._2.size != 0)
    if(!selfLoop.isDefined) return None
    val (selfLoopVertex,selfLoopAdjs) = selfLoop.get
    val aExpr: Expression = lazabs.nts.FlataWrapper.accelerate(label2lists(selfLoopAdjs.head.label),lazabs.nts.AccelerationStrategy.PRECISE) match {
      case Some(v: Expression) =>
        println("static acceleration")
        v
      case None => return None
    }
    val (acceleratedExpr,freshs) = skolemize(aExpr)
    val nv = CFGVertex(FreshCFGStateId.apply)
    // ################# maintain the adjacency map #################
    var newAdjMap = cfg.transitions + (selfLoopVertex -> (cfg.transitions.getOrElse(selfLoopVertex,Set()) - selfLoopAdjs.head)) // removing the previous loop transition of selfLoopVertex
    cfg.parent.getOrElse(selfLoopVertex,Set()).filterNot(_.to == selfLoopVertex).foreach{adj =>
      newAdjMap += (adj.to -> (newAdjMap.getOrElse(adj.to,Set()) - CFGAdjacent(adj.label,selfLoopVertex) + CFGAdjacent(adj.label,nv))) // updating the transitions to selfLoopVertex
    }
    newAdjMap += (nv -> Set(CFGAdjacent(Transfer(acceleratedExpr),selfLoopVertex))) // adding the new transition of nv to selfLoopVertex    
    // #################   maintain the parent map  #################
    var newParentMap = cfg.parent + (selfLoopVertex -> (cfg.parent.getOrElse(selfLoopVertex,Set()) - selfLoopAdjs.head)) // removing the previous loop transition of selfLoopVertex
    newParentMap += (selfLoopVertex -> (cfg.parent.getOrElse(selfLoopVertex,Set()).filter(_.to == selfLoopVertex) + CFGAdjacent(Transfer(acceleratedExpr),nv) - selfLoopAdjs.head))
    newParentMap += (nv -> (cfg.parent.getOrElse(selfLoopVertex,Set()).filter(_.to != selfLoopVertex)))   
    // #################   maintain the variable map  #################      
    val newVarsMap = cfg.variables.updated(nv,cfg.variables.getOrElse(selfLoopVertex,Set()) ++ freshs)
    Some(cfg.update(transitions = newAdjMap.filterNot(_._2.size == 0),parent = newParentMap.filterNot(_._2.size == 0),variables = newVarsMap, 
        predicates = cfg.predicates + (nv -> List((BoolConst(false),List()),(Variable("sc_LBE"),List())))))
  }
}

/**
 * Large-block encoding
 */
object LargeBlock extends CFGTransformer {
  var accelerate: Boolean = false
  def doAcceleration {
    accelerate = true
  }
  def apply(cfg: CFG): Option[CFG] = {
    var changed = false
    var applicable = false
    var after: Option[CFG] = None
    var currentCFG = cfg
    do {
      changed = false
      // 1 - apply sequence rule until fix-point
      after = SequenceRule(currentCFG)
      if(after.isDefined)
        changed = true
      while(after.isDefined) {
        currentCFG = after.get
        after = SequenceRule(currentCFG)
      }
      // 2 - apply choice rule until fix-point
      after = ChoiceRule(currentCFG)
      if(after.isDefined) 
        changed = true
      while(after.isDefined) {
        currentCFG = after.get
        after = ChoiceRule(currentCFG)
      }
      // 2 - apply acceleration rule until fix-point
      if(accelerate) {
        after = AccelerationRule(currentCFG)
        if(after.isDefined)
          changed = true
        while(after.isDefined) {
          currentCFG = after.get
          after = AccelerationRule(currentCFG)
        }
      }      
      if(changed) applicable = true
    } while(changed)
    //lazabs.viewer.DrawGraph(currentCFG.transitions.toList,currentCFG.predicates,false,None)
    //Console.readLine
    if(applicable) Some(currentCFG) else None
  }
}

/**
 * checks indexing of arrays to ensure the index is smaller than the length  
 */
object ArrayBound extends CFGTransformer {
  def arrayAccessConstraint(l: Label): Set[Expression] = {
    def arrayAccessConstraint(e: Expression): Set[Expression] = e match {
      case Not(e) => arrayAccessConstraint(e)
      case Minus(e) => arrayAccessConstraint(e)
      case Disjunction(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case Conjunction(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case Equality(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case Inequality(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case LessThan(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case LessThanEqual(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case GreaterThan(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case GreaterThanEqual(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case Addition(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case Subtraction(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case Multiplication(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case Division(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case Modulo(e1,e2) => arrayAccessConstraint(e1) ++ arrayAccessConstraint(e2)
      case ArraySelect(ScArray(_,Some(aLength)),e2) => arrayAccessConstraint(e2) + LessThan(e2,aLength)
      case ArraySelect(ScArray(_,None),e2) => Set()
      case _ => Set()
    }
    l match {
      case Assume(p) => arrayAccessConstraint(p)
      case Assign(lhs, rhs) => (arrayAccessConstraint(lhs) ++ arrayAccessConstraint(rhs))
      case _ => Set()
    }
  }
  var adjMap = Map[CFGVertex,Set[CFGAdjacent]]().empty
  var parentMap = Map[CFGVertex,Set[CFGAdjacent]]().empty
  var predMap = Map[CFGVertex,List[(Expression,List[Int])]]().empty
  var start = CFGVertex(-1)
  def apply(cfg: CFG): Option[CFG] = {
    adjMap = arrayBound(start,List())
    Some(cfg.update(transitions = adjMap, predicates = predMap,parent = parentMap))
  }  
  def arrayBound(start: CFGVertex, alreadyExplored: List[CFGVertex]): Map[CFGVertex,Set[CFGAdjacent]] = {
    if (alreadyExplored.contains(start)) return Map.empty
    var constraints = Set[Expression]()
    var constraintsTrans = Map[CFGVertex,Set[CFGAdjacent]]().empty
    var vertex2Constraint = Map[Expression,CFGVertex]().empty
    adjMap.get(start) match {
      case Some(adjs) => 
        val newAdjs = adjs.map(adj => {
          constraints = arrayAccessConstraint(adj.label)
          if (constraints.size != 0) {
            val assertVertex = vertex2Constraint.get(constraints.reduceLeft(Conjunction(_,_))) match {
              case Some(vertex) => vertex
              case None =>
                val nv = CFGVertex(FreshCFGStateId.apply)
                predMap += (nv -> predMap.getOrElse(start,List()))
                vertex2Constraint += (constraints.reduceLeft(Conjunction(_,_)) -> nv)
                nv
            }
            constraintsTrans = addMultiMap(constraintsTrans, Map(assertVertex -> Set(adj))) + 
              (start -> Set(CFGAdjacent(Assume(Not(constraints.reduceLeft(Conjunction(_,_)))), CFGVertex(-1))))
            // maintaining the parent relation
            parentMap = subtractMultiMap(addMultiMap(addMultiMap(addMultiMap(parentMap, Map(adj.to -> Set(CFGAdjacent(adj.label,assertVertex)))),
              Map(assertVertex -> Set(CFGAdjacent(Assume(constraints.reduceLeft(Conjunction(_,_))), start)))),
              Map(CFGVertex(-1) -> Set(CFGAdjacent(Assume(Not(constraints.reduceLeft(Conjunction(_,_)))), start)))),
              Map(adj.to -> Set(CFGAdjacent(adj.label,start)))) // the original link in the parent is deleted
                CFGAdjacent(Assume(constraints.reduceLeft(Conjunction(_,_))), assertVertex)
          } else adj})
        addMultiMap(addMultiMap(constraintsTrans, adjs.map(_.to).map(arrayBound(_, start :: alreadyExplored)).reduceLeft(_++_)), Map(start -> newAdjs))  
      case None =>
        Map.empty
    }
  }
}

object CFGTransform {
  /**
   * removes the access to arrays
   */
  def removeArrayAccess(adjMap: Map[CFGVertex,Set[CFGAdjacent]]): Map[CFGVertex,Set[CFGAdjacent]] = {
    var arrayMaps = adjMap.filter(x => x._2.exists(y => haveArrayAccess(y.label)))
    var newAdjMap = adjMap
    arrayMaps.foreach{arrayMap =>
      arrayMap._2.filter(x => haveArrayAccess(x.label)).foreach{ adj =>
        newAdjMap = addMultiMap(subtractMultiMap(newAdjMap, Map(arrayMap._1 -> Set(adj))),
            Map(arrayMap._1 -> Set(CFGAdjacent(Assume(BoolConst(true)),adj.to))))
      }}
    newAdjMap
  }
  /**
   * determines if a label uses array access
   */
  def haveArrayAccess(l: Label): Boolean = {
    def haveArrayAccess(e: Expression): Boolean = e match {
      case ArraySelect(ScArray(_,_),_) => true
      case ArrayConst(_) => true      
      case TernaryExpression(op, e1, e2, e3) => (haveArrayAccess(e1) || haveArrayAccess(e2) || haveArrayAccess(e3))
      case BinaryExpression(e1, op, e2) => (haveArrayAccess(e1) || haveArrayAccess(e2))
      case UnaryExpression(op, e) => haveArrayAccess(e)
      case _ => false
    }
    l match {
      case Assume(p) => haveArrayAccess(p)
      case Assign(lhs, rhs) => (haveArrayAccess(lhs) || haveArrayAccess(rhs))
      case _ => false
    }
  }
  
  def apply(cfg: CFG, arrayRemoval: Boolean, accelerate: Boolean): CFG = {
    //adjMap = arrayBound(start,List())
    //if(arrayRemoval) removeArrayAccess
    lazabs.art.RTreeMethods.startTimer
    if(accelerate) LargeBlock.doAcceleration
    val localLBENodes = cfg.transitions.filterKeys(key => cfg.predicates.getOrElse(key,List()).map(_._1).contains(Variable("sc_LBE",None))).map(_._1).toList
    val lbe: Option[CFG] = (if(localLBENodes.size > 0) LargeBlock(cfg) else None)
    val result: CFG = if(lbe.isDefined) lbe.get else cfg
    var aFormulas: Map[(CFGVertex,CFGVertex),Expression] = Map.empty
    var aFreshVars: Map[(CFGVertex,CFGVertex),Set[Variable]] = Map.empty
    result.transitions.foreach(x => x._2.foreach(y => {
      val (trans,_,freshs) =
        (if(cfg.sobject.isDefined) transFormula(y.label,result.variables.getOrElse(x._1, Set())) else {  // we do not generate fresh variables for NTS files
          val resElim = transFormulaElim(y.label,result.variables.getOrElse(x._1, Set())) 
          (resElim._1,resElim._2,Set[Variable]())
        })
      aFormulas += ((x._1,y.to) -> trans)   // only one edge between two vertices
      aFreshVars += ((x._1,y.to) -> (freshs ++ (aFreshVars.getOrElse((x._1,y.to),Set()))))
    }))
    result.update(formulas = aFormulas, freshVars = aFreshVars)  
  }
}