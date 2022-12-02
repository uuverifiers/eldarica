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

package lazabs.horn.global

import lazabs.ast.ASTree._
import lazabs.utils.Manip._
import lazabs.types._
import lazabs.horn.global.ARGraph._
import lazabs.viewer.DrawGraph
import lazabs.viewer.HornPrinter
import scala.collection.mutable.HashMap
import ap.parser._
import IExpression._
import lazabs.prover._
import lazabs.prover.PrincessWrapper._
import lazabs.horn.bottomup.DisjInterpolator._
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.bottomup.Util._
import lazabs.horn.bottomup.HornTranslator
 

object Status extends Enumeration {
  type Status = Value
  val UNKNOWN, SAFE, ERROR = Value
}

case class HornCegar(val originalConstraints: Seq[HornClause], val log: Boolean) {
  val translator = new HornTranslator

  import Status._
  lazy val constraints = HornLBE(originalConstraints.map(Horn.discriminateRelVarArguments(_)))

  /**
   * global variables storing the reachability graph
   */
  var pi = scala.collection.mutable.Map[String,Set[Expression]]().empty
  var alpha = scala.collection.mutable.Map[String,Set[Expression]]().empty
  var arg = ARGraph(InterpNode(-1,BoolConst(false)),Map.empty,Map.empty,Map.empty)
  var nodeHash = collection.mutable.Map[String,Set[RelVarNode]]().empty    // hashing the previous nodes  
  var status: Status = UNKNOWN
    
  /**
   * makes the ARG empty by initializing the global variables 
   */
  def emptyArg {
    arg = ARGraph(InterpNode(-1,BoolConst(false)),Map.empty,Map.empty,Map.empty)
    nodeHash = collection.mutable.Map[String,Set[RelVarNode]]().empty
  }
  
  /**
   * replaces the variables used in the predicate with the local variables used in the constraint 
   */
  def instantiatePredicate(orig: Expression, params: List[Parameter]): Expression = {
    val replace = Map[Variable,Expression]().empty ++ (0 until params.size).zip(params).map{x => (Variable("_" + x._1,Some(x._1)) -> Variable(x._2.name,None).stype(x._2.typ))}
    def rename(e: Expression): Expression = e match {
      case Existential(v, qe) => Existential(v, rename(qe))
      case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, rename(e1), rename(e2), rename(e3))
      case BinaryExpression(e1, op, e2) => BinaryExpression(rename(e1), op, rename(e2))
      case UnaryExpression(op, e) => UnaryExpression(op, rename(e))
      case v@Variable(name, Some(_)) => replace.get(v) match {
        case Some(nv) => nv
        case _ => v
      }
      case _ => 
        e
    }
    rename(orig)
  }
  
  /**
   * gets the formula corresponding to the body of a Horn clause
   */
  def bodyAbstraction(horn: HornClause): Expression = horn.body.map {
    case Interp(f) => f
    case RelVar(name,params) => alpha.get(name) match {
      case Some(preds) => 
        val plist = preds.map(instantiatePredicate(_,params))
        plist.size match {
          case 0 => BoolConst(true)
          case 1 => plist.head
          case _ => plist.reduceLeft(Conjunction(_,_))
        }
      case None => BoolConst(true)
    }
  }.reduceLeft(Conjunction(_,_))
  
  /**
   * gets the formula corresponding to the head of a Horn clause
   */
  def headAbstraction(horn: HornClause): Expression = horn.head match {
    case Interp(f) => f
    case RelVar(i,params) => alpha.get(i) match {
      case Some(preds) => 
        val plist = preds.map(instantiatePredicate(_,params))
        plist.size match {
          case 0 => BoolConst(true)
          case 1 => plist.head
          case _ => plist.reduceLeft(Conjunction(_,_))
        }
      case None => BoolConst(true)
    }
  }
  
  /**
   * determines if a Horn clause is satisfied
   */
  def isSatisfied(horn: HornClause): Boolean = lazabs.prover.Prover.isSatisfiable(Conjunction(bodyAbstraction(horn),Not(headAbstraction(horn)))) match {
    case Some(false) => true // the constraint is satisfied
    case _ => false          // the constraint is not satisfied
  }
  
  /**
   * makes a new abs node if it is not already there in the tree
   * @param relName relation name
   * @param abs abstraction of the node
   */
  def getAbsNode(relName: String, abs: Set[Expression]): RelVarNode = {
    val existingNodes = nodeHash.getOrElse(relName,List())
    existingNodes.find(n => abs == n.abstraction) match {
      case Some(equal) =>
        equal
      case None =>
        val res = RelVarNode(FreshNodeID.apply, relName, abs)
        nodeHash += (res.relName -> (nodeHash.getOrElse(res.relName,Set()) + res))
        val strongers: Set[RelVarNode] = Set() ++ existingNodes.filter(n => (abs.subsetOf(n.abstraction)) && (abs != n.abstraction))
        if (strongers.size != 0)
          arg.subsumption += (res -> strongers)
        res
    }
  }
  
  /**
   * adds a horn clause to ARG
   */
  def addRuleToTree(cl: HornClause,removal: Set[Expression] = Set()) {
    val headNode = cl.head match {
      case RelVar(i,params) => getAbsNode(i,alpha(i) -- removal)
      case Interp(BoolConst(false)) => arg.startNode
      case _ => throw new Exception("Invalid argument in head")
    }
    var children = Seq[ARGNode]()
    cl.body.foreach {_ match {
      case RelVar(varId,childParams) =>
        val child = getAbsNode(varId,alpha(varId))
        children = child +: children
      case Interp(exp) =>
        children = InterpNode(FreshNodeID.apply,exp) +: children
    }}
    arg.transitions += (headNode -> (arg.transitions.getOrElse(headNode, Set.empty) + AndTransition(cl,children)))    
  }
  
  /**
   * the method for constructing an Abstract Reachability Graph
   */
  def constructARG {
    var unsatClause = constraints.find(clause => !isSatisfied(clause) && (clause.head != Interp(BoolConst(false))))
    while(unsatClause.isDefined) {
      unsatClause match {
        case Some(cl) => 
          //println("the constraint is not satisfied: " + lazabs.viewer.HornPrinter(cl))
          cl.head match {
            case RelVar(i,params) =>
              var removal: Set[Expression] = Set()
              alpha(i).foreach {p =>
                if(!isSatisfied(HornClause(Interp(instantiatePredicate(p,params)),cl.body))) {
                  removal += p
                }
              }
              addRuleToTree(cl,removal)
              alpha = alpha.updated(i,alpha.getOrElse(i,Set()) -- removal)
            case _ =>
              throw new Exception("Invalid head for a Horn clause")
          }
          unsatClause = constraints.find(clause => !isSatisfied(clause) && (clause.head != Interp(BoolConst(false))))
        case None =>
      }
    }
    // the A -> false constraint
    constraints.filter(_.head == Interp(BoolConst(false))).find(cl => !isSatisfied(cl)) match {
      case Some(unsatAssert) =>
        addRuleToTree(unsatAssert)
      case None =>
        status = SAFE
        println("==================== SYSTEM SAFE ====================")
    }
    // converting subsumption edges to or-transition
    if(status != SAFE) arg.subsumption.toList.foreach{
      case (weaker,subsumed) => subsumed.foreach{ strongNode =>
        // making transitions to the children of the stronger node
        arg.transitions += (weaker -> (arg.transitions.getOrElse(weaker,Set.empty) ++ arg.transitions.getOrElse(strongNode,Set.empty)))
      }
    }
  }
  
  /**
   * prunes the ARG by removing the nodes not participating in the DAG counter-example
   */
  def prune = {
    var visited = Set[ARGNode]()
    var queue: List[ARGNode] = List(arg.startNode)
    while( queue.size != 0) {
      if(!visited.contains(queue.head)) { 
        visited += queue.head
        arg.transitions.get(queue.head) match {
          case Some(andTrans) if (andTrans.size == 1) =>
            val AndTransition(clause,children) = andTrans.head
            queue ++= (for (r@RelVarNode(_,_,_) <- children) yield r).filterNot(visited.contains(_)).distinct
          case Some(andTrans) if (andTrans.size > 1) =>
            var newChildren = Set[RelVarNode]()  // new children for the OR node
            andTrans.foreach{
              case andTran@AndTransition(HornClause(RelVar(vn,_),_),children) =>
                val dummyNode = RelVarNode(FreshNodeID.apply, vn, Set())
                arg.transitions += (dummyNode -> Set(andTran))
                newChildren += dummyNode
              case _ =>
            }
            arg.transitions += (queue.head -> Set())
            arg.or += (queue.head -> newChildren)
            queue ++= newChildren
          case None =>
        }
      } else
        queue = queue.tail
    }
    arg.transitions = arg.transitions.filter (tran => visited.contains(tran._1))
  }
  
  /**
   * converts level-order to topologial ordering 
   */
  def topolOrder: HashMap[ARGNode,Int] = {
    var result: HashMap[ARGNode,Int] = HashMap[ARGNode,Int]()
    
    var inDegrees = (arg.transitions.map {
      case (n,andTrans) => (for (relChild <- andTrans.map {
        case AndTransition(clause,children) => (for (r@RelVarNode(_,_,_) <- children.distinct) yield r)
      }.flatten) yield (relChild,n))
    }.flatten.groupBy(_._1).mapValues(_.size)) ++ Map(arg.startNode -> 0) ++ (arg.or.values.flatten.map(dum => (dum,1))).toMap
        
    var current = 0
    while(!inDegrees.isEmpty) {
      inDegrees.find {_._2 == 0} match {
        case Some((node,_)) => 
          result += (node -> current)
          arg.transitions.get(node) match {
            case Some(trans) if (trans.size == 1) =>
              (for (rvn@RelVarNode(_,_,_) <- trans.head.children.distinct) yield rvn).foreach{ child =>
                inDegrees += (child -> (inDegrees.getOrElse(child,0) - 1))
              }
            case _ =>
              arg.or.get(node) match {
                case Some(children) =>
                  children.foreach{ child =>
                    inDegrees += (child -> (inDegrees.getOrElse(child,0) - 1))                
                }
                case None => throw new Exception("Error in topological ordering of the counter-example DAG")
              } 
          }
          inDegrees -= node
          current += 1
        case None =>
      }
    }    
    result
  }
  
  def counterExampleDag(nodes: HashMap[ARGNode,Int]): Dag[AndOrNode[HornClause,Unit]] = {
    var dag: Dag[AndOrNode[HornClause,Unit]] = DagEmpty
    nodes.toList.sortWith((a,b) => a._2 >= b._2).foreach {
      case (node,i) =>
        arg.transitions.get(node) match {
          case Some(trans) if (trans.size == 1) =>
            val relVarChildren = (for (rvn@RelVarNode(_,_,_) <- trans.head.children) yield rvn).toList
            val interpChildren = (for (i@InterpNode(_,_) <- trans.head.children) yield i).toList
            dag = DagNode(
              AndNode[HornClause,Unit](HornClause(trans.head.clause.head,
                (for (i@RelVar(_,_) <- trans.head.clause.body) yield i).toList.sortWith {
                  case (RelVar(vName1,_),RelVar(vName2,_)) => 
                    relVarChildren.map(_.relName).indexOf(vName1) <= relVarChildren.map(_.relName).indexOf(vName2)
                } ++
                (for (i@Interp(_) <- trans.head.clause.body) yield i).toList
                )),
              relVarChildren.map(nodes.getOrElse(_,0) - i).toList,
              dag
            )
          case _ =>
            arg.or.get(node) match {
              case Some(children) =>
                val childrenLevels: List[Int] = (for (rvn@RelVarNode(_,_,_) <- children) yield rvn).map(nodes.getOrElse(_,0) - i).toList
                dag = DagNode(
                  OrNode[HornClause,Unit](()),
                  childrenLevels,
                  dag
                )
              case None =>
            }            
        }
    }
    dag
  }

  implicit def horn2cc (h: HornClause): ConstraintClause = translator.global2bup (h)

  /**
   * refining a counter-example dag
   */
  def refinement: Map[String,Set[Expression]] = {
    if(status == SAFE) return Map.empty
    //DrawGraph(arg)
    //Console.readLine
    prune  // pruning the arg
    val dag = counterExampleDag(topolOrder)
    //println(dag)
    //show(dag,"horn-cex")
    //Console.readLine
    val result: Map[String,Set[Expression]] = iPredicateGenerator(dag) match {
      case Left(predicates) =>
        predicates.map{
          case (pName,predicates) =>
            (pName.name,Set[Expression]() ++ predicates.map(formula2Eldarica(_,Map.empty,false)))
        }.toMap
      case Right(bug) =>
        status = ERROR
        Map.empty
    }
    if(log) println("The interpolant map: " + result.map(ip => ip._2.map(lazabs.viewer.ScalaPrinter(_)).mkString(" , ")))
    result
  }
  
  def apply: ARGraph = {
    //println(constraints.map(lazabs.viewer.HornPrinter.printDebug(_)).mkString("\n"))
    val relVars: Set[RelVar] = constraints.map(c => (Set[HornLiteral]() ++ c.body) + c.head).foldLeft[Set[HornLiteral]](Set())(_++_).filter(_ match {
      case RelVar(_,_) => true
      case _ => false
    }).asInstanceOf[Set[RelVar]]
    relVars.foreach{v =>
      pi(v.varName) = Set(BoolConst(false))
    }
    alpha = pi
    constructARG
    var newPredicates = refinement
    //DrawGraph(arg)
    //Console.readLine
    while(!newPredicates.isEmpty) {
      newPredicates.foreach {res =>
        pi.update(res._1,pi.getOrElse(res._1,Set()) ++ res._2)
      }
      alpha = pi
      emptyArg
      constructARG
      newPredicates = refinement
      //DrawGraph(arg)
      //Console.readLine
    }   

    /*for (c <- constraints)
      if (!isSatisfied(c)) {
        println("Clause not satisfied: ")
        println(lazabs.viewer.HornPrinter(c))
      }*/

    if(status == ERROR)
      println("Genuine error in the system")
    arg
  }
}