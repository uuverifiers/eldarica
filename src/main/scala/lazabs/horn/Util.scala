/**
 * Copyright (c) 2011-2023 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn

import ap.parser._
import ap.parser.IExpression.{Eq, i}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.prover.Tree

import ap.terfor.conjunctions.Conjunction

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer,
                                 HashSet => MHashSet}

object Util {

  def toStream[A](f : Int => A) : Stream[A] =
    toStreamHelp(0, f)
  
  private def toStreamHelp[A](n : Int, f : Int => A) : Stream[A] =
    f(n) #:: toStreamHelp(n + 1, f)
  
  //////////////////////////////////////////////////////////////////////////////

  abstract sealed class Dag[+D] {
    def isEmpty : Boolean
    val size : Int

    def map[E](f : D => E) : Dag[E]
    def foreach[U](f : D => U) : Unit

    def toTree[B >: D] : Tree[B]
    def drop(n : Int) : Dag[D]
    def apply(n : Int) : D

    def zipWithIndex : Dag[(D, Int)] = zipWithIndexHelp(0)

    protected[Util]
      def zipWithIndexHelp(depth : Int) : Dag[(D, Int)]

    def zip[B](that : Dag[B]) : Dag[(D, B)]

    def updated[B >: D](updates : Map[Int, (B, List[Int])]) : Dag[B] =
      updatedHelp(0, updates)
    protected[Util]
      def updatedHelp[B >: D](depth : Int,
                              updates : Map[Int, (B, List[Int])]) : Dag[B]

    /**
     * Substitute nodes at given indexes with sub-dags. Each sub-dag
     * of size <code>n</code> can reference nodes <code>n+1, n+2, ...</code>,
     * which are then connected to the children of the original node.
     */
    def substitute[B >: D](insertedDags : Map[Int, Dag[B]]) : Dag[B] =
      substituteHelp(0, insertedDags)._1
    protected[Util]
      def substituteHelp[B >: D](depth : Int,
                                 insertedDags : Map[Int, Dag[B]])
                                : (Dag[B], List[Int])

    /**
     * Inserts <code>insertedDag</code> at <code>index</code>, pushing the
     * existing sub-dag that starts at <code>index</code> downwards.
     * Above the insertion, children of existing nodes are shifted by the size
     * of the inserted dag.
     */
    def insertAt[B >: D](index: Int, insertedDag: Dag[B]): Dag[B]

    def head = apply(0)
    def tail = drop(1)

    def subdagIterator = new Iterator[DagNode[D]] {
      private var rem = Dag.this
      def hasNext = DagEmpty != rem
      def next = {
        val res = rem.asInstanceOf[DagNode[D]]
        rem = res.next
        res
      }
    }

    def iterator : Iterator[D] =
      for (DagNode(d, _, _) <- subdagIterator) yield d

    def incoming(n : Int) : Seq[(Int, Int)] = incomingIterator(n).toList
    def incomingIterator(n : Int) : Iterator[(Int, Int)] =
      for ((DagNode(_, children, _), i) <- subdagIterator.zipWithIndex;
           (c, ci) <- children.iterator.zipWithIndex;
           if (i + c == n)) yield (i, ci)

    def pathFromRoot(n : Int) : Seq[(Int, Int)] = {
      var res = List[(Int, Int)]()
      var k = n
      while (k > 0) {
        val p@(nextk, _) = incomingIterator(k).next
        res = p :: res
        k = nextk
      }
      res
    }

    /**
     * Eliminate orphan nodes other than the root.
     */
    def elimUnconnectedNodes : Dag[D] = elimUnconnectedNodesHelp(0, Set(0))._1

    protected[Util]
      def elimUnconnectedNodesHelp(depth : Int, refs : Set[Int])
                                  : (Dag[D], List[Boolean])

    /**
     * Minimize the DAG by merging nodes with the same data and the
     * same children.
     */
    def collapseNodes : Dag[D] = {
      val seenNodes = new MHashMap[(D, List[Int]), Int]
      val indexMap  = new MHashMap[Int, Int]

      def collapseNodesHelp(dag : Dag[D]) : Dag[D] = dag match {
        case DagEmpty =>
          DagEmpty
        case DagNode(d, children, nextNode) => {
          val newNext         = collapseNodesHelp(nextNode)
          val dSize           = dag.size
          val childrenIndexes = for (c <- children) yield indexMap(dSize - c)
          val key             = (d, childrenIndexes)
          (seenNodes get key) match {
            case Some(oldNode) => {
              indexMap.put(dSize, oldNode)
              DagNode(d, children, newNext)
            }
            case None => {
              seenNodes.put(key, dSize)
              indexMap.put(dSize, dSize)
              val newChildren = childrenIndexes map (dSize - _)
              DagNode(d, newChildren, newNext)
            }
          }
        }
      }

      val remappedDag  = collapseNodesHelp(this)
      val remappedDag2 = remappedDag drop (size - indexMap(size))

      remappedDag2.elimUnconnectedNodes
    }

    def prettyPrint : Unit =
      for ((DagNode(d, children, _), i) <- subdagIterator.zipWithIndex)
        println("" + i + ": " + d +
                (if (children.isEmpty)
                   ""
                 else
                   (" -> " + (for (ind <- children) yield (i + ind)).mkString(", "))))

    def dotPrint(reverse : Boolean) : Unit = {
      println("digraph dag {")
      for ((DagNode(d, children, _), i) <- subdagIterator.zipWithIndex) {
        println("" + i + "[label=\"" + d + "\"];")
        for (c <- children)
          if (reverse)
            println("" + (i + c) + "->" + i + ";")
          else
            println("" + i + "->" + (i + c) + ";")
      }
      println("}")
    }
  }

  case class DagNode[+D](d : D, children : List[Int],
                         next : Dag[D]) extends Dag[D] {
    def isEmpty = false
    val size : Int = next.size + 1
    def map[E](f : D => E) : Dag[E] = {
      val newD = f(d)
      DagNode(newD, children, next map f)
    }
    def foreach[U](f : D => U) : Unit = {
      f(d)
      next foreach f
    }

    protected[Util]
      def zipWithIndexHelp(depth : Int) : Dag[(D, Int)] =
        DagNode((d, depth), children, next.zipWithIndexHelp(depth + 1))

    def drop(n : Int) : Dag[D] =
      if (n == 0) this else (next drop (n-1))

    def zip[B](that : Dag[B]) : Dag[(D, B)] =
      DagNode((d, that.asInstanceOf[DagNode[B]].d),
              children,
              next zip that.asInstanceOf[DagNode[B]].next)

    protected[Util]
      def elimUnconnectedNodesHelp(depth : Int, refs : Set[Int])
                                   : (Dag[D], List[Boolean]) =
      if (refs contains depth) {
        // this node has to be kept
        val (newNext, shifts) =
          next.elimUnconnectedNodesHelp(depth + 1,
                                        refs ++ (for (c <- children.iterator)
                                                 yield (depth + c)))
        (DagNode(d,
                 for (c <- children)
                 yield (1 + shifts.iterator.take(c-1).count(x => !x)),
                 newNext),
         false :: shifts)
      } else {
        // drop this node
        val (newNext, shifts) = next.elimUnconnectedNodesHelp(depth + 1, refs)
        (newNext, true :: shifts)
      }

    def apply(n : Int) : D =
      if (n == 0) d else next(n-1)
    def toTree[B >: D] : Tree[B] =
      Tree(d, for (i <- children) yield drop(i).toTree[B])

    protected[Util]
      def updatedHelp[B >: D](
                 depth : Int,
                 updates : Map[Int, (B, List[Int])]) : Dag[B] = {
      val newNext = next.updatedHelp(depth + 1, updates)
      (updates get depth) match {
        case None =>
          if (newNext eq next) this else DagNode(d, children, newNext)
        case Some((newD, newChildren)) =>
          DagNode(newD, newChildren, newNext)
      }
    }

    protected[Util]
      def substituteHelp[B >: D](depth : Int,
                                 insertedDags : Map[Int, Dag[B]])
                                : (Dag[B], List[Int]) = {
      val (newNext, gaps) = next.substituteHelp(depth + 1, insertedDags)
      val newChildren = for (c <- children) yield (c + firstNSum(gaps, c-1))

      (insertedDags get depth) match {
        case None =>
          (DagNode(d, newChildren, newNext), 0 :: gaps)

        case Some(subDag) => {
          def substChildren(dag : Dag[B]) : (Dag[B], Int) = dag match {
            case DagNode(dagD, dagChildren, dagNext) => {
              val (newDagNext, size) = substChildren(dagNext)
              val newDagChildren =
                for (c <- dagChildren)
                yield (if (c > size) (newChildren(c - size - 1) + size) else c)
              (DagNode(dagD, newDagChildren, newDagNext), size + 1)
            }
            case DagEmpty =>
              (newNext, 0)
          }

          (substChildren(subDag)._1, (subDag.size - 1) :: gaps)
        }
      }
    }

    private def updateNextOfLastNode[B >: D](dag     : Dag[B],
                                             nextDag : Dag[B]) : Dag[B] = {
      dag match {
        case DagNode(d, children, DagEmpty) =>
          DagNode(d, children, nextDag)
        case DagNode(d, children, next) =>
          DagNode(d, children, updateNextOfLastNode(next, nextDag))
        case DagEmpty =>
          nextDag
      }
    }

    def insertAt[B >: D](index : Int, insertedDag : Dag[B]) : Dag[B] = {
      if (index == 0)
        updateNextOfLastNode(insertedDag, this)
      else
        DagNode(d, children.map(_ + insertedDag.size),
                next.insertAt(index - 1, insertedDag))
    }
  }

  case object DagEmpty extends Dag[Nothing] {
    def isEmpty = true
    val size : Int = 0
    def map[E](f : Nothing => E) : Dag[E] = this
    def foreach[U](f : Nothing => U) : Unit = {}

    protected[Util]
      def zipWithIndexHelp(depth : Int) : Dag[(Nothing, Int)] = DagEmpty

    def drop(n : Int) : Dag[Nothing] = {
      if (n != 0)
        throw new IllegalArgumentException
      this
    }

    def zip[B](that : Dag[B]) : Dag[(Nothing, B)] = DagEmpty

    protected[Util]
      def elimUnconnectedNodesHelp(depth : Int, refs : Set[Int])
                                  : (Dag[Nothing], List[Boolean]) = (this, List())

    def apply(n : Int) : Nothing =
      throw new UnsupportedOperationException
    def toTree[B >: Nothing] : Tree[B] =
      throw new UnsupportedOperationException

    protected[Util]
      def updatedHelp[B >: Nothing](
               depth : Int,
               updates : Map[Int, (B, List[Int])]) : Dag[B] = this
    protected[Util]
      def substituteHelp[B >: Nothing](depth : Int,
                                       insertedDags : Map[Int, Dag[B]])
                                      : (Dag[B], List[Int]) = (this, List())
    def insertAt[B](index : Int, insertedDag : Dag[B]) : Dag[B] =
      if (index == 0) insertedDag else throw new IllegalArgumentException
  }

  //////////////////////////////////////////////////////////////////////////////

  private def firstNSum(l : List[Int], n : Int) : Int = {
    var res = 0
    var i = 0
    var rem = l
    while (i < n && !rem.isEmpty) {
      res = res + rem.head
      rem = rem.tail
      i = i + 1
    }
    res
  }

  //////////////////////////////////////////////////////////////////////////////

  def show[D](d : Dag[D], name : String, reverse : Boolean = true) : Unit = {
      val runTime = Runtime.getRuntime
      val filename = if (lazabs.GlobalParameters.get.dotSpec)
                       lazabs.GlobalParameters.get.dotFile
                     else
                       "dag-graph-" + name + ".dot"
      val dotOutput = new java.io.FileOutputStream(filename)
      Console.withOut(dotOutput) {
        d.dotPrint(reverse)
      }
      dotOutput.close

      if (lazabs.GlobalParameters.get.eogCEX) {
        var proc = runTime.exec( "dot -Tpng " + filename + " -o " + filename + ".png" )
        proc.waitFor
        proc = runTime.exec( "eog " + filename + ".png")
//    proc.waitFor
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Union-find specialised for integers ranging over <code>[0, card)</code>
   */
  class IntUnionFind(card : Int) extends Cloneable {
    private val parent : Array[Int] = (0 until card).toArray
    private val rank   : Array[Int] = new Array[Int] (card)

    def apply(d : Int) : Int = {
      val p = parent(d)
      if (p == d) {
        p
      } else {
        val res = apply(p)
        parent(d) = res
        res
      }
    }

    def union(d : Int, e : Int) : Unit = {
      val dp = apply(d)
      val ep = apply(e)
      
      if (dp != ep) {
        val dr = rank(dp)
        val er = rank(ep)
        if (dr < er) {
          parent(dp) = ep
        } else if (dr > er) {
          parent(ep) = dp
        } else {
          parent(ep) = dp
          rank(dp) = dr + 1
        }
      }
    }

    override def clone : IntUnionFind = {
      val res = new IntUnionFind(card)
      Array.copy(this.parent, 0, res.parent, 0, card)
      Array.copy(this.rank,   0, res.rank,   0, card)
      res
    }

    override def toString : String = "[" + (parent mkString ", ") + "]"
  }

  //////////////////////////////////////////////////////////////////////////////
  def treeSize(t : Tree[Conjunction]) =
    (for (c <- t.iterator) yield nodeCount(c)).sum

  def nodeCount(c : Conjunction) : Int =
    ((c.arithConj.size + c.predConj.size) /: c.negatedConjs) {
      case (n, d) => n + nodeCount(d)
    }

  object ClauseTermGraph {
    case class Edge(from : Node, to : Node)

    abstract class Node
    // Used when a graph has more than one sink.
//    case object PseudoNode extends Node

    case class ConstNode(c : IConstant) extends Node {
      override def toString : String = s"$c (${c.hashCode})"
    }

    class AtomNode(a : IAtom) extends Node {
      val constants : Set[IConstant] =
        a.args.flatMap(
          term => SymbolCollector.constants(term).map(c => IConstant(c))).toSet
      override def toString : String = ap.SimpleAPI.pp(a)
    }
    case class HeadNode(a : IAtom) extends AtomNode(a) {
      override def toString : String = ap.SimpleAPI.pp(a) + "_h"
    }
    case class BodyNode(a : IAtom) extends AtomNode(a) {
      override def toString : String = ap.SimpleAPI.pp(a) + "_b"
    }

    case class SyncNode(f : IFormula) extends Node {
      val constants : Set[IConstant] =
        SymbolCollector.constants(f).map(c => IConstant(c)).toSet
      override def toString : String = ap.SimpleAPI.pp(f)
    }

    // Requires function applications of the form f(\bar{x}) = y.
    // (Constraint simplifier preprocessor ensures this form.)
    case class FunAppNode(funApp : IFunApp, eq : IEquation) extends Node {
      val toArg    : IConstant      = eq.right.asInstanceOf[IConstant]
      val fromArgs : Set[IConstant] = funApp.args.flatMap(
        arg => SymbolCollector.constants(arg).map(IConstant)).toSet
      override def toString : String = ap.SimpleAPI.pp(eq)
    }

    val emptyOrdering : Ordering[Dag[Node]] = new Ordering[Dag[Node]] {
      override def compare(x : Dag[Node], y : Dag[Node]) : Int = 0
    }

    def clauseDagToClause(clauseDag : Dag[Node]) : Clause = {
      val nodes = clauseDag.subdagIterator.toList
      // There must at least be two nodes: one for head and one for the body.
      assert(nodes.size >= 2)

      // head is always the last node
      assert(nodes.last.d.isInstanceOf[HeadNode])
      val head : IAtom = nodes.last.d.asInstanceOf[HeadNode].a

      val body      = new ArrayBuffer[IAtom]
      val conjuncts = new ArrayBuffer[IFormula]
      for (node : DagNode[Node] <- nodes.init) {
        node.d match {
          case FunAppNode(_, f) => conjuncts += f
          case SyncNode(f) => if (!f.isTrue) conjuncts += f
          case BodyNode(a) => body += a
          case _ : ConstNode => // nothing needed
          case _ : HeadNode => assert(false) // not possible, we drop the last node
        }
      }
      Clause(head, body.toList, IExpression.and(conjuncts))
    }
  }

  class ClauseTermGraph(clause : Clause) {
    import ClauseTermGraph._

    // TODO: optimize
    def outgoing(n : Node) = edges.filter(e => e.from == n)
    def incoming(n : Node) = edges.filter(e => e.to == n)

    private val conjuncts =
      LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)
    private val curNodes = new ArrayBuffer[Node]
    private val curEdges = new ArrayBuffer[Edge]

    // Add one node for each constant
    clause.constants.foreach(c => curNodes += ConstNode(IConstant(c)))

    private val sources = clause.body.map(BodyNode)
    private val sink    = HeadNode(clause.head)

    (sources ++ Seq(sink)) foreach(curNodes += _)

    // Handle clause body
    for (source <- sources) {
      // Add each constant as outgoing
      for (constant <- source.constants) {
        val constantNode = ConstNode(constant)
        curEdges += Edge(source, constantNode)
      }
    }

    // Handle clause head / sink
    // Add each constant as incoming
    for (constant <- sink.constants) {
      val constantNode = ConstNode(constant)
      curEdges += Edge(constantNode, sink)
    }

    for (conjunct <- conjuncts) {
      conjunct match {
        case IBoolLit(true) => // ignore - used as pseudo-root
        case Eq(funApp@IFunApp(f, args), IConstant(_)) if args isEmpty =>
          // 0-ary function applications (constants)
          val node = FunAppNode(funApp, conjunct.asInstanceOf[IEquation])
          for (fromArg <- node.fromArgs) {
            curEdges += Edge(ConstNode(fromArg), node)
          }
          curEdges += Edge(node, ConstNode(node.toArg))
          curNodes += node
        case Eq(funApp@IFunApp(f, args), IConstant(_)) if args nonEmpty =>
          val node = FunAppNode(funApp, conjunct.asInstanceOf[IEquation])
          for (fromArg <- node.fromArgs) {
            curEdges += Edge(ConstNode(fromArg), node)
          }
          curEdges += Edge(node, ConstNode(node.toArg))
          curNodes += node
        case _ =>
          val node = SyncNode(conjunct)
          curNodes += node
          for (constant <- node.constants) {
            val constantNode = ConstNode(constant)
            curEdges += Edge(constantNode, node)
          }
          // Sync nodes are connected to the sink
          curEdges += Edge(node, sink)
      }
    }

    // A clause always has a head, thus no pseudo-sink is needed; but the head
    // can be FALSE or might throw away some arguments. Since these would not
    // have incoming edges from all leaves, we add those manually.
    val leavesExceptHead : Seq[Node] = curNodes.filter(
      node => node != sink && outgoing(node).isEmpty)

    // Add edges from leaves to the sink
    leavesExceptHead.foreach(leaf => curEdges += Edge(leaf, sink))

//    if (clause.head == IAtom(HornClauses.FALSE, Nil)) {
//      val falseNode        = AtomNode(IAtom(HornClauses.FALSE, Nil))
//      val sinksExceptFalse =
//        nodes.filter(node => outgoing(node).isEmpty && node != falseNode)
//      curEdges ++= sinksExceptFalse.map(node => Edge(node, falseNode))
//    }

    /**
     * Returns source nodes, but does not include the pseudo-root (if there is
     * one)
     */
    val getNonPseudoSources : Seq[Node] =
      curNodes.filter(node => incoming(node).isEmpty)

    // If there is more than one source, add a pseudo-root.
    val (getPseudoRoot, hasPseudoRoot) = if (getNonPseudoSources.size != 1) {
      val pseudoRoot = SyncNode(i(true))
      curNodes += pseudoRoot
      curEdges ++= getNonPseudoSources.map(node => Edge(pseudoRoot, node))
      (pseudoRoot, true)
    } else {
      (getNonPseudoSources.head, false)
    }

    def nodes : Seq[Node] = curNodes
    def edges : Seq[Edge] = curEdges

    if (lazabs.GlobalParameters.get.assertions) {
      // TODO: assert invariants about the graph that should be preserved.
    }

    /**
     * Attempts to produce a topologically sorted DAG from the graph.
     * If the graph has cycles, returns `None`.
     * @param dagOrdering If possible, DAG will be ordered such that smaller nodes
     *                 in this ordering will appear earlier in the DAG when
     *                 possible. For instance, can be used to put selects before
     *                 stores, which can lead to a DAG with shorter edges.
     * @return `Option[Dag[Node]]`, `None` if graph has cycles.
     */
    def topologicalSort(dagOrdering : Ordering[Dag[Node]] =
                        ClauseTermGraph.emptyOrdering) : Option[Dag[Node]] = {
      // Keep track of visited nodes to detect cycles.
      val createdSubDags = new MHashMap[Node, Dag[Node]]
      val visiting       = new MHashSet[Node]()

      def buildDagFromNode(node : Node) : Option[Dag[Node]] = {
        if (visiting.contains(node)) return None // Cycle detected
        if (createdSubDags.contains(node)) return Some(createdSubDags(node))

        visiting += node

        val childNodes = outgoing(node).map(edge => edge.to)
        val maybeChildDags =
          for (childNode <- childNodes) yield buildDagFromNode(childNode)

        if (maybeChildDags.exists(_.isEmpty)) {
          None // Cycle detected in one of the child nodes
        } else {
          // TODO: order children so that the cuts are minimized
          val childDags = maybeChildDags.map(_.get).sorted(dagOrdering)

          val dagNode = (node match {
            case _ : ConstNode | _ : SyncNode =>
              val nextDag : Dag[Node] =
                if (childDags isEmpty) {
                  DagEmpty
                } else {
                  var next : Dag[Node] = DagEmpty
                  for (subDag <- childDags.reverse if !subDag.isEmpty) {
                    next = DagNode(subDag.head, Nil, next)
                  }
                  next
                }
                DagNode(node, childDags.indices.map(_ + 1).toList, nextDag)
                  .substitute(
                    childDags.indices.map(_ + 1).toList.zip(childDags).toMap)
            case _ : AtomNode | _ : FunAppNode =>
            // Ensure all (ConstNode) children of a node are right below
            // that node. This is needed, because when splitting a DAG, we want
            // the splits to only happen from a ConstNode to some other node,
            // as the splitting code duplicates ConstNodes to below the DAG.
            // Alternatively, such nodes would need to be duplicated above,
            // or we would need to use hypergraphs, which would both be more
            // complicated.
            // This is possible because there cannot be more than one incoming
            // edge to a ConstNode (ensured by EquationInliner by splitting such
            // cases). Therefore this modification cannot introduce back-edges.z
              val conjoinedChildDags = childDags.size match {
                case 1 => childDags.head
                case _ =>
                  childDags.reduceRightOption(
                    (childDag, dagToInsert) => childDag.insertAt(1, dagToInsert))
                    .getOrElse(DagEmpty)
              }
              val dnode = DagNode(node, (1 to childDags.size).toList, conjoinedChildDags)
              val dNodeCollapsed = dnode.collapseNodes
              if (childDags.size > 1 && !node.isInstanceOf[ConstNode]) {
//                Util.show(dNodeCollapsed, "collapsed", false)
//                Util.show(dnode, "orig", false)
//                println("Orig")
//                dnode.prettyPrint
//                println("Coll")
//                dNodeCollapsed.prettyPrint
//                println("="*80)
                //         Util.show(dNodeCollapsed, "dagNode", false)
              }
              dnode
          })
          val dNodeCollapsed = dagNode.collapseNodes
          visiting -= node

          createdSubDags += ((node, dNodeCollapsed))
          Some(dNodeCollapsed)
        }
      }

      buildDagFromNode(getPseudoRoot) match {
        case Some(dag) => Some(dag.collapseNodes)
        case None      => None
      }
    }

    /**
     * Splits a topologically-sorted DAG into two parts after the specified node.
     *
     * @param dag The original DAG to be split.
     * @param node The node in the DAG after which the split is to occur.
     * @param glueNodeInstantiator A function to instantiate a new node
     *                             to serve as a connector between the two parts.
     *                             Its argument is a list of incoming nodes,
     *                             and it should return the glue nodes
     *                             (n1, n2) where n1 is the sink of split above,
     *                             and n2 is the source of the split below.
     * @param isSplittable A predicate to check if the passed node is splittable,
     *                     i.e., if it can be connected via the connector node.
     * @param hasPseudoRoot if true, edges coming from the root will not be
     *                     considered real, and any such orphans will be connected
     *                     to the glue node below.
     * @tparam T The type of nodes in the DAG.
     * @return A tuple containing the two parts of the DAG, in order.
     */
    /**
     * Splits a topologically-sorted DAG into two parts after the specified node.
     *
     * @param dag The original DAG to be split.
     * @param node The node in the DAG after which the split is to occur.
     * @param glueNodeInstantiator A function to instantiate a new node
     *                             to serve as a connector between the two parts.
     *                             Its argument is a list of indices of incoming
     *                             nodes, and it should return the glue node.
     * @param isSplittable A predicate to check if the passed node is splittable,
     *                     i.e., if it can be connected via the connector node.
     * @param hasPseudoRoot if true, edges coming from the root will not be
     *                     considered real, and any such orphans will be connected
     *                     to the glue node below.
     * @tparam T The type of nodes in the DAG.
     * @return A tuple containing the two parts of the DAG, in order.
     */
    def splitDagAfterNode[T](dag                  : Dag[T],
                             node                 : T,
                             glueNodeInstantiator : List[T] => (T, T),
                             isSplittable         : T => Boolean,
                             hasPseudoRoot        : Boolean = false)
    : (Dag[T], Dag[T]) = {
      val indexedDag = dag.zipWithIndex
      val splitInd   = indexedDag.iterator.indexWhere(_._1 == node)

      if (splitInd == -1 || splitInd == dag.size) {
        throw new IllegalArgumentException(
          "Node T cannot be the last node or is not found in the DAG")
      }

      // Index for the glue node
      val glueInd = splitInd + 1

      /* Sync nodes
       */
      val syncsAboveSplit : Seq[DagNode[(T, Int)]] = {
        indexedDag.subdagIterator.collect{
          case d@DagNode((SyncNode(_), i), children, _)
            if children.size == 1 && i + children.head == dag.size - 1 => d
        }.toSeq
      }

      val parentToOrphanChildren     = new ArrayBuffer[(T, List[Int])]
      val orphanedParentInds         = new ArrayBuffer[(DagNode[(T, Int)], Int)]
      val orphanedNodeAboveUpdateMap = new MHashMap[Int, (T, List[Int])]
      // Orphaned nodes have at least one child below split
      for (n : DagNode[(T, Int)] <- indexedDag.subdagIterator
           // only iterate over nodes above the split and ignore pseudo-root
           if n.d._2 < glueInd && (!hasPseudoRoot || n.d._2 > 0)) {
        val nInd    = n.d._2
        val orphans =
          n.children.filter(childInd => childInd + nInd > splitInd &&
            !syncsAboveSplit.contains(n))
            .map(childInd => childInd + nInd - glueInd)
        if (orphans nonEmpty) {
          parentToOrphanChildren += n.d._1 -> orphans
          orphanedParentInds += n -> nInd
          val newChildren = n.children.map(
            childInd =>
              if (childInd + nInd > glueInd) glueInd - nInd else childInd)
            .distinct.sorted
          orphanedNodeAboveUpdateMap += nInd -> (n.d._1, newChildren)
        }
        // Connect syncs above split to the new glue node.
        if (syncsAboveSplit contains n) {
          orphanedNodeAboveUpdateMap += nInd -> (n.d._1, List(glueInd - nInd))
        }
      }

      /* If there was a pseudo-root with orphaned edges, carry those over to
         the glue node as outgoing edges.
       */
      val orphansFromPseudoRoot =
        if (hasPseudoRoot) {
          dag.asInstanceOf[DagNode[T]]
            .children.filter(childInd => childInd > splitInd)
        } else {
          Nil
        }
      // Create the glue node using the information of orphaned nodes and
      // duplicated nodes.
      val (glueNodeSink, glueNodeSource) = glueNodeInstantiator(
        orphanedParentInds.map(pair => pair._1.d._1).toList)

      val root          = dag.asInstanceOf[DagNode[T]]
      val dagAboveSplit =
        DagNode(root.d, root.children.diff(orphansFromPseudoRoot), root.next)
          .substitute(Map(glueInd -> DagNode(glueNodeSink, List(), DagEmpty)))
          .updated(orphanedNodeAboveUpdateMap.toMap).elimUnconnectedNodes

      val dagBelowSplit = {
        val belowOldDag = dag.drop(glueInd)
        var next        = belowOldDag
        // orphaned nodes are replicated below
        for (((orphanedNode, orphanInds), i) <- parentToOrphanChildren.zipWithIndex) {
          // offset children by the number of orphans that were added
          val newChildren = orphanInds.map(ind => ind + i + 1)
          val newNode     = DagNode(orphanedNode, newChildren, next)
          next = newNode
        }
        val pseudoChildren = orphansFromPseudoRoot.map(
          childInd => childInd - glueInd + parentToOrphanChildren.size + 1)
        DagNode(glueNodeSource, (1 to parentToOrphanChildren.size).toList ++
          pseudoChildren, next)
      }

//      lazabs.horn.bottomup.Util.show(dag, "dag", false)
//      println("\nabove\n")
//      lazabs.horn.bottomup.Util.show(dagAboveSplit, "aboveSplit", false)
//      dagAboveSplit.prettyPrint
//      println("\nbelow\n")
//      lazabs.horn.bottomup.Util.show(dagBelowSplit, "belowSplit", false)
//      dagBelowSplit.prettyPrint
//      println

      (dagAboveSplit, dagBelowSplit)
    }

    def show(pngName : String) : Unit = {
      import java.io.PrintWriter

      val title = clause.toPrologString

      val dotContent = new StringBuilder()
      dotContent.append("digraph G {\n")
      dotContent.append(s"""  label="$title";\n""")
      dotContent.append("  labelloc=t;\n")
      dotContent.append("  labeljust=l;\n")

      for (edge <- edges) {
        val from =
          "\"" + edge.from.toString.replace("\"", "\\\"") + "\""
        val to =
          "\"" + edge.to.toString.replace("\"", "\\\"") + "\""
        dotContent.append(s"  $from -> $to;\n")
      }

      dotContent.append("}\n")

      val pw = new PrintWriter("graph.dot")
      pw.write(dotContent.toString)
      pw.close()

      import sys.process._
      "dot -Tpng graph.dot -o " + pngName !

      "open " + pngName !
    }
  }

}
