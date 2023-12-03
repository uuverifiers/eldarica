/**
 * Copyright (c) 2011-2023 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.preprocessor

import ap.basetypes.{Leaf, Tree}
import ap.parser.IExpression._
import ap.parser._
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.bottomup.Util.{Dag, DagEmpty, DagNode}
import lazabs.horn.preprocessor.ClauseShortener.BTranslator

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap, HashSet => MHashSet, Stack => MStack}

object ClauseTermGraph {
  case class Edge(from : Node, to : Node)

  abstract class Node

  case class ConstNode(c : IConstant) extends Node {
    override def toString : String = c.c.name
  }

  case class AtomNode(a : IAtom) extends Node {
    val constants : Set[IConstant] =
      a.args.flatMap(
        term => SymbolCollector.constants(term).map(c => IConstant(c))).toSet
    override def toString : String = ap.SimpleAPI.pp(a)
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
}

class ClauseTermGraph(clause : Clause) {
  import ClauseTermGraph._

  def outgoing(n : Node) = edges.filter(e => e.from == n)
  def incoming(n : Node) = edges.filter(e => e.to == n)

  private val conjuncts =
    LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)
  private val curNodes = new ArrayBuffer[Node]
  private val curEdges = new ArrayBuffer[Edge]

  // Add one node for each constant
  clause.constants.foreach(c => curNodes += ConstNode(IConstant(c)))

  private val sources = clause.body.map(AtomNode)
  private val sink    = AtomNode(clause.head)

  (sources ++ Seq(sink)) foreach(curNodes += _)

  // Handle clause body
  for (source <- sources) {
    // Add each constant as outgoing
    for (constant <- source.constants) {
      val constantNode = ConstNode(constant)
      curEdges += Edge(source, constantNode)
    }
  }

  { // Handle clause head / sink
    // Add each constant as incoming
    for (constant <- sink.constants) {
      val constantNode = ConstNode(constant)
      curEdges += Edge(constantNode, sink)
    }
  }

  for (conjunct <- conjuncts) {
    conjunct match {
      case IBoolLit(true) => // ignore - used as pseudo-root
      case Eq(funApp@IFunApp(f, _), _) =>
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

  /**
   * Returns source nodes, but does not include the pseudo-root and the false
   * atom. This is useful for getting unbound terms.
   */
  val getSources : Iterable[Node] = nodes.filter(
    node => incoming(node).isEmpty && (node match {
      case SyncNode(IAtom(p, _)) => p != HornClauses.FALSE
      case _ => true
    }))

  // If there is more than one source, add a pseudo-root.
  // TODO: refactor
  val (getPseudoRoot, hasPseudoRoot) = if (getSources.size != 1) {
    val pseudoRoot = SyncNode(i(true))
    curNodes += pseudoRoot
    curEdges ++= getSources.map(node => Edge(pseudoRoot, node))
    (pseudoRoot, true)
  } else {
    (getSources.head, false)
  }
  // A clause always has a head, but it can be FALSE. Since FALSE doesn't have
  // any incoming edges, we add these manually.
  if (clause.head == IAtom(HornClauses.FALSE, Nil)) {
    val falseNode        = AtomNode(IAtom(HornClauses.FALSE, Nil))
    val sinksExceptFalse =
      nodes.filter(node => outgoing(node).isEmpty && node != falseNode)
    curEdges ++= sinksExceptFalse.map(node => Edge(node, falseNode))
  }

  def nodes : Iterable[Node] = curNodes
  def edges : Iterable[Edge] = curEdges

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

      val childNodes     = outgoing(node).map(edge => edge.to)
      val maybeChildDags = (for (childNode <- childNodes) yield {
        buildDagFromNode(childNode)
      }).toSeq

      if (maybeChildDags.exists(_.isEmpty)) {
        None
      } // Cycle detected in one of the child nodes
      else {
        // TODO: order children so that the cuts are minimized
        val childDags           = maybeChildDags.map(_.get).sorted(dagOrdering)
        val nextDag : Dag[Node] =
          if (childDags isEmpty) {
            DagEmpty
          } else {
            var next : Dag[Node] = DagEmpty
            for (subDag <- childDags if !subDag.isEmpty) {
              next = DagNode(subDag.head, Nil, next)
            }
            next
          }

        visiting -= node

        val dagNode =
          DagNode(node, childDags.indices.map(_ + 1).toList, nextDag)
            .substitute(
              childDags.indices.map(_ + 1).toList.zip(childDags).toMap)
        createdSubDags += ((node, dagNode))

        Some(dagNode)
      }
    }

    buildDagFromNode(getPseudoRoot) match {
      case Some(dag) => Some(dag.collapseNodes)
      case None => None
    }
  }

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
                           glueNodeInstantiator : List[Int] => T,
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

    val orphanNodeInds             = new ArrayBuffer[(T, List[Int])]
    val orphanedNodeInds           = new ArrayBuffer[(DagNode[(T, Int)], Int)]
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
        orphanNodeInds += n.d._1 -> orphans
        orphanedNodeInds += n -> nInd
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
    // Create the glue node using the information of orphaned nodes
    val glueNode : T = glueNodeInstantiator(orphanedNodeInds.map(_._2).toList)

    val root          = dag.asInstanceOf[DagNode[T]]
    val dagAboveSplit =
      DagNode(root.d, root.children.diff(orphansFromPseudoRoot), root.next)
        .substitute(Map(glueInd -> DagNode(glueNode, List(), DagEmpty)))
        .updated(orphanedNodeAboveUpdateMap.toMap).elimUnconnectedNodes

    val dagBelowSplit = {
      val belowOldDag = dag.drop(glueInd)
      var next        = belowOldDag
      // orphaned nodes are replicated below
      for (((orphanedNode, orphanInds), i) <- orphanNodeInds.zipWithIndex) {
        // offset children by the number of orphans that were added
        val newChildren = orphanInds.map(ind => ind + i + 1)
        val newNode     = DagNode(orphanedNode, newChildren, next)
        next = newNode
      }
      val pseudoChildren = orphansFromPseudoRoot.map(
        childInd => childInd - glueInd + orphanNodeInds.size + 1)
      DagNode(glueNode, (1 to orphanNodeInds.size).toList ++
        pseudoChildren, next)
    }

//    lazabs.horn.bottomup.Util.show(dag, "dag", false)
//    println("\nabove\n")
//    lazabs.horn.bottomup.Util.show(dagAboveSplit, "aboveSplit", false)
//    dagAboveSplit.prettyPrint
//    println("\nbelow\n")
//    lazabs.horn.bottomup.Util.show(dagBelowSplit, "belowSplit", false)
//    dagBelowSplit.prettyPrint
    println

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

object ClauseSplitterFuncsAndUnboundTerms {
  import HornPreprocessor._

  object BTranslator {

    def apply(tempPreds   : Set[Predicate],
              backMapping : Map[Clause, Clause]) : BTranslator = {
      val extendedMapping =
        for ((newClause, oldClause) <- backMapping) yield {
          assert(newClause.body.size == oldClause.body.size)
          val indexTree =
            Tree(-1, (for (n <- newClause.body.indices) yield Leaf(n)).toList)
          (newClause, (oldClause, indexTree))
        }
      new BTranslator(tempPreds, extendedMapping)
    }

    def withIndexes(tempPreds   : Set[Predicate],
                    backMapping : Map[Clause, (Clause, Tree[Int])])
    : BTranslator =
      new BTranslator(tempPreds, backMapping)

  }

  class BTranslator private(tempPreds   : Set[Predicate],
                            backMapping : Map[Clause, (Clause, Tree[Int])])
    extends BackTranslator {

    def translate(solution : Solution) = solution -- tempPreds

    def translate(cex : CounterExample) =
      if (tempPreds.isEmpty && backMapping.isEmpty) {
        cex
      } else {
        val res = simplify(translateCEX(cex).elimUnconnectedNodes)

        assert(res.subdagIterator forall {
          case dag@DagNode((state, clause@Clause(head, body, constraint)),
                           children, _) =>
            // syntactic check: do clauses fit together?
            state.pred == head.pred &&
              children.size == body.size &&
              ((children.iterator zip body.iterator) forall {
                case (c, IAtom(pred, _)) =>
                  c > 0 && dag(c)._1.pred == pred
              })
        })

        res
      }

    private def translateCEX(dag : CounterExample) : CounterExample =
      dag match {
        case DagNode(p@(a, clause), children, next) =>
          val newNext = translateCEX(next)
          backMapping get clause match {
            case Some((oldClause, indexTree)) =>
              val newChildrenAr =
                new Array[Int](oldClause.body.size)
              for ((c, t) <- children.iterator zip indexTree.children.iterator)
                allProperChildren(dag drop c, t, newChildrenAr, c)
              DagNode((a, oldClause), newChildrenAr.toList, newNext)
            case None => DagNode(p, children, newNext)
          }
        case DagEmpty => DagEmpty
      }

    private def allProperChildren(dag           : CounterExample,
                                  indexTree     : Tree[Int],
                                  newChildrenAr : Array[Int],
                                  offset        : Int) : Unit = {
      val DagNode((IAtom(p, _), _), children, _) = dag
      if (tempPreds contains p) {
        for ((c, t) <- children.iterator zip indexTree.children.iterator)
          allProperChildren(dag drop c, t, newChildrenAr, offset + c)
      } else {
        newChildrenAr(indexTree.d) = offset
      }
    }
  }
}

/**
 * Split clauses such that there is at most one function in the specified set of
 * functions.
 *
 * The preprocessor expects as invariant that the direction of function
 * applications of the input function set is from the body to the head in all
 * clauses, i.e., in 'f(x) = y', 'y' must be closer to the head of the clause
 * than 'x'. Identity transformation is applied otherwise.
 *
 * Optionally, expects an ordering over functions, which will attempt to order
 * the appearance of functions in that order when possible.
 */
class ClauseSplitterFuncsAndUnboundTerms(
  functionsToSplitOn            : Set[IFunction],
  sortsForUnboundTermsToSplitOn : Set[Sort],
  functionOrdering              : Option[Ordering[IFunction]] = None)
  extends HornPreprocessor {
  import HornPreprocessor._

  private val tempPredicates    = new MHashSet[Predicate]
  private val clauseBackMapping = new MHashMap[Clause, (Clause, Tree[Int])]

  val name : String = "splitting clauses with functions : {" +
    functionsToSplitOn.mkString(",") + "}"

  override def isApplicable(clauses          : Clauses,
                            frozenPredicates : Set[Predicate]) : Boolean = {
    // TODO: Update this based on what exactly this preprocessor does.
    clauses.exists(
      c => FunctionCollector(c.constraint)
        .intersect(functionsToSplitOn).nonEmpty ||
        c.constants.exists(sortsForUnboundTermsToSplitOn
                             contains Sort.sortOf(_)))
  }

  override def process(clauses          : Clauses,
                       hints            : VerificationHints,
                       frozenPredicates : Set[Predicate])
  : (Clauses, VerificationHints, BackTranslator) = {
    import ClauseTermGraph._

    val newInitialPreds = hints

    val unchangedClauses = new MHashMap[Clause, Seq[Clause]]

    val remainingClauses = new MStack[Clause]
    clauses.reverse.foreach(remainingClauses push)

    val clauseGraphs : Map[Clause, ClauseTermGraph] = clauses.map(
      clause => (clause, new ClauseTermGraph(clause))).toMap

    // A custom ordering used when combining subDags during topological sorting
    val dagOrdering : Ordering[Dag[Node]] = new Ordering[Dag[Node]] {
      // Extract the last FunAppNode from a Dag[Node] containing a
      // function to split on.
      def lastFunAppNode(dag : Dag[Node]) : Option[FunAppNode] = {
        dag.subdagIterator.toList.reverse.find(
          n => n.d.isInstanceOf[FunAppNode] &&
            functionsToSplitOn
              .contains(n.d.asInstanceOf[FunAppNode].funApp.fun)) match {
          case Some(DagNode(node@FunAppNode(IFunApp(fun, _), _), _, _))
            if functionsToSplitOn contains fun =>
            Some(node)
          case _ => None
        }
      }
      // If a subdag contains no fun apps, it comes first, otherwise the one
      // with the "least" function as its last node comes first.
      override def compare(x : Dag[Node], y : Dag[Node]) : Int = {
        (lastFunAppNode(x), lastFunAppNode(y)) match {
          case (None, Some(_)) if functionOrdering.nonEmpty => -1 // x first
          case (Some(_), None) if functionOrdering.nonEmpty => 1 // y first
          case (Some(fx), Some(fy)) if functionOrdering.nonEmpty =>
            functionOrdering.get.compare(fx.funApp.fun, fy.funApp.fun)
          case _ =>
            // sort by Dag size, put smaller DAG first
            if (x.size <= y.size) -1 else 1
        }
        // TOdO: order so that sync nodes appear as early as possible.
      }
    }

    val clauseDags : Map[Clause, Dag[Node]] = clauseGraphs.map{
      case (clause, graph) =>
        graph.topologicalSort(dagOrdering) match {
          case Some(dag) => (clause, dag)
          case None =>
            println(
              s"Warning: cannot apply ($name) because a clause cannot be" +
                "converted to a DAG (from body to head)\n" + clause
                .toPrologString + "\n" +
                "Applying identity transformation instead.")
            return (clauses, hints, IDENTITY_TRANSLATOR)
        }
    }

    val clauseNewDags  = new MHashMap[Clause, Seq[Dag[Node]]]
    val clauseNewPreds = new MHashMap[Clause, Set[Predicate]]

    var gluePredCounter = -1
    def newGluePred(argSorts : Seq[Sort]) : Predicate = {
      gluePredCounter += 1
      val newPred = new MonoSortedPredicate(
        s"_Glue$gluePredCounter", argSorts)
      tempPredicates += newPred
      // TODO: update hints
      newPred
    }

    for (clause <- clauses) {
      val clauseGraph = clauseGraphs(clause)
      val clauseDag   = clauseDags(clause)

      val unboundTermNodesToSplitOn = clauseGraph.getSources.filter{
        case node : ConstNode =>
          sortsForUnboundTermsToSplitOn contains Sort.sortOf(node.c)
        case _ => false
      }.map(_.asInstanceOf[ConstNode])

      val funAppNodesToSplitOn = clauseGraph.nodes.filter{
        case node : FunAppNode => functionsToSplitOn contains node.funApp.fun
        case _ => false
      }.map(_.asInstanceOf[FunAppNode])

      if (unboundTermNodesToSplitOn.size + funAppNodesToSplitOn.size < 2) {
        println(s"No splitting needed for ${clause.toPrologString}")
        unchangedClauses += clause -> Seq(clause)
      } else {
        println(s"Splitting clause ${clause.toPrologString}")
        if (unboundTermNodesToSplitOn.nonEmpty) {
          println(s"It has ${unboundTermNodesToSplitOn.size} " +
                    s"unbound terms to split on: $unboundTermNodesToSplitOn")
        }
        if (funAppNodesToSplitOn.nonEmpty) {
          println(s"It has ${funAppNodesToSplitOn.size} " +
                    s"fun apps to split on: $funAppNodesToSplitOn")
        }

        // Split after unbounded heap terms, and after the return term of funs.
        val termsToSplitOn : Set[Node] =
          (unboundTermNodesToSplitOn ++
            funAppNodesToSplitOn.map(f => ConstNode(f.toArg))).toSet

        val toSplitNodesSorted =
          clauseDag.iterator.filter(termsToSplitOn contains).toSeq

        val clauseDags  = new MStack[Dag[Node]]
        val clausePreds = new MHashSet[Predicate]
        clauseDags push clauseDag
        for (term <- toSplitNodesSorted.init) {
          val curDag = clauseDags pop

          def connectorNodeInstantiator(orphanedNodes : List[Int]) : Node = {
            val newPredArgs =
              for (ind <- orphanedNodes if curDag(ind).isInstanceOf[ConstNode])
                yield curDag(ind).asInstanceOf[ConstNode].c.c
            val newPred = newGluePred(newPredArgs.map(Sort.sortOf(_)))
            clausePreds += newPred
            val newAtom = IAtom(newPred, newPredArgs)
            AtomNode(newAtom)
          }
          // The splitting should fail if it is attempted for non-constant
          // nodes.
          def isSplittable(node : Node) : Boolean = node.isInstanceOf[ConstNode]

          val (headDag, tailDag) = clauseGraph.splitDagAfterNode(
            curDag, term, connectorNodeInstantiator, isSplittable,
            clauseGraph.hasPseudoRoot)
          clauseDags push headDag
          clauseDags push tailDag
        }
        //        println("\nStarting DAG: ")
        //        clauseDag.prettyPrint

        //        println("\nSplit DAG(s):")
        //        for ((dag, i) <- clauseDags.reverse.zipWithIndex) {
        //          println(s"DAG $i:")
        //          dag.prettyPrint
        //          println
        //        }
        clauseNewDags += clause -> clauseDags.reverse
        clauseNewPreds += clause -> clausePreds.toSet
      }
    }

    def clauseDagToClause(clauseDag : Dag[Node]) : Clause = {
      val nodes = clauseDag.subdagIterator.toList
      // There must at least be two nodes: one for head and one for the body.
      assert(nodes.size >= 2)

      // head is always the last node
      assert(nodes.last.d.isInstanceOf[AtomNode])
      val head : IAtom = nodes.last.d.asInstanceOf[AtomNode].a

      val body      = new ArrayBuffer[IAtom]
      val conjuncts = new ArrayBuffer[IFormula]
      for (node : DagNode[Node] <- nodes.init) {
        node.d match {
          case FunAppNode(_, f) => conjuncts += f
          case SyncNode(f) => if (!f.isTrue) conjuncts += f
          case AtomNode(a) => body += a
          case ConstNode(_) => // nothing needed
        }
      }
      Clause(head, body.toList, and(conjuncts))
    }

    val clauseToNewClauses : Map[Clause, Seq[Clause]] = (clauseNewDags.map(
      pair => pair._1 -> pair._2.map(clauseDagToClause)) ++
        unchangedClauses).toMap

    for ((clause, newClauses) <- clauseToNewClauses.filter(
      c => !unchangedClauses.contains(c._1))) {
      println("\n\nOld:")
      println(clause.toPrologString)
      println("\nNew:")
      newClauses.foreach(c => println(c.toPrologString))
    }
    println

    //    while (remainingClauses nonEmpty) {
    /*
     *  clauseDag is topologically sorted, so we can simply split the terms in
     *  the order that they appear in the DAG.
     *  We create new clauses by iteratively splitting clauseDag into its
     *   sub-DAGs, and each one we split from the head will be a new clause.
     *   1) For function applications
     *  Let n be the node that we split on. In the sub-DAG we split (the new
     *  clause):
     *    - create a new RelNode (for the new head predicate)
     *      - create a new predicate, and create an IAtom using that predicate
     *        with all ConstNode nodes in the path from root to node n+1
     *        (the result of the function application).
     *      - create a new RelNode n' using the predicate from the previous
     *      step.
     *
     *      - create two copies of clauseDag: dag1, dag2.
     *      - update n' as the single child of n.
     *      - update the children of all nodes in dag1 that has index >= n+1
     *        to be n+1 (the new node n')
     *      - In dag2, add n' as the root node.
     *      - todo: easy way to take subdag2?
     *  Repeat this until there are no more functions applications to split
     *  on.
     */

    //    }
    val translator = BTranslator.withIndexes(tempPredicates.toSet,
                                             clauseBackMapping.toMap)
    (clauseToNewClauses.flatMap(_._2).toSeq, hints, translator)
  }
}
