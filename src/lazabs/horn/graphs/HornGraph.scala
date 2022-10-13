package lazabs.horn.graphs

import lazabs.horn.abstractions.VerificationHints

object HornGraphType extends Enumeration {
  val CDHG, CG = Value
}

case class templateCollection(unlabeled: VerificationHints = VerificationHints(Map()), positive: VerificationHints = VerificationHints(Map()),
                              negative: VerificationHints = VerificationHints(Map()), predicted: VerificationHints = VerificationHints(Map()))

case class Node(nodeID: Int, canonicalName: String, dotGraphName: String, className: String, shape: String,
                labelList: Array[Int] = Array(), predictedLabelList: Array[Int] = Array(),
                color: String = "black", fillColor: String = "while")


case class Edge(edge: Array[Int], dotGraphName: String, className: String)

class HornGraph(file: String) {

  val nodeTypes = Seq("relationSymbol", "initial", "false", "relationSymbolArgument", "variables", "operator", "constant", "guard",
    "clause", "clauseHead", "clauseBody", "clauseArgument")
  var canonicalClassIDMap: Map[String, Int] = (for (n <- nodeTypes) yield n -> 0).toMap
  var globalID = 0

  def drawDotGraph(nodeList: Array[Node], edgeMap: Map[String, Array[Edge]]): Unit = {

  }

  def outputJson(): Unit = {

  }

}
