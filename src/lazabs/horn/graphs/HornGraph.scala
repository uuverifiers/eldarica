package lazabs.horn.graphs

import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

import java.io.{File, PrintWriter}

object HornGraphType extends Enumeration {
  val CDHG, CG = Value
}

case class templateCollection(unlabeled: VerificationHints = VerificationHints(Map()), positive: VerificationHints = VerificationHints(Map()),
                              negative: VerificationHints = VerificationHints(Map()), predicted: VerificationHints = VerificationHints(Map()))

case class Node(nodeID: Int, canonicalName: String, dotGraphName: String, className: String, shape: String,
                labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array(),
                color: String = "black", fillColor: String = "while")


case class Edge(edge: Array[Int], dotGraphName: String, className: String, style: String = "solid", color: String = "black")

class HornGraph(clauses: Clauses, templates: templateCollection) {

  val nodeTypes = Seq("relationSymbol", "initial", "false", "relationSymbolArgument", "variables", "operator", "constant", "guard",
    "clause", "clauseHead", "clauseBody", "clauseArgument",
    "templateBool", "templateEq", "templateIneq", "dummy")
  val nodeTypesAbbrev = Map("relationSymbol" -> "rs", "initial" -> "initial", "false" -> "false",
    "relationSymbolArgument" -> "rsa", "variables" -> "var", "operator" -> "op", "constant" -> "c", "guard" -> "g",
    "clause" -> "cla", "clauseHead" -> "ch", "clauseBody" -> "cb", "clauseArgument" -> "ca",
    "templateBool" -> "tb", "templateEq" -> "teq", "templateIneq" -> "tineq", "dummy" -> "dm")
  val ternaryEdgeTypes = Seq("controlFlowHyperEdge", "dataFlowHyperEdge", "ternaryHyperEdge")
  val binaryEdgeTypes = Seq("guardEdge", "relationSymbolArgumentEdge", "ASTLeft", "ASTRight"
    , "AST", "relationSymbolInstanceEdge", "argumentInstanceEdge", "clauseHeadEdge", "clauseBodyEdge",
    "clauseArgumentEdge", "data", "binaryEdges")
  val edgeTypes = ternaryEdgeTypes ++ binaryEdgeTypes
  var canonicalNodeTypeIDMap: Map[String, Int] = (for (n <- nodeTypes) yield n -> 0).toMap
  var globalNodeID = 0
  val nodeShapeMap: Map[String, String] = getNodeShapeMap(Map("relationSymbol" -> "box", "dummy" -> "box"))


  def getNodeShapeMap(updateMap: Map[String, String]): Map[String, String] = {
    (for (n <- nodeTypes) yield {
      if (updateMap.keys.toSeq.contains(n))
        n -> updateMap(n)
      else
        n -> "circle"
    }).toMap
  }


  def createNode(nodeType: String, readName: String, labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array(),
                 color: String = "black", fillColor: String = "while"): Node = {
    val nodeTypeCanonicalID = canonicalNodeTypeIDMap(nodeType)
    val canonicalIDName = getCanonicalName(nodeType, nodeTypeCanonicalID)
    val dotGraphName = globalNodeID.toString + ":" + getAbbrevCanonicalName(nodeType, nodeTypeCanonicalID) + ":" + readName
    val newNode = Node(globalNodeID, canonicalIDName, dotGraphName, nodeType, nodeShapeMap(nodeType))
    globalNodeID += 1
    canonicalNodeTypeIDMap = canonicalNodeTypeIDMap.updated(nodeType, canonicalNodeTypeIDMap(nodeType) + 1)
    newNode
  }

  def getCanonicalName(nodeType: String, canonicalID: Int): String = {
    nodeType + "_" + canonicalID.toString
  }

  def getAbbrevCanonicalName(nodeType: String, canonicalID: Int): String = {
    nodeTypesAbbrev(nodeType) + "_" + canonicalID.toString
  }

  def drawDotGraph(nodeList: Array[Node], edgeMap: Map[String, Array[Edge]]): Unit = {
    val dotFileName =
      if (GlobalParameters.get.hornGraphType == HornGraphType.CDHG)
        GlobalParameters.get.fileName + ".hyperEdgeGraph.gv"
      else
        GlobalParameters.get.fileName + ".monoDirectionLayerGraph.gv"

    val writerGraph = new PrintWriter(new File(dotFileName)) 
    writerGraph.write("digraph dag { " + "\n")

    // draw nodes
    for (n <- nodeList) {
      val shapeString = " " + "shape" + "=" + n.shape + " "
      val nameString = " " + "label" + "=" + "\"" + n.dotGraphName + "\"" + " "
      val colorString = " " + "color" + "=" + n.color + " "
      val fillcolorString = " " + "fillcolor" + "=" + n.fillColor + " "
      writerGraph.write(n.nodeID.toString + " " + "[" + shapeString + nameString + colorString + fillcolorString + "]" + "\n")
    }
    // todo: draw hyperedges

    // draw binary edges
    for ((et, edges) <- edgeMap; if edges.head.edge.length == 2; edge <- edges) {
      val styleString = " " + "shape" + "=" + edge.style + " "
      val nameString = " " + "label" + "=" + "\"" + edge.dotGraphName + "\"" + " "
      val colorString = " " + "color" + "=" + edge.color + " "
      writerGraph.write(edge.edge.head.toString + " -> " + edge.edge.tail.head.toString +
        " " + "[" + nameString + styleString + colorString + "]" + "\n")
    }

    writerGraph.write("} " + "\n")
    writerGraph.close()

  }

  def outputJson(): Unit = {

  }

}


class CDHG(clauses: Clauses, templates: templateCollection) extends HornGraph(clauses: Clauses, templates: templateCollection) {

  var nodeMap: Map[Int, Node] = Map(0 -> createNode("dummy", "dummy")) //todo add a dummy node 0
  var edgeMap: Map[String, Array[Edge]] = (for (t <- edgeTypes) yield {
    if (ternaryEdgeTypes.contains(t))
      t -> Array(Edge(Array(0, 0, 0), "dummy:" + t, t))
    else
      t -> Array(Edge(Array(0, 0), "dummy:" + t, t))
  }).toMap
  for (clause <- clauses) {
    //draw control flow
    //create clause head node
    val headNodeID = globalNodeID
    nodeMap += (globalNodeID -> createNode("relationSymbol", clause.head.pred.name))

    for (a <- clause.head.args) {
      //create clause head argument nodes
      val argumentNodeID = globalNodeID
      nodeMap += (globalNodeID -> createNode("relationSymbolArgument", a.toString))
      // add edges with head node
      val edgeClass = "relationSymbolArgumentEdge"
      edgeMap = edgeMap.updated(edgeClass, edgeMap(edgeClass).+:(Edge(Array(argumentNodeID, headNodeID), "RSA", edgeClass)))
    }


    //create body nodes
    for (b <- clause.body)
      nodeMap += (globalNodeID -> createNode("relationSymbol", b.pred.name))

  }
  //draw control flow
  drawDotGraph(nodeList = nodeMap.values.toArray, edgeMap = edgeMap)
}

class CG(clauses: Clauses, templates: templateCollection) extends HornGraph(clauses: Clauses, templates: templateCollection) {

}