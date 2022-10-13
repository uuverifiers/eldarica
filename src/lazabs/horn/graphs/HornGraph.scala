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
    "templateBool", "templateEq", "templateIneq")
  val edgeTypes = Seq("controlFlowHyperEdge", "dataFlowHyperEdge", "guardEdge", "relationSymbolArgumentEdge", "ASTLeft", "ASTRight"
    , "AST", "relationSymbolInstanceEdge", "argumentInstanceEdge", "clauseHeadEdge", "clauseBodyEdge", "clauseArgumentEdge", "data")
  var canonicalClassIDMap: Map[String, Int] = (for (n <- nodeTypes) yield n -> 0).toMap
  var globalNodeID = 0
  val nodeShapeMap: Map[String, String] = getNodeShapeMap(Map("relationSymbol" -> "box"))


  def getNodeShapeMap(updateMap: Map[String, String]): Map[String, String] = {
    val shapeMap = (for (n <- nodeTypes) yield n -> "circle").toMap
    for ((k, v) <- updateMap) shapeMap.updated(k, v)
    shapeMap
  }

  def createNode(nodeClass: String, readName: String, labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array(),
                 color: String = "black", fillColor: String = "while"): Node = {
    val classCanonicalID = canonicalClassIDMap(nodeClass)
    val canonicalIDName = getCanonicalName(nodeClass, classCanonicalID)
    val dotGraphName = canonicalIDName + ":" + readName
    val newNode = Node(globalNodeID, canonicalIDName, dotGraphName, nodeClass, nodeShapeMap(nodeClass))
    globalNodeID += 1
    canonicalClassIDMap.updated(nodeClass, canonicalClassIDMap(nodeClass) + 1)
    newNode
  }

  def getCanonicalName(nodeClass: String, canonicalID: Int): String = {
    nodeClass + "_" + canonicalID.toString
  }

  def drawDotGraph(nodeList: Array[Node], edgeMap: Map[String, Array[Edge]]): Unit = {
    val dotFileName =
      if (GlobalParameters.get.hornGraphType == HornGraphType.CDHG)
        GlobalParameters.get.fileName + ".hyperEdgeGraph.gv"
      else
        GlobalParameters.get.fileName + ".monoDirectionLayerGraph.gv"

    val writerGraph = new PrintWriter(new File(dotFileName)) //todo: open and close file by with:
    writerGraph.write("digraph dag { " + "\n")

    // draw nodes
    for (n <- nodeList) {
      val shapeString = " " + "shape" + "=" + n.shape + " "
      val nameString = " " + "label" + "=" + "\"" + n.dotGraphName + "\"" + " "
      val colorString = " " + "color" + "=" + n.color + " "
      val fillcolorString = " " + "fillcolor" + "=" + n.fillColor + " "
      writerGraph.write(n.nodeID.toString + " " + "[" + shapeString + nameString + colorString + fillcolorString + "]")
    }
    // todo: draw hyperedges

    // draw binary edges
    for ((et, edges) <- edgeMap; if edges.head.edge.length == 2; edge <- edges) {
      val styleString = " " + "shape" + "=" + edge.style + " "
      val nameString = " " + "label" + "=" + "\"" + edge.dotGraphName + "\"" + " "
      val colorString = " " + "color" + "=" + edge.color + " "
      writerGraph.write(edge.edge.head.toString + " -> " + edge.edge.tail.head.toString +
        " " + "[" + nameString + styleString + colorString + "]")
    }

    writerGraph.write("} " + "\n")
    writerGraph.close()

  }

  def outputJson(): Unit = {

  }

}


class CDHG(clauses: Clauses, templates: templateCollection) extends HornGraph(clauses: Clauses, templates: templateCollection) {

  var nodeMap: Map[Int, Node] = Map()
  var edgeMap: Map[String, Array[Edge]] = Map()
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
      println(Console.BLUE+"debug")
      val edgeClass = "relationSymbolArgumentEdge"
      edgeMap(edgeClass).+:(Edge(Array(argumentNodeID, headNodeID), "RSA", edgeClass))
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