package lazabs.horn.graphs

import ap.parser.IAtom
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.preprocessor.HornPreprocessor.Clauses
import org.antlr.analysis.SemanticContext.TruePredicate

import java.io.{BufferedWriter, File, FileWriter, PrintWriter}

object HornGraphType extends Enumeration {
  val CDHG, CG = Value
}

case class templateCollection(unlabeled: VerificationHints = VerificationHints(Map()), positive: VerificationHints = VerificationHints(Map()),
                              negative: VerificationHints = VerificationHints(Map()), predicted: VerificationHints = VerificationHints(Map()))

case class Node(nodeID: Int, canonicalName: String, dotGraphName: String, typeName: String, readName: String, shape: String,
                labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array(),
                color: String = "black", fillColor: String = "while")


case class Edge(edge: Array[Int], dotGraphName: String, typeName: String, style: String = "solid", color: String = "black")

class HornGraph(clauses: Clauses, templates: templateCollection) {
  val graphNameMap = Map(HornGraphType.CDHG -> "hyperEdgeGraph", HornGraphType.CG -> "monoDirectionLayerGraph")

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

  def checkNodeExistenceByString(readName: String, nodeList: Array[Node]): Boolean = {
    if (nodeList.map(_.readName).contains(readName)) true else false

  }

  def createNode(nodeType: String, readName: String, labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array(),
                 color: String = "black", fillColor: String = "while"): Node = {
    val nodeTypeCanonicalID = canonicalNodeTypeIDMap(nodeType)
    val canonicalIDName = getCanonicalName(nodeType, nodeTypeCanonicalID)
    val dotGraphName = globalNodeID.toString + ":" + getAbbrevCanonicalName(nodeType, nodeTypeCanonicalID) + ":" + readName
    val newNode = Node(globalNodeID, canonicalIDName, dotGraphName, nodeType, readName, nodeShapeMap(nodeType))
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
    val dotFileName = GlobalParameters.get.fileName + "." + graphNameMap(GlobalParameters.get.hornGraphType) + ".gv"

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

  def outputJson(nodeList: Array[Node], edgeMap: Map[String, Array[Edge]]): Unit = {
    val nodeIndicesList = for (nt <- nodeTypes) yield {
      nt + "Indices" -> nodeList.filter(_.typeName == nt)
    }
    val nodeSymbolList = nodeList.sortBy(_.nodeID)


    val jsonFileName = GlobalParameters.get.fileName + "." + graphNameMap(GlobalParameters.get.hornGraphType) + ".JSON"
    val writer = new PrintWriter(new File(jsonFileName))
    writer.write("{\n")

    //write nodeID
    writeOneLineJson("nodeIDList", nodeSymbolList.map(_.nodeID).toSeq.toString)
    //write nodeSymbolList
    writeOneLineJson("nodeSymbolList", nodeSymbolList.map("\"" + _.canonicalName + "\"").toSeq.toString)
    //write indices
    for ((nt, nl) <- nodeIndicesList) {
      val listString = nl.map(_.nodeID).toSeq.toString()
      writeOneLineJson(nt, listString)
    }
    //write edges
    for ((edgeType,edges)<-edgeMap){
      val listString = edges.map(x=>seqToString(x.edge.toSeq.toString())).toSeq.toString()
      writeOneLineJson(edgeType, listString)
    }

    writer.write("}")
    writer.close()

    def writeOneLineJson(head: String, body: String): Unit =
      writer.write("\"" + head + "\"" + ":\n"  + seqToString(body)  + "," + "\n")

    def seqToString(s: String): String = {
      if (s.contains("("))
        "["+s.substring(s.indexOf("(") + 1, s.indexOf(")")) + "]"
      else
        s
    }
  }

}


class CDHG(clauses: Clauses, templates: templateCollection) extends HornGraph(clauses: Clauses, templates: templateCollection) {

  var nodeMap: Map[Int, Node] = Map(0 -> createNode("dummy", "dummy"))
  var edgeMap: Map[String, Array[Edge]] = (for (t <- edgeTypes) yield {
    if (ternaryEdgeTypes.contains(t))
      t -> Array(Edge(Array(0, 0, 0), "dummy:" + t, t))
    else
      t -> Array(Edge(Array(0, 0), "dummy:" + t, t))
  }).toMap
  for (clause <- clauses) {
    println(clause)
    //draw control flow
    //create head relation symbol node
    createRelationSymbolNodesAndArguments(clause.head)


    //create body nodes
    for (b <- clause.body)
      createRelationSymbolNodesAndArguments(b)

  }

  drawDotGraph(nodeList = nodeMap.values.toArray, edgeMap = edgeMap)
  outputJson(nodeList = nodeMap.values.toArray, edgeMap = edgeMap)


  def createRelationSymbolNodesAndArguments(atom: IAtom): Unit = {
    val nodeFromExistedList = nodeMap.values.find(_.readName == atom.pred.name)
    if (nodeFromExistedList.isEmpty) { //if node not existed in nodeMap, create new rs node and rsa nodes
      val rsHeadNode: Node = createNode("relationSymbol", atom.pred.name)
      nodeMap += (rsHeadNode.nodeID -> rsHeadNode)
      for (a <- atom.args) {
        //create clause head argument nodes
        val argumentNodeID = globalNodeID
        nodeMap += (globalNodeID -> createNode("relationSymbolArgument", a.toString))
        // add edges with head node
        val edgeType = "relationSymbolArgumentEdge"
        edgeMap = edgeMap.updated(edgeType, edgeMap(edgeType).+:(Edge(Array(argumentNodeID, rsHeadNode.nodeID),
          "RSA", edgeType)))
      }
    }
  }

}

class CG(clauses: Clauses, templates: templateCollection) extends HornGraph(clauses: Clauses, templates: templateCollection) {

}