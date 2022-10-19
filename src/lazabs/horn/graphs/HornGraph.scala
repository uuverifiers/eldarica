package lazabs.horn.graphs

import ap.parser.IExpression.{Conj, Difference, Disj, Eq, EqLit, EqZ, Geq, GeqZ}
import lazabs.horn.graphs.GraphUtils._
import ap.parser.{IAtom, IBinJunctor, IBoolLit, IConstant, IExpression, IFormula, IIntLit, INot, IPlus, IQuantified, ITerm, ITimes, IVariable, LineariseVisitor, SymbolCollector}
import ap.terfor.ConstantTerm
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.preprocessor.HornPreprocessor.Clauses
import org.antlr.analysis.SemanticContext.TruePredicate

import java.io.{BufferedWriter, File, FileWriter, PrintWriter}

object HornGraphType extends Enumeration {
  val CDHG, CG = Value
}

object NodeAndEdgeType {
  //node definition
  val nodeTypes = Seq("relationSymbol", "initial", "false", "relationSymbolArgument", "variables", "operator", "constant", "guard",
    "clause", "clauseHead", "clauseBody", "clauseArgument",
    "templateBool", "templateEq", "templateIneq", "dummy", "unknown", "empty")
  val nodeTypesAbbrev = Map("relationSymbol" -> "rs", "initial" -> "initial", "false" -> "false",
    "relationSymbolArgument" -> "rsa", "variables" -> "var", "operator" -> "op", "constant" -> "c", "guard" -> "g",
    "clause" -> "cla", "clauseHead" -> "ch", "clauseBody" -> "cb", "clauseArgument" -> "ca",
    "templateBool" -> "tb", "templateEq" -> "teq", "templateIneq" -> "tineq", "dummy" -> "dm", "unknown" -> "unk",
    "empty" -> "e")

  // edge definition
  val ternaryEdgeTypes = Seq("controlFlow", "dataFlow", "ternary").map(_ + "HyperEdge")
  val binaryEdgeTypes = Seq("guard", "relationSymbolArgument", "ASTLeft", "ASTRight"
    , "AST", "relationSymbolInstance", "argumentInstance", "clauseHead", "clauseBody",
    "clauseArgument", "data", "binary").map(_ + "Edge")
  val templateEdgeTypes = Seq("template", "templateAST").map(_ + "Edge")
  val edgeTypes = ternaryEdgeTypes ++ binaryEdgeTypes ++ templateEdgeTypes
  val edgeTypesAbbrev = Map("controlFlowHyperEdge" -> "CFHE", "dataFlowHyperEdge" -> "DFHE", "ternaryHyperEdge" -> "te",
    "guardEdge" -> "G", "relationSymbolArgumentEdge" -> "RSA", "ASTLeftEdge" -> "ASTL", "ASTRightEdge" -> "ASTR"
    , "ASTEdge" -> "AST", "relationSymbolInstanceEdge" -> "RSI", "argumentInstanceEdge" -> "AI", "clauseHeadEdge" -> "CH",
    "clauseBodyEdge" -> "CB", "clauseArgumentEdge" -> "CA", "dataEdge" -> "data", "binaryEdge" -> "be")

}

case class templateCollection(unlabeled: VerificationHints = VerificationHints(Map()), positive: VerificationHints = VerificationHints(Map()),
                              negative: VerificationHints = VerificationHints(Map()), predicted: VerificationHints = VerificationHints(Map()))

case class Node(nodeID: Int, canonicalName: String, dotGraphName: String, typeName: String, var readName: String, shape: String,
                labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array(),
                color: String = "black", fillColor: String = "while", argumentIndex: Int = -1,
                rsName: String = "", clauseID: Int = -1)

case class Edge(edge: Array[Int], dotGraphName: String, typeName: String, style: String = "solid", color: String = "black")

class HornGraph(clauses: Clauses, templates: templateCollection) {


  var globalNodeID = 0
  var canonicalNodeTypeIDMap: Map[String, Int] = (for (n <- NodeAndEdgeType.nodeTypes) yield n -> 0).toMap
  val nodeShapeMap: Map[String, String] = getNodeShapeMap(Map("relationSymbol" -> "box",
    "initial" -> "box", "dummy" -> "box", "guard" -> "box"))
  val graphNameMap = Map(HornGraphType.CDHG -> "hyperEdgeGraph", HornGraphType.CG -> "monoDirectionLayerGraph")


  var nodeMap: Map[Int, Node] = Map()
  val dummyNode = createNode("dummy", "dummy")
  var edgeMap: Map[String, Array[Edge]] = (for (t <- NodeAndEdgeType.edgeTypes) yield {
    if (NodeAndEdgeType.ternaryEdgeTypes.contains(t))
      t -> Array(Edge(Array(0, 0, 0), "dummy:" + t, t))
    else
      t -> Array(Edge(Array(0, 0), "dummy:" + t, t))
  }).toMap

  //create initial rs node
  val initialNode = createNode("initial", "initial")
  //create global constants
  val globalTrueNode = createNode("constant", "true")

  def getNodeShapeMap(updateMap: Map[String, String]): Map[String, String] = {
    (for (n <- NodeAndEdgeType.nodeTypes) yield {
      if (updateMap.keys.toSeq.contains(n))
        n -> updateMap(n)
      else
        n -> "circle"
    }).toMap
  }


  def createNode(nodeType: String, readName: String, labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array(),
                 color: String = "black", fillColor: String = "while", argumentIndex: Int = -1,
                 rsName: String = "", clauseID: Int = -1): Node = {
    val nodeTypeCanonicalID = canonicalNodeTypeIDMap(nodeType)
    val canonicalIDName = getCanonicalName(nodeType, nodeTypeCanonicalID)
    val dotGraphName = globalNodeID.toString + ":" + getAbbrevCanonicalName(nodeType, nodeTypeCanonicalID) + ":" + readName
    val newNode = Node(globalNodeID, canonicalIDName, dotGraphName, nodeType, readName, nodeShapeMap(nodeType),
      argumentIndex = argumentIndex, rsName = rsName, clauseID = clauseID)
    globalNodeID += 1
    canonicalNodeTypeIDMap = canonicalNodeTypeIDMap.updated(nodeType, canonicalNodeTypeIDMap(nodeType) + 1)
    nodeMap += (newNode.nodeID -> newNode)
    newNode
  }

  def createEdge(edgeType: String, edge: Array[Int]): Unit = {
    edgeMap = edgeMap.updated(edgeType, edgeMap(edgeType).+:(Edge(edge, NodeAndEdgeType.edgeTypesAbbrev(edgeType), edgeType)))
    if (edge.length == 2) { //add global binary
      if (edgeType == "ASTLeftEdge" || edgeType == "ASTRightEdge") {
        val etype = "ASTEdge"
        edgeMap = edgeMap.updated(etype, edgeMap(etype).+:(Edge(edge, NodeAndEdgeType.edgeTypesAbbrev(etype), etype)))
      }
      val etype = "binaryEdge"
      edgeMap = edgeMap.updated(etype, edgeMap(etype).+:(Edge(edge, NodeAndEdgeType.edgeTypesAbbrev(etype), etype)))
    } else { //add global ternary edges
      val etype = "ternaryHyperEdge"
      edgeMap = edgeMap.updated(etype, edgeMap(etype).+:(Edge(edge, NodeAndEdgeType.edgeTypesAbbrev(etype), etype)))
    }
  }

  def getCanonicalName(nodeType: String, canonicalID: Int): String = {
    nodeType + "_" + canonicalID.toString
  }

  def getAbbrevCanonicalName(nodeType: String, canonicalID: Int): String = {
    NodeAndEdgeType.nodeTypesAbbrev(nodeType) + "_" + canonicalID.toString
  }

  def drawDotGraph(nodeList: Array[Node], edgeMap: Map[String, Array[Edge]]): Unit = {
    val dotFileName = GlobalParameters.get.fileName + "." + graphNameMap(GlobalParameters.get.hornGraphType) + ".gv"

    val writerGraph = new PrintWriter(new File(dotFileName))
    writerGraph.write("digraph dag { " + "\n")

    // draw nodes
    for (n <- nodeList; if n.typeName != "dummy") {
      val shapeString = " " + "shape" + "=" + n.shape + " "
      val nameString = " " + "label" + "=" + "\"" + n.dotGraphName + "\"" + " "
      val colorString = " " + "color" + "=" + n.color + " "
      val fillcolorString = " " + "fillcolor" + "=" + n.fillColor + " "
      writerGraph.write(n.nodeID.toString + " " + "[" + shapeString + nameString + colorString + fillcolorString + "]" + "\n")
    }

    // draw binary edges
    for ((et, edges) <- edgeMap; if edges.head.edge.length == 2 && et != "binaryEdge" && et != "ASTEdge"; edge <- edges; if edge.edge.sum != 0) {
      val styleString = " " + "shape" + "=" + edge.style + " "
      val nameString = " " + "label" + "=" + "\"" + edge.dotGraphName + "\"" + " "
      val colorString = " " + "color" + "=" + edge.color + " "
      writerGraph.write(edge.edge.head.toString + " -> " + edge.edge.tail.head.toString +
        " " + "[" + nameString + styleString + colorString + "]" + "\n")
    }

    //draw hyperedges
    var hyperEdgeNodeCounter = 0
    for ((et, edges) <- edgeMap; if edges.head.edge.length == 3 && et != "ternaryHyperEdge"; edge <- edges; if edge.edge.sum != 0) {
      //create a hyperedge node
      val clauseID = nodeMap(edge.edge.tail.head).clauseID.toString
      val hyperEdgeNodeID = et + "_" + hyperEdgeNodeCounter.toString
      val shapeString = " " + "shape" + "=" + "diamond" + " "
      val nameString = " " + "label" + "=" + "\"" + et + ":" + clauseID + "\"" + " "
      val colorString = " " + "color" + "=" + edge.color + " "
      val fillcolorString = " " + "fillcolor" + "=" + "while" + " "
      writerGraph.write(hyperEdgeNodeID + " " +
        "[" + shapeString + nameString + colorString + fillcolorString + "]" + "\n")
      hyperEdgeNodeCounter += 1

      val bodyNodeID = edge.edge.head.toString
      val guardNodeID = edge.edge.tail.head.toString
      val headNodeID = edge.edge.tail.tail.head.toString
      val edgeStyleString = " " + "shape" + "=" + edge.style + " "
      val edgeNameString = " " + "label" + "=" + "\"" + edge.dotGraphName + "\"" + " "
      val edgeColorString = " " + "color" + "=" + edge.color + " "
      //edge from body to hyperedge
      writerGraph.write(bodyNodeID + " -> " + hyperEdgeNodeID +
        " " + "[" + edgeNameString + edgeStyleString + edgeColorString + "]" + "\n")
      //edge from hyperEdgeNodeID to head
      writerGraph.write(hyperEdgeNodeID + " -> " + headNodeID +
        " " + "[" + edgeNameString + edgeStyleString + edgeColorString + "]" + "\n")
      //edge from head to hyperEdgeNodeID
      writerGraph.write(guardNodeID + " -> " + hyperEdgeNodeID +
        " " + "[" + edgeNameString + edgeStyleString + edgeColorString + "]" + "\n")

    }

    writerGraph.write("} " + "\n")
    writerGraph.close()

  }

  def outputJson(nodeList: Array[Node], edgeMap: Map[String, Array[Edge]]): Unit = {
    val nodeIndicesList = for (nt <- NodeAndEdgeType.nodeTypes) yield {
      nt + "Indices" -> nodeList.filter(_.typeName == nt)
    }
    val nodeSymbolList = nodeList.sortBy(_.nodeID)


    val jsonFileName = GlobalParameters.get.fileName + "." + graphNameMap(GlobalParameters.get.hornGraphType) + ".JSON"
    val writer = new PrintWriter(new File(jsonFileName))
    writer.write("{\n")

    //write statistic info
    writeOneLineJson("node number", Seq(nodeSymbolList.length).toString, changeLine = false)
    //write nodeID
    writeOneLineJson("nodeIDList", nodeSymbolList.map(_.nodeID).toSeq.toString)
    //write nodeSymbolList
    writeOneLineJson("nodeSymbolList", nodeSymbolList.map("\"" + _.canonicalName + "\"").toSeq.toString)
    //write indices
    for ((nt, nl) <- nodeIndicesList) {
      val listString = nl.map(_.nodeID).toSeq.toString()
      writeOneLineJson(nt + " number", Seq(nl.length).toString, changeLine = false)
      writeOneLineJson(nt, listString)
    }
    //write edges
    for ((edgeType, edges) <- edgeMap) {
      val filterDummyEdges = if (edges.length == 1) edges else edges.filterNot(x => x.edge.sum == 0)
      val listString = filterDummyEdges.map(x => seqToString(x.edge.toSeq.toString())).toSeq.toString()
      writeOneLineJson(edgeType + " number", Seq(edges.length).toString, changeLine = false)
      writeOneLineJson(edgeType, listString)
    }

    writer.write("}")
    writer.close()

    def writeOneLineJson(head: String, body: String, changeLine: Boolean = true): Unit = {
      if (changeLine == true)
        writer.write("\"" + head + "\"" + ":\n" + seqToString(body) + "," + "\n")
      else
        writer.write("\"" + head + "\"" + ":" + seqToString(body) + "," + "\n")
    }

    def seqToString(s: String): String = {
      if (s.contains("("))
        "[" + s.substring(s.indexOf("(") + 1, s.indexOf(")")) + "]"
      else
        s
    }
  }


  def parseConstraint(clause: Clause, rsHeadNode: (Node, Array[Node])): (Set[IFormula], Map[Node, (ITerm, IFormula)]) = {

    val bodyArguments = (for (body <- clause.body; arg <- body.args) yield arg)
    val separatedFormulas = LineariseVisitor(clause.constraint, IBinJunctor.And)
    var dataFlowFormula = Map[Node, (ITerm, IFormula)]()
    for ((arg, i) <- clause.head.args.zipWithIndex; f <- separatedFormulas) {
      val SE = IExpression.SymbolEquation(arg)
      f match {
        case SE(coefficient, rhs) if !coefficient.isZero => {
          val rhsSymbol = SymbolCollector.constants(rhs) ++ SymbolCollector.variables(rhs)
          if (!rhsSymbol.map(_.toString).intersect(bodyArguments.map(_.toString).toSet).isEmpty) { // if rhs symbol appear in body argument
            dataFlowFormula += findNodeInNodeList(nodeType = "relationSymbolArgument", readName = arg.toString,
              nodeList = rsHeadNode._2, rsName = clause.head.pred.name, argumentIndex = i).get -> (arg, f)
          }
        }
        case _ =>
      }
    }
    val guardFormula = separatedFormulas.toSet.diff(dataFlowFormula.values.map(_._2).toSet)

    (guardFormula, dataFlowFormula)
  }

  def constructAST(e: IExpression): Node = {
    e match {
      case Eq(t1, t2) => constructBinaryRelation("=", t1, t2)
      case EqLit(t1, t2) => constructBinaryRelation("=", t1, t2)
      case EqZ(t) => constructBinaryRelation("=", t, IConstant(new ConstantTerm(0.toString))) //constructUnaryRelation(">=", t)
      case Geq(t1, t2) => constructBinaryRelation(">=", t1, t2)
      case GeqZ(t) => constructBinaryRelation(">=", t, IConstant(new ConstantTerm(0.toString)))
      case Conj(t1, t2) => constructBinaryRelation("&", t1, t2)
      case Disj(t1, t2) => constructBinaryRelation("|", t1, t2)
      case IPlus(t1, t2) => constructBinaryRelation("+", t1, t2)
      case Difference(t1, t2) => constructBinaryRelation("-", t1, t2)
      case ITimes(coeff, subt) => {
        if (coeff.intValue == -1)
          constructUnaryRelation("-", subt)
        else if (coeff.intValue == 1)
          constructAST(subt)
        else
          constructBinaryRelation("*", IConstant(new ConstantTerm(coeff.intValue.toString)), subt)
      }
      case IQuantified(quan, subf) => constructUnaryRelation(quan.toString, subf)
      case INot(subf) => constructUnaryRelation("!", subf)
      case IBoolLit(c) => constructEndNode(nodeType = "constant", readName = c.toString)
      case IIntLit(c) => constructEndNode(nodeType = "constant", readName = c.toString)
      case IConstant(c) => constructEndNode(nodeType = "constant", readName = c.toString)
      case IVariable(c) => constructEndNode(nodeType = "constant", readName = c.toString)
      case _ => createNode("unknown", "unkown")
    }
  }

  def constructBinaryRelation(op: String, left: IExpression, right: IExpression): Node = {
    val opNode = constructUnaryRelation(op, left)
    val rightNode = constructAST(right)
    createEdge("ASTRightEdge", Array(rightNode.nodeID, opNode.nodeID))
    opNode
  }

  def constructUnaryRelation(op: String, e: IExpression): Node = {
    //todo merge op nodes (sub trees)
    val opNode = createNode("operator", op)
    val subExpressionNode = constructAST(e)
    createEdge("ASTLeftEdge", Array(subExpressionNode.nodeID, opNode.nodeID))
    opNode
  }

  def constructEndNode(nodeType: String, readName: String): Node = {
    //check if it is an argument node
    val rsaNodes = nodeMap.values.filter(x => x.typeName == "relationSymbolArgument")
    findNodeInNodeList(nodeType, readName, rsaNodes.toArray) match {
      case Some(n) => n
      case None => {
        //check if it is created
        val existedConstantNodes = nodeMap.values.filter(x => (x.typeName == "constant" || x.typeName == "variable"))
        findNodeInNodeList(nodeType, readName, existedConstantNodes.toArray) match {
          case Some(n) => n
          case None => createNode(nodeType, readName)
        }
      }
    }
  }

  def findNodeInNodeList(nodeType: String, readName: String, nodeList: Array[Node], argumentIndex: Int = -1,
                         rsName: String = ""): Option[Node] = {
    nodeType match {
      case "relationSymbolArgument" => nodeList.find(x => (x.rsName == rsName && x.argumentIndex == argumentIndex))
      case "relationSymbol" => nodeList.find(x => x.rsName == rsName && x.readName == rsName && x.argumentIndex == -1)
      case "constant" => nodeList.find(x => x.readName == readName)
      case "variable" => nodeList.find(x => x.readName == readName)
      case _ => None
    }
  }


}


class CDHG(clauses: Clauses, templates: templateCollection) extends HornGraph(clauses: Clauses, templates: templateCollection) {


  val normalizedClauses = normalizeClauses(clauses, templates.unlabeled)


  var clauseCount = 0

  for (clause <- normalizedClauses) {
    println(Console.BLUE + clause.toPrologString)


    //create head relation symbol node
    val rsHeadNode = createRelationSymbolNodesAndArguments(clause.head)


    //create body nodes
    val rsBodyNodeList = for (b <- clause.body) yield createRelationSymbolNodesAndArguments(b)


    val (guardFormula, dataFlowFormula) = parseConstraint(clause, rsHeadNode)
    println("guardFormula", guardFormula.map(_.toString))
    println("dataFlowFormula", dataFlowFormula.map(_._2._2.toString))

    //construct guard
    val guardNode = createNode("guard", "G", clauseID = clauseCount)
    val guardASTRootList =
      if (guardFormula.isEmpty)
        Seq(globalTrueNode)
      else
        for (g <- guardFormula.toSeq) yield {
          constructAST(g)
        }
    for (guardASTRoot <- guardASTRootList)
      createEdge("guardEdge", Array(guardASTRoot.nodeID, guardNode.nodeID))



    //construct dataflow rhs ast root - guard - head argument
    for ((headArg, df) <- dataFlowFormula) {
      val SE = IExpression.SymbolEquation(df._1)
      df._2 match {
        case SE(coefficient, rhs) if (!coefficient.isZero) => {
          val rhsASTRoot = constructAST(coefficient * rhs)
          createEdge("dataFlowHyperEdge", Array(rhsASTRoot.nodeID, guardNode.nodeID, headArg.nodeID))
        }
        case _ => {
          println("debug df", df)
        }
      }
    }

    //draw control flow : body-guard-head
    if (rsBodyNodeList.isEmpty)
      createEdge("controlFlowHyperEdge", Array(initialNode.nodeID, guardNode.nodeID, rsHeadNode._1.nodeID))
    else
      for ((rsb, rsbArgs) <- rsBodyNodeList) {
        createEdge("controlFlowHyperEdge", Array(rsb.nodeID, guardNode.nodeID, rsHeadNode._1.nodeID))
      }

    //todo draw templates

    clauseCount += 1
  }

  drawDotGraph(nodeList = nodeMap.values.toArray, edgeMap = edgeMap)
  outputJson(nodeList = nodeMap.values.toArray, edgeMap = edgeMap)


  def createRelationSymbolNodesAndArguments(atom: IAtom): (Node, Array[Node]) = {
    val atomName = atom.pred.name
    val nodeFromExistedList = findNodeInNodeList(nodeType = "relationSymbol", readName = atomName,
      nodeList = nodeMap.values.toArray, rsName = atomName)
    nodeFromExistedList match {
      case Some(headNode) => {
        val existedArgList = (for ((arg, i) <- atom.args.zipWithIndex) yield {
          val argNode = findNodeInNodeList("relationSymbolArgument", readName = arg.toString,
            nodeList = nodeMap.values.toArray, rsName = headNode.readName, argumentIndex = i).get
          //change readName for argument in every clause
          argNode.readName = arg.toString
          argNode
        })
        (headNode, existedArgList.toArray)
      }
      case None => {
        val rsNode: Node = createNode("relationSymbol", atomName, rsName = atomName)
        val argumentNodeList = for ((a, i) <- atom.args.zipWithIndex) yield {
          //create clause head argument nodes
          val argumentNode = createNode("relationSymbolArgument", a.toString, argumentIndex = i,
            rsName = atomName)
          // add edges with head node
          createEdge("relationSymbolArgumentEdge", Array(argumentNode.nodeID, rsNode.nodeID))
          argumentNode
        }
        (rsNode, argumentNodeList.toArray)
      }
    }

  }

}

class CG(clauses: Clauses, templates: templateCollection) extends HornGraph(clauses: Clauses, templates: templateCollection) {
  val simplifiedClauses = simplifyClauses(clauses, templates.unlabeled)
}