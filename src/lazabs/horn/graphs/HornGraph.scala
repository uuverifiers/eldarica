package lazabs.horn.graphs

import ap.parser.IExpression.{Conj, Difference, Disj, Eq, EqLit, EqZ, Geq, GeqZ,Predicate}
import lazabs.horn.graphs.GraphUtils._
import ap.parser.{IAtom, IBinJunctor, IBoolLit, IConstant, IExpression, IFormula, IIntLit, INot, IPlus, IQuantified, ITerm, ITimes, IVariable, LineariseVisitor, SymbolCollector}
import ap.terfor.ConstantTerm
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.abstractions.VerificationHints.{VerifHintTplEqTerm, VerifHintTplInEqTerm, VerifHintTplPredPosNeg}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.graphs.TemplateUtils._
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

import java.io.{File, PrintWriter}

object HornGraphType extends Enumeration {
  val CDHG, CG = Value
}

object NodeAndEdgeType {
  //node definition
  val nodeTypes = Seq("relationSymbol", "initial", "false", "relationSymbolArgument", "variable", "operator", "constant", "guard",
    "clause", "clauseHead", "clauseBody", "clauseArgument",
    "templateBool", "templateEq", "templateIneq", "dummy", "unknown", "empty")
  val nodeTypesAbbrev = Map("relationSymbol" -> "rs", "initial" -> "initial", "false" -> "false",
    "relationSymbolArgument" -> "rsa", "variable" -> "var", "operator" -> "op", "constant" -> "c", "guard" -> "g",
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
    "clauseBodyEdge" -> "CB", "clauseArgumentEdge" -> "CA", "dataEdge" -> "data", "binaryEdge" -> "be"
    ,"templateEdge"->"t","templateASTEdge"->"tAST")

}


case class Node(nodeID: Int, canonicalName: String, dotGraphName: String, typeName: String, var readName: String, shape: String,
                labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array(),
                color: String = "black", fillColor: String = "while", argumentIndex: Int = -1,
                rsName: String = "", clauseID: Int = -1)

case class Edge(edge: Array[Int], dotGraphName: String, typeName: String, style: String = "solid", color: String = "black")

class HornGraph(clauses: Clauses, templates: Map[String,VerificationHints]) {

  var globalNodeID = 0
  var canonicalNodeTypeIDMap: Map[String, Int] = (for (n <- NodeAndEdgeType.nodeTypes) yield n -> 0).toMap
  val nodeShapeMap: Map[String, String] = getNodeAttributeMap(Map("relationSymbol" -> "component",
    "initial" -> "tab", "dummy" -> "box", "guard" -> "octagon", "clause" -> "octagon", "operator" -> "box",
    "relationSymbolArgument" -> "hexagon", "clauseArgument" -> "hexagon", "clauseHead" -> "box", "clauseBody" -> "box",
  "templateEq"->"box","templateIneq"->"box","templateBool"->"box"),
    elementTypes = NodeAndEdgeType.nodeTypes, "circle")
  val nodeColorMap: Map[String, String] = getNodeAttributeMap(Map("relationSymbol" -> "black",
    "relationSymbolArgument" -> "black", "constant" -> "black"), elementTypes = NodeAndEdgeType.nodeTypes, "black")
  val nodeFillColorMap: Map[String, String] = getNodeAttributeMap(Map("relationSymbol" -> "white",
    "relationSymbolArgument" -> "white", "constant" -> "white",
    "templateEq"->"red","templateIneq"->"yellow","templateBool"->"green"), elementTypes = NodeAndEdgeType.nodeTypes, "white")
  val edgeColorMap: Map[String, String] = getNodeAttributeMap(Map("dataEdge" -> "black"),
    elementTypes = NodeAndEdgeType.edgeTypes, "black")
  val edgeStyleMap: Map[String, String] = getNodeAttributeMap(Map("dataEdge" -> "solid"),
    elementTypes = NodeAndEdgeType.edgeTypes, "solid")
  val graphNameMap = Map(HornGraphType.CDHG -> "hyperEdgeGraph", HornGraphType.CG -> "monoDirectionLayerGraph")


  var nodeMap: Map[Int, Node] = Map()
  var currentClauseNodeMap: Map[Int, Node] = Map()
  val dummyNode = createNode("dummy", "dummy")()
  var edgeMap: Map[String, Array[Edge]] = (for (t <- NodeAndEdgeType.edgeTypes) yield {
    if (NodeAndEdgeType.ternaryEdgeTypes.contains(t))
      t -> Array(Edge(Array(0, 0, 0), "dummy:" + t, t))
    else
      t -> Array(Edge(Array(0, 0), "dummy:" + t, t))
  }).toMap

  //create global constants
  var globalConstantNodeList: Array[Node] = Array()
  val globalConstantNameList = Array("0")
  globalConstantNodeList = for (readName <- globalConstantNameList) yield
    createNode("constant", readName)()

  var clauseConstraintSubExpressionMap: Map[IExpression, Node] = Map()


  def createNode(nodeType: String, readName: String, argumentIndex: Int = -1, rsName: String = "", clauseID: Int = -1,
                 labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array())
                (shape: String = nodeShapeMap(nodeType), color: String = nodeColorMap(nodeType), fillColor: String = nodeFillColorMap(nodeType)): Node = {
    val nodeTypeCanonicalID = canonicalNodeTypeIDMap(nodeType)
    val canonicalIDName = getCanonicalName(nodeType, nodeTypeCanonicalID)
    val dotGraphName = globalNodeID.toString + ":" + getAbbrevCanonicalName(nodeType, nodeTypeCanonicalID) + ":" + readName
    val newNode = Node(globalNodeID, canonicalIDName, dotGraphName, nodeType, readName, shape = shape,
      argumentIndex = argumentIndex, rsName = rsName, clauseID = clauseID, color = color, fillColor = fillColor)
    globalNodeID += 1
    canonicalNodeTypeIDMap = canonicalNodeTypeIDMap.updated(nodeType, canonicalNodeTypeIDMap(nodeType) + 1)
    nodeMap += (newNode.nodeID -> newNode)
    currentClauseNodeMap += (newNode.nodeID -> newNode)
    if (nodeType == "constant")
      globalConstantNodeList = globalConstantNodeList.+:(newNode)
    newNode
  }

  def createEdge(edgeType: String, edge: Array[Int])
                (color: String = edgeColorMap(edgeType), style: String = edgeStyleMap(edgeType)): Unit = {
    edgeMap = edgeMap.updated(edgeType, edgeMap(edgeType).+:(
      Edge(edge = edge, dotGraphName = NodeAndEdgeType.edgeTypesAbbrev(edgeType), typeName = edgeType, color = color, style = style)))
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
      val styleString = " " + "style" + "=" + "filled" + " "
      writerGraph.write(n.nodeID.toString + " " + "[" + shapeString + nameString + colorString + fillcolorString + styleString + "]" + "\n")
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
      val fillcolorString = " " + "fillcolor" + "=" + "white" + " "
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

  def createRelationSymbolNodesAndArguments(atom: IAtom): (Node, Array[Node]) = {
    //this merge rs and their arguments globally
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
      case None => createNewRelationSymbolNodesAndArguments(atom, "relationSymbol",
        argumenNodeType = "relationSymbolArgument", argumentEdgeType = "relationSymbolArgumentEdge")

    }
  }

  def createNewRelationSymbolNodesAndArguments(atom: IAtom, atomType: String, argumenNodeType: String,
                                               argumentEdgeType: String, inverseEdgeDirection: Boolean = false): (Node, Array[Node]) = {
    val atomName = atom.pred.name
    val rsNode: Node = createNode(atomType, atomName, rsName = atomName)()
    val argumentNodeList = for ((a, i) <- atom.args.zipWithIndex) yield {
      //create rs argument nodes
      val argumentNode = createNode(argumenNodeType, a.toString, argumentIndex = i, rsName = atomName)()
      // add edges with from argument to rs
      val edge = if (inverseEdgeDirection == true) Array(rsNode.nodeID, argumentNode.nodeID) else Array(argumentNode.nodeID, rsNode.nodeID)
      createEdge(argumentEdgeType, edge)()
      argumentNode
    }
    (rsNode, argumentNodeList.toArray)
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
    //merge sub tree
    clauseConstraintSubExpressionMap.find(x => x._1 == e) match {
      case Some(subE) => {
        //println("merge sub tree",subE._1,subE._2.readName)
        subE._2
      }
      case None => {
        val astRootNode = e match {
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
          case IIntLit(c) => {
            constructEndNode(nodeType = "constant", readName = c.toString)
          }
          case IConstant(c) => {
            constructEndNode(nodeType = "variable", readName = c.toString)
          }
          case IVariable(c) => constructEndNode(nodeType = "variable", readName = c.toString)
          case _ => createNode("unknown", "unkown")()
        }
        clauseConstraintSubExpressionMap += (e -> astRootNode)
        astRootNode
      }
    }

  }

  def constructBinaryRelation(op: String, left: IExpression, right: IExpression): Node = {
    val opNode = constructUnaryRelation(op, left)
    val rightNode = constructAST(right)
    createEdge("ASTRightEdge", Array(rightNode.nodeID, opNode.nodeID))()
    opNode
  }

  def constructUnaryRelation(op: String, e: IExpression): Node = {
    val opNode = createNode("operator", op)()
    val subExpressionNode = constructAST(e)
    createEdge("ASTLeftEdge", Array(subExpressionNode.nodeID, opNode.nodeID))()
    opNode
  }

  def constructEndNode(nodeType: String, readName: String): Node = {
    GlobalParameters.get.hornGraphType match {
      case HornGraphType.CDHG => {
        val rsaNodes = nodeMap.values.filter(x => x.typeName == "relationSymbolArgument") // merge global rsa
        findNodeInNodeList(nodeType, readName, rsaNodes.toArray) match { //merge argument node
          case Some(argNode) => argNode
          case None => {
            mergeExistedEndNodeInClauseAndGlobalConstant(nodeType, readName)
          }
        }
      }
      case HornGraphType.CG => {
        val caNodes = currentClauseNodeMap.values.filter(x => x.typeName == "clauseArgument") // find ca in clause
        val endNode = mergeExistedEndNodeInClauseAndGlobalConstant(nodeType, readName)
        findNodeInNodeList(nodeType, readName, caNodes.toArray) match {
          case Some(correspondCANode) =>
            createEdge("dataEdge", Array(endNode.nodeID, correspondCANode.nodeID))()
          case None =>
        }
        endNode
      }
    }

  }

  def mergeExistedEndNodeInClauseAndGlobalConstant(nodeType: String, readName: String): Node = {
    //check if it is created
    val existedConstantNodes = (currentClauseNodeMap.values ++ globalConstantNodeList).filter(x => (x.typeName == "constant" || x.typeName == "variable"))
    findNodeInNodeList(nodeType, readName, existedConstantNodes.toArray) match {
      case Some(n) => n
      case None => createNode(nodeType, readName)()
    }
  }

  def findNodeInNodeList(nodeType: String, readName: String, nodeList: Array[Node], argumentIndex: Int = -1,
                         rsName: String = ""): Option[Node] = {
    nodeType match {
      case "relationSymbolArgument" => nodeList.find(x => (x.rsName == rsName && x.argumentIndex == argumentIndex))
      case "clauseArgument" => nodeList.find(x => (x.rsName == rsName && x.argumentIndex == argumentIndex))
      case "relationSymbol" => nodeList.find(x => x.rsName == rsName && x.readName == rsName && x.argumentIndex == -1)
      case "constant" => nodeList.find(x => x.readName == readName)
      case "variable" => nodeList.find(x => x.readName == readName)
      case _ => None
    }
  }

  def constructTemplates(templateMap:Map[String,VerificationHints]): Unit ={
    //todo predicate-2 will match TplEqTerm, differerntiate boolean by Sort
    val unlabeledTemplate = templateMap("unlabeled")

    for ((pred,temps)<-unlabeledTemplate.predicateHints;t<-temps){
      //create template node
      t match {
        case VerifHintTplEqTerm(e,cost)=> createTemplateNodeAndCorrespondingEdges("templateEq",pred,e)
        case  VerifHintTplInEqTerm(e,cost)=> createTemplateNodeAndCorrespondingEdges("templateIneq",pred,e)
        case VerifHintTplPredPosNeg(e,cost)=> createTemplateNodeAndCorrespondingEdges("templateBool",pred,e)
      }

    }

    def createTemplateNodeAndCorrespondingEdges(templateType:String,pred:Predicate,e:IExpression): Unit ={
      val templateNode=createNode(templateType,templateType)()
      //edge from rs to templates
      val correspondingRs = nodeMap.values.find(x=>x.typeName=="relationSymbol" && x.readName == pred.name && x.rsName ==pred.name).get
      createEdge("templateEdge",Array(correspondingRs.nodeID,templateNode.nodeID))()
      //ast root node
      val astRootNode = constructAST(e) //todo check merging
      //edge from ast note to template node
      createEdge("templateASTEdge",Array(astRootNode.nodeID,templateNode.nodeID))()
    }

  }


}


class CDHG(clauses: Clauses, templates: Map[String,VerificationHints]) extends HornGraph(clauses: Clauses, templates: Map[String,VerificationHints]) {

  val normalizedClauses = normalizeClauses(clauses, templates("unlabeled"))

  //create initial rs node
  val initialNode = createNode("initial", "initial")()
  //create true constant node
  globalConstantNodeList = globalConstantNodeList.+:(createNode("constant", "true")())
  var clauseCount = 0

  for (clause <- normalizedClauses) {
    //create head relation symbol node
    val rsHeadNode = createRelationSymbolNodesAndArguments(clause.head)
    //create body nodes
    val rsBodyNodeList = for (b <- clause.body) yield createRelationSymbolNodesAndArguments(b)
    //parse guard and data formula
    val (guardFormula, dataFlowFormula) = parseConstraint(clause, rsHeadNode)

    //construct guard node
    val guardNode = createNode("guard", "G", clauseID = clauseCount)()
    //get AST root nodes
    val guardASTRootList =
      if (guardFormula.isEmpty)
        Seq(globalConstantNodeList.find(x => x.readName == "true").get)
      else
        for (g <- guardFormula.toSeq) yield {
          constructAST(g)
        }
    //connect AST root to guard node
    for (guardASTRoot <- guardASTRootList)
      createEdge("guardEdge", Array(guardASTRoot.nodeID, guardNode.nodeID))()


    //construct dataflow rhs AST root - guard - head argument
    for ((headArg, df) <- dataFlowFormula) {
      val SE = IExpression.SymbolEquation(df._1)
      df._2 match {
        case SE(coefficient, rhs) => {
          //println("coef",coefficient,"rhs",rhs)
          val rhsASTRoot =
            if (coefficient.intValue == 0)
              globalConstantNodeList.find(x => x.readName == "0").get
            else if (coefficient.intValue == 1)
              constructAST(rhs)
            else
              constructAST(coefficient * rhs)
          createEdge("dataFlowHyperEdge", Array(rhsASTRoot.nodeID, guardNode.nodeID, headArg.nodeID))()
        }
        case _ => {
          println("debug df", df)
        }
      }
    }

    //construct control flow : body-guard-head
    if (rsBodyNodeList.isEmpty)
      createEdge("controlFlowHyperEdge", Array(initialNode.nodeID, guardNode.nodeID, rsHeadNode._1.nodeID))()
    else
      for ((rsb, rsbArgs) <- rsBodyNodeList) {
        createEdge("controlFlowHyperEdge", Array(rsb.nodeID, guardNode.nodeID, rsHeadNode._1.nodeID))()
      }


    clauseConstraintSubExpressionMap = Map()
    currentClauseNodeMap = Map()
    clauseCount += 1


    if (GlobalParameters.get.log) {
      println(Console.BLUE + clause.toPrologString)
      println("guardFormula", guardFormula.map(_.toString))
      println("dataFlowFormula", dataFlowFormula.map(_._2._2.toString))
      //      for ((k, v) <- clauseConstraintSubExpressionMap)
      //        println(k, v.readName)
    }

  }

  //todo draw templates
  printListMap(templates("unlabeled").predicateHints, "unlabeled templates")
  constructTemplates(templates)

  drawDotGraph(nodeList = nodeMap.values.toArray, edgeMap = edgeMap)
  outputJson(nodeList = nodeMap.values.toArray, edgeMap = edgeMap)

}

class CG(clauses: Clauses, templates: Map[String,VerificationHints]) extends HornGraph(clauses: Clauses, templates: Map[String,VerificationHints]) {
  val simplifiedClauses = simplifyClauses(clauses, templates("unlabeled"))
  var clauseCount = 0

  //predicate layer
  val atomSet = (for (clause <- simplifiedClauses; atom <- clause.allAtoms) yield atom).toSet
  val rsNodeList = for (atom <- atomSet) yield createRelationSymbolNodesAndArguments(atom)

  currentClauseNodeMap = Map()
  for (clause <- simplifiedClauses) {

    //clause layer
    // create clause head and body and their argument nodes
    val clauseHeadNode = createNewRelationSymbolNodesAndArguments(clause.head, "clauseHead",
      argumenNodeType = "clauseArgument", argumentEdgeType = "clauseArgumentEdge")
    val clauseBodyNodeList = for (b <- clause.body) yield createNewRelationSymbolNodesAndArguments(b,
      "clauseBody", argumenNodeType = "clauseArgument", argumentEdgeType = "clauseArgumentEdge")

    //create clause node
    val clauseNode = createNode("clause", "clause_" + clauseCount.toString)()
    //connect clause head and body to clause node
    createEdge("clauseHeadEdge", Array(clauseHeadNode._1.nodeID, clauseNode.nodeID))()
    for (cbn <- clauseBodyNodeList)
      createEdge("clauseBodyEdge", Array(cbn._1.nodeID, clauseNode.nodeID))()

    //connect from clause layer to predicate layer
    for (c <- clauseBodyNodeList ++ Seq(clauseHeadNode)) {
      val correspondingRs = rsNodeList.find(x => x._1.rsName == c._1.rsName).get
      createEdge("relationSymbolInstanceEdge", Array(c._1.nodeID, correspondingRs._1.nodeID))()
      for (a <- c._2) {
        val correspondingArg = correspondingRs._2.find(x => x.argumentIndex == a.argumentIndex).get
        createEdge("argumentInstanceEdge", Array(a.nodeID, correspondingArg.nodeID))()
      }
    }

    //constraint layer and connections
    val subConstraintFormulas = LineariseVisitor(clause.constraint, IBinJunctor.And)
    val constraintRootNodes = for (subf <- subConstraintFormulas) yield constructAST(subf)
    for (r <- constraintRootNodes)
      createEdge("guardEdge", Array(r.nodeID, clauseNode.nodeID))()


    clauseConstraintSubExpressionMap = Map()
    currentClauseNodeMap = Map()
    clauseCount += 1

    if (GlobalParameters.get.log) {
      println(Console.BLUE + clause.toPrologString)
    }

  }

  drawDotGraph(nodeList = nodeMap.values.toArray, edgeMap = edgeMap)
  outputJson(nodeList = nodeMap.values.toArray, edgeMap = edgeMap)

}