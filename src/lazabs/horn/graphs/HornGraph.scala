package lazabs.horn.graphs

import ap.parser.IExpression.{Conj, Difference, Disj, Eq, EqLit, EqZ, Geq, GeqZ, IdealInt2ITerm, Predicate, ex}
import lazabs.horn.graphs.GraphUtils._
import ap.parser.{IAtom, IBinJunctor, IBoolLit, IConstant, IExpression, IFormula, IIntLit, INot, IPlus, IQuantified, ITerm, ITimes, IVariable, LineariseVisitor, SymbolCollector}
import ap.terfor.ConstantTerm
import ap.types.Sort.{:::, AnyBool}
import ap.util.Seqs
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, VerifHintTplEqTerm, VerifHintTplInEqTerm, VerifHintTplPredPosNeg}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.graphs.TemplateUtils._
import lazabs.horn.preprocessor.HornPreprocessor.Clauses
import lazabs.horn.graphs.NodeAndEdgeType.{_}

import java.io.{File, PrintWriter}
import scala.collection.mutable

object HornGraphType extends Enumeration {
  val CDHG, CG = Value
}

object ASTSouce extends Enumeration {
  val clause, template = Value
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
    , "templateEdge" -> "t", "templateASTEdge" -> "tAST")

  val nodeShapeMap: Map[String, String] = getNodeAttributeMap(Map("relationSymbol" -> "component",
    "initial" -> "tab", "dummy" -> "box", "guard" -> "octagon", "clause" -> "octagon", "operator" -> "box",
    "relationSymbolArgument" -> "hexagon", "clauseArgument" -> "hexagon", "clauseHead" -> "box", "clauseBody" -> "box",
    "templateEq" -> "box", "templateIneq" -> "box", "templateBool" -> "box", "variable" -> "doublecircle"),
    elementTypes = nodeTypes, "circle")
  val nodeColorMap: Map[String, String] = getNodeAttributeMap(Map("relationSymbol" -> "black",
    "relationSymbolArgument" -> "black", "constant" -> "black"), elementTypes = nodeTypes, "black")
  val nodeFillColorMap: Map[String, String] = getNodeAttributeMap(Map("relationSymbol" -> "white",
    "relationSymbolArgument" -> "white", "constant" -> "white", "variable" -> "white",
    "templateEq" -> rgb(100, 100, 100), "templateIneq" -> rgb(150, 150, 150), "templateBool" -> rgb(200, 200, 200)), elementTypes = nodeTypes, "white")
  val edgeColorMap: Map[String, String] = getNodeAttributeMap(Map("dataEdge" -> "black", "templateASTEdge" -> "black"),
    elementTypes = edgeTypes, "black")
  val edgeStyleMap: Map[String, String] = getNodeAttributeMap(Map("dataEdge" -> "solid"),
    elementTypes = edgeTypes, "solid")
  val graphNameMap = Map(HornGraphType.CDHG -> "hyperEdgeGraph", HornGraphType.CG -> "monoDirectionLayerGraph")

}


case class Node(nodeID: Int, canonicalName: String, dotGraphName: String, typeName: String, var readName: String, shape: String,
                labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array(),
                color: String = "black", fillColor: String = "while", argumentIndex: Int = -1,
                rsName: String = "", clauseID: Int = -1)

case class Edge(edge: Array[Int], dotGraphName: String, typeName: String, style: String = "solid", color: String = "black")

class HornGraph(clauses: Clauses, templates: Map[String, VerificationHints]) {

  var globalNodeID = 0
  val canonicalNodeTypeIDMap = new mutable.HashMap[String, Int]
  (for (n <- nodeTypes) canonicalNodeTypeIDMap(n) = 0)


  val nodeMap = new mutable.HashMap[Int, Node]
  val currentClauseNodeMap = new mutable.HashMap[Int, Node]
  val dummyNode = createNode("dummy", "dummy")()
  var edgeMap = new mutable.HashMap[String, Array[Edge]]
  //add dummy edge to edgeMap
  for (t <- edgeTypes) {
    if (ternaryEdgeTypes.contains(t))
      edgeMap(t) = Array(Edge(Array(0, 0, 0), "dummy:" + t, t))
    else
      edgeMap(t) = Array(Edge(Array(0, 0), "dummy:" + t, t))
  }

  //create global constants
  val globalConstantNodeMap = new mutable.HashMap[String,Node]()
  val initialGlobalConstantNameList = Array("0")
  for (readName <- initialGlobalConstantNameList) globalConstantNodeMap(readName)=createNode("constant", readName)()

  val clauseConstraintSubExpressionMap = new mutable.HashMap[IExpression, Node]

  //global parameter for construct templates
  var astSource = ASTSouce.clause
  var currentRsNode: Node = dummyNode

  def createNode(nodeType: String, readName: String, argumentIndex: Int = -1, rsName: String = "", clauseID: Int = -1,
                 labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array())
                (shape: String = nodeShapeMap(nodeType), color: String = nodeColorMap(nodeType), fillColor: String = nodeFillColorMap(nodeType)): Node = {
    val nodeTypeCanonicalID = canonicalNodeTypeIDMap(nodeType)
    val canonicalIDName = getCanonicalName(nodeType, nodeTypeCanonicalID)
    val dotGraphName = globalNodeID.toString + ":" + getAbbrevCanonicalName(nodeType, nodeTypeCanonicalID) + ":" + readName
    val newNode = Node(globalNodeID, canonicalIDName, dotGraphName, nodeType, readName, shape = shape,
      argumentIndex = argumentIndex, rsName = rsName, clauseID = clauseID, color = color, fillColor = fillColor)
    globalNodeID += 1
    //canonicalNodeTypeIDMap = canonicalNodeTypeIDMap.updated(nodeType, canonicalNodeTypeIDMap(nodeType) + 1)
    canonicalNodeTypeIDMap(nodeType)=canonicalNodeTypeIDMap(nodeType) + 1

    nodeMap += (newNode.nodeID -> newNode)
    currentClauseNodeMap += (newNode.nodeID -> newNode)
    if (nodeType == "constant")
      globalConstantNodeMap(newNode.readName)=newNode
    newNode
  }

  def createEdge(edgeType: String, edge: Array[Int])
                (color: String = edgeColorMap(edgeType), style: String = edgeStyleMap(edgeType)): Unit = {
    val newEdge = Edge(edge = edge, dotGraphName = edgeTypesAbbrev(edgeType), typeName = edgeType, color = color, style = style)
    edgeMap += (edgeType->edgeMap(edgeType).+:(newEdge))
    if (edge.length == 2) { //add global binary
      if (edgeType == "ASTLeftEdge" || edgeType == "ASTRightEdge") {
        val etype = "ASTEdge"
        edgeMap(etype)= edgeMap(etype).+:(Edge(edge, edgeTypesAbbrev(etype), etype))
      }
      val etype = "binaryEdge"
      edgeMap(etype) =edgeMap(etype).+:(Edge(edge, edgeTypesAbbrev(etype), etype))
    } else { //add global ternary edges
      val etype = "ternaryHyperEdge"
      edgeMap(etype)= edgeMap(etype).+:(Edge(edge, edgeTypesAbbrev(etype), etype))
    }
  }


  def drawDotGraph(nodeList: Array[Node], edgeMap: mutable.HashMap[String, Array[Edge]]): Unit = {
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

  def outputJson(nodeList: Array[Node], edgeMap: mutable.HashMap[String, Array[Edge]],labelList:Array[Int]): Unit = {
    val nodeIndicesList = for (nt <- nodeTypes) yield {
      nt + "Indices" -> nodeList.filter(_.typeName == nt)
    }
    val nodeSymbolList = nodeList.sortBy(_.nodeID)

    val jsonFileName = GlobalParameters.get.fileName + "." + graphNameMap(GlobalParameters.get.hornGraphType) + ".JSON"
    val writer = new PrintWriter(new File(jsonFileName))
    writer.write("{\n")


    //write labels
    writeOneLineJson("labelNumber", Seq(labelList.length).toString, changeLine = false)
    writeOneLineJson("labelList", labelList.toSeq.toString)
    //write nodeID
    writeOneLineJson("nodeNumber", Seq(nodeSymbolList.length).toString, changeLine = false)
    writeOneLineJson("nodeIDList", nodeSymbolList.map(_.nodeID).toSeq.toString)
    //write nodeSymbolList
    writeOneLineJson("nodeSymbolList", nodeSymbolList.map("\"" + _.canonicalName + "\"").toSeq.toString)
    //write indices
    for ((nt, nl) <- nodeIndicesList) {
      val listString = nl.map(_.nodeID).toSeq.toString()
      writeOneLineJson(nt + "Number", Seq(nl.length).toString, changeLine = false)
      writeOneLineJson(nt, listString)
    }
    //write edges
    for ((edgeType, edges) <- edgeMap) {
      val filterDummyEdges = if (edges.length == 1) edges else edges.filterNot(x => x.edge.sum == 0)
      val listString = filterDummyEdges.map(x => seqToString(x.edge.toSeq.toString())).toSeq.toString()
      writeOneLineJson(edgeType + "Number", Seq(edges.length).toString, changeLine = false)
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

  def createRelationSymbolNodesAndArguments(atom: IAtom): (String,(Node,Array[Node])) = {
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
        (headNode.readName->(headNode->existedArgList.toArray))
      }
      case None => createNewRelationSymbolNodesAndArguments(atom, "relationSymbol",
        argumenNodeType = "relationSymbolArgument", argumentEdgeType = "relationSymbolArgumentEdge")

    }
  }

  def createNewRelationSymbolNodesAndArguments(atom: IAtom, atomType: String, argumenNodeType: String,
                                               argumentEdgeType: String, inverseEdgeDirection: Boolean = false):
  (String,(Node, Array[Node])) = {
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
    (rsNode.readName,(rsNode, argumentNodeList.toArray))
  }

  def parseConstraint(clause: Clause, rsHeadNode: (Node, Array[Node])): (Set[IFormula], mutable.HashMap[Node, (ITerm, IFormula)]) = {

    val bodyArguments = (for (body <- clause.body; z<-SymbolCollector.constants(body)) yield z).toSet
    val separatedFormulas = LineariseVisitor(clause.constraint, IBinJunctor.And)
    val dataFlowFormula = mutable.HashMap[Node, (ITerm, IFormula)]()
    for ((arg, i) <- clause.head.args.zipWithIndex; f <- separatedFormulas) {
      val SE = IExpression.SymbolEquation(arg)
      f match {
        case SE(coefficient, rhs) if !coefficient.isZero => {
          val rhsSymbol = SymbolCollector.constants(rhs)
          if (!Seqs.disjoint(rhsSymbol, bodyArguments)) {
            // if rhs symbol appear in body argument
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
    try{clauseConstraintSubExpressionMap(e)} //find e in clauseConstraintSubExpressionMap
    catch {
      case _=>{
        val astRootNode = e match {
          case Eq(t1, t2) => constructBinaryRelation("=", t1, t2)
          case Geq(t1, t2) => constructBinaryRelation(">=", t1, t2)
          case Conj(t1, t2) => constructBinaryRelation("&", t1, t2)
          case Disj(t1, t2) => constructBinaryRelation("|", t1, t2)
          case Difference(t1, t2) => constructBinaryRelation("-", t1, t2)
          case IPlus(t1, t2) => constructBinaryRelation("+", t1, t2)

          case ITimes(coeff, subt) => {
            if (coeff.isMinusOne)
              constructUnaryRelation("-", subt)
            else if (coeff.isOne)
              constructAST(subt)
            else
              constructBinaryRelation("*", coeff, subt)
          }
          case IQuantified(quan, subf) => constructUnaryRelation(quan.toString, subf)
          //todo connect quantifier and its corresponding variables
          case INot(subf) => constructUnaryRelation("!", subf)
          case IBoolLit(c) => constructEndNode(nodeType = "constant", readName = c.toString)
          case IIntLit(c) => constructEndNode(nodeType = "constant", readName = c.toString)
          case IConstant(c) => {
            constructEndNode(nodeType = "variable", readName = c.toString)
          }
          case IVariable(v) => { //todo match object
            println(Console.RED + v)
            val vName = if (astSource == ASTSouce.clause) "v" + v.toString else v.toString
            constructEndNode(nodeType = "variable", readName = vName, argumentIndex = v)
          }
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

  def constructEndNode(nodeType: String, readName: String, rsName: String = "", argumentIndex: Int = -1): Node = {
    GlobalParameters.get.hornGraphType match {
      case HornGraphType.CDHG => {
        val mergeNodeTypeList= Seq("relationSymbolArgument","constant","variable")
        mergeExistedEndNodeInClauseAndGlobalConstant(nodeType, readName,mergeNodeTypeList,rsName=rsName,argumentIndex=argumentIndex)
      }
      case HornGraphType.CG => {
        val mergeNodeTypeList= if (astSource == ASTSouce.clause) Seq("constant","variable") else Seq("relationSymbolArgument","constant","variable")
        val endNode = mergeExistedEndNodeInClauseAndGlobalConstant(nodeType, readName,mergeNodeTypeList,argumentIndex=argumentIndex,rsName=rsName)
        //add data edge
        val caNodes = currentClauseNodeMap.values.filter(x => x.typeName == "clauseArgument") // find ca in clause
        findNodeInNodeList(nodeType, readName, caNodes.toArray) match {
          case Some(correspondCANode) =>
            createEdge("dataEdge", Array(endNode.nodeID, correspondCANode.nodeID))()
          case None =>
        }
        endNode
      }
    }

  }

  def mergeExistedEndNodeInClauseAndGlobalConstant(nodeType: String, readName: String, mergeTypeList:Seq[String]=Seq(),
                                                   argumentIndex:Int = -1, rsName:String=""): Node = {
    //check if it is created
    val existedNodes = (currentClauseNodeMap.values.filter(x => mergeTypeList.contains(x.typeName) )).toArray
    findNodeInNodeList(nodeType, readName, existedNodes,argumentIndex=argumentIndex,rsName=rsName) match {
      case Some(n) => n
      case None => createNode(nodeType, readName)()
    }
  }

  def findNodeInNodeList(nodeType: String, readName: String, nodeList: Array[Node], argumentIndex: Int = -1,
                         rsName: String = ""): Option[Node] = {
    //todo match by object
    nodeType match {
      case "relationSymbolArgument" => nodeList.find(x => (x.rsName == rsName && x.argumentIndex == argumentIndex))
      case "clauseArgument" => nodeList.find(x => (x.rsName == rsName && x.argumentIndex == argumentIndex))
      case "relationSymbol" => nodeList.find(x => x.rsName == rsName && x.readName == rsName && x.argumentIndex == -1)
      case "constant" => nodeList.find(x => x.readName == readName) //match rs node and rsa name
      case "variable" => {
        if (astSource == ASTSouce.template)
          nodeList.find(x => x.rsName == currentRsNode.rsName && x.argumentIndex == argumentIndex)
        else
          nodeList.find(x => x.readName == readName)
      } //match rs node and index
      case _ => None
    }
  }

  def constructTemplates(templateMap: Map[String, VerificationHints]): Array[Int] = {
    astSource = ASTSouce.template

    val unlabeledTemplate = templateMap("unlabeled")
    val labeledTemplates = templateMap("labeled")

    val templateRelevanceLabelList = for ((pred, temps) <- unlabeledTemplate.predicateHints; t <- temps) yield{
      println(t)
      currentRsNode = nodeMap.values.find(x => x.typeName == "relationSymbol" && x.rsName == pred.name).get
      val currentRsaNodeList= nodeMap.values.filter(x => x.typeName == "relationSymbolArgument" && x.rsName == pred.name)
      for (a<-(currentRsaNodeList ++ globalConstantNodeMap.values)) currentClauseNodeMap(a.nodeID)=a
      val templateRelevanceLabel = t match {
        case VerifHintTplEqTerm(term, cost) => {
          term match { //predicate-2 (VerifHintTplPredPosNeg) will match TplEqTerm, differentiate boolean by Sort
            case (e: ITerm) ::: AnyBool(_) => createTemplateNodeAndCorrespondingEdges("templateBool", pred, e,t,labeledTemplates)
            case (e: ITerm) => createTemplateNodeAndCorrespondingEdges("templateEq", pred, e,t,labeledTemplates)
          }
        }
        case VerifHintTplInEqTerm(e, cost) => createTemplateNodeAndCorrespondingEdges("templateIneq", pred, e,t,labeledTemplates)
        case VerifHintTplPredPosNeg(e, cost) => createTemplateNodeAndCorrespondingEdges("templateBool", pred, e,t,labeledTemplates)
      }
      clauseConstraintSubExpressionMap.clear()
      currentClauseNodeMap.clear()
      templateRelevanceLabel
    }
    templateRelevanceLabelList.map(x=> if (x==true) 1 else 0).toArray

  }

  def createTemplateNodeAndCorrespondingEdges(templateType: String, pred: Predicate, e: IExpression,t:VerifHintElement,
                                              labeledTemplates:VerificationHints): Boolean = {
    val templateNode = createNode(templateType, templateType)()
    //edge from rs to templates
    createEdge("templateEdge", Array(currentRsNode.nodeID, templateNode.nodeID))()
    //ast root node
    val astRootNode = constructAST(e)
    //edge from ast note to template node
    createEdge("templateASTEdge", Array(astRootNode.nodeID, templateNode.nodeID))()

    //return label
    val labeledTemplateInPred = if (labeledTemplates.predicateHints.keys.toSeq.contains(pred)) labeledTemplates.predicateHints(pred) else Seq()
    verifHintElementContains(labeledTemplateInPred,t)

  }


}


class CDHG(clauses: Clauses, templates: Map[String, VerificationHints]) extends HornGraph(clauses: Clauses, templates: Map[String, VerificationHints]) {
  //todo unify the names for all elements in clauses.

  //notice: templates are only correspond to the original clauses
  val normalizedClauses = normalizeClauses(clauses, VerificationHints(Map()))

  //create initial rs node
  val initialNode = createNode("initial", "initial")()
  //create true constant node
  globalConstantNodeMap("true")=createNode("constant", "true")()
  var clauseCount = 0

  for (clause <- normalizedClauses) {
    val currentRsAndGlobalConstantNodes = globalConstantNodeMap.values ++ nodeMap.values.filter(x=>Seq("relationSymbol","relationSymbolArgument").contains(x.typeName))
    for(n<-currentRsAndGlobalConstantNodes)  currentClauseNodeMap(n.nodeID)=n

    //create head relation symbol node
    val rsHeadNode = createRelationSymbolNodesAndArguments(clause.head)
    //create body nodes
    val rsBodyNodeList = for (b <- clause.body) yield createRelationSymbolNodesAndArguments(b)
    //parse guard and data formula
    val (guardFormula, dataFlowFormula) = parseConstraint(clause, rsHeadNode._2)

    //construct guard node
    val guardNode = createNode("guard", "G", clauseID = clauseCount)()
    //get AST root nodes
    val guardASTRootList =
      if (guardFormula.isEmpty)
        Seq(globalConstantNodeMap("true"))
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
          println("coefficient",coefficient,"rhs", rhs)
          val rhsASTRoot =
            if (coefficient.isZero)
              globalConstantNodeMap("0")
            else
              constructAST(rhs *** coefficient)
          createEdge("dataFlowHyperEdge", Array(rhsASTRoot.nodeID, guardNode.nodeID, headArg.nodeID))()
        }
        case _ => {
          println("debug df", df)
        }
      }
    }

    //construct control flow : body-guard-head
    if (rsBodyNodeList.isEmpty)
      createEdge("controlFlowHyperEdge", Array(initialNode.nodeID, guardNode.nodeID, rsHeadNode._2._1.nodeID))()
    else
      for (rsb <- rsBodyNodeList) {
        createEdge("controlFlowHyperEdge", Array(rsb._2._1.nodeID, guardNode.nodeID, rsHeadNode._2._1.nodeID))()
      }


    clauseConstraintSubExpressionMap.clear()
    currentClauseNodeMap.clear()
    clauseCount += 1


    if (GlobalParameters.get.log) {
      println(Console.BLUE + clause.toPrologString)
      println("guardFormula", guardFormula.map(_.toString))
      println("dataFlowFormula", dataFlowFormula.map(_._2._2.toString))
      //      for ((k, v) <- clauseConstraintSubExpressionMap)
      //        println(k, v.readName)
    }

  }


  //val labelList = logTime(constructTemplates(templates), "construct templates")

  logTime(drawDotGraph(nodeList = nodeMap.values.toArray, edgeMap = edgeMap), "write dot graph")
  //logTime(outputJson(nodeList = nodeMap.values.toArray, edgeMap = edgeMap,labelList), "write graph to JSON")

}

class CG(clauses: Clauses, templates: Map[String, VerificationHints]) extends HornGraph(clauses: Clauses, templates: Map[String, VerificationHints]) {
  //notice: templates are only correspond to the original clauses
  val simplifiedClauses = simplifyClauses(clauses, VerificationHints(Map()))
  var clauseCount = 0

  //predicate layer
  val atomSet = (for (clause <- simplifiedClauses; atom <- clause.allAtoms) yield atom).toSet
  val rsNodeMap = new mutable.HashMap[String,(Node,Array[Node])]()
    for (atom <- atomSet) rsNodeMap+= createRelationSymbolNodesAndArguments(atom)


  for (clause <- simplifiedClauses) {
    val currentRsAndGlobalConstantNodes = globalConstantNodeMap.values ++ nodeMap.values.filter(x => Seq("relationSymbol", "relationSymbolArgument").contains(x.typeName))
    for (n <- currentRsAndGlobalConstantNodes) currentClauseNodeMap(n.nodeID) = n

    //clause layer
    // create clause head and body and their argument nodes
    val clauseHeadNode = createNewRelationSymbolNodesAndArguments(clause.head, "clauseHead",
      argumenNodeType = "clauseArgument", argumentEdgeType = "clauseArgumentEdge")
    val clauseBodyNodeList = for (b <- clause.body) yield createNewRelationSymbolNodesAndArguments(b,
      "clauseBody", argumenNodeType = "clauseArgument", argumentEdgeType = "clauseArgumentEdge")

    //create clause node
    val clauseNode = createNode("clause", "clause_" + clauseCount.toString)()
    //connect clause head and body to clause node
    createEdge("clauseHeadEdge", Array(clauseHeadNode._2._1.nodeID, clauseNode.nodeID))()
    for (cbn <- clauseBodyNodeList)
      createEdge("clauseBodyEdge", Array(cbn._2._1.nodeID, clauseNode.nodeID))()

    //connect from clause layer to predicate layer
    for (c <- clauseBodyNodeList ++ Seq(clauseHeadNode)) {
      val correspondingRs = rsNodeMap(c._1)
      createEdge("relationSymbolInstanceEdge", Array(c._2._1.nodeID, correspondingRs._1.nodeID))()
      for (a <- c._2._2) {
        val correspondingArg = correspondingRs._2.find(x => x.argumentIndex == a.argumentIndex).get
        createEdge("argumentInstanceEdge", Array(a.nodeID, correspondingArg.nodeID))()
      }
    }

    //constraint layer and connections
    val subConstraintFormulas = LineariseVisitor(clause.constraint, IBinJunctor.And)
    val constraintRootNodes = for (subf <- subConstraintFormulas) yield constructAST(subf)
    for (r <- constraintRootNodes)
      createEdge("guardEdge", Array(r.nodeID, clauseNode.nodeID))()


    clauseConstraintSubExpressionMap.clear()
    currentClauseNodeMap.clear()
    clauseCount += 1

    if (GlobalParameters.get.log) {
      println(Console.BLUE + clause.toPrologString)
    }
  }

  val labelList = logTime(constructTemplates(templates),"construct templates")

  logTime(drawDotGraph(nodeList = nodeMap.values.toArray, edgeMap = edgeMap),"write dot graph")
  logTime(outputJson(nodeList = nodeMap.values.toArray, edgeMap = edgeMap,labelList),"write graph to JSON")

}