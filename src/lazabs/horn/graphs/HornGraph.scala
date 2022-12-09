package lazabs.horn.graphs

import ap.basetypes.IdealInt
import ap.parser.IExpression.{Conj, Difference, Disj, Eq, EqLit, EqZ, Geq, GeqZ, IdealInt2ITerm, Predicate, ex}
import lazabs.horn.graphs.GraphUtils._
import ap.parser.{IAtom, IBinJunctor, IBoolLit, IConstant, IExpression, IFormula, IFunApp, IIntLit, INot, IPlus, IQuantified, ITerm, ITimes, IVariable, LineariseVisitor, SymbolCollector}
import ap.terfor.ConstantTerm
import ap.theories.ADT.BoolADT
import ap.util.Seqs
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, VerifHintTplEqTerm, VerifHintTplInEqTerm, VerifHintTplPredPosNeg}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.{HornClauses, HornTranslator}
import lazabs.horn.graphs.TemplateUtils._
import lazabs.horn.graphs.Utils._
import lazabs.horn.preprocessor.HornPreprocessor.Clauses
import lazabs.horn.graphs.NodeAndEdgeType._
import lazabs.horn.parser.HornReader.fromSMT

import java.io.{File, PrintWriter}
import scala.collection.mutable

object HornGraphType extends Enumeration {
  val CDHG, CG = Value
}

object HornGraphLabelType extends Enumeration {
  val template, unsatCore = Value
}

object ASTSouce extends Enumeration {
  val clause, template = Value
}

object NodeAndEdgeType {
  //node definition
  val nodeTypes = Seq("relationSymbol", "initial", "false", "relationSymbolArgument", "variable",
    "operator", "constant", "guard",
    "clause", "clauseHead", "clauseBody", "clauseArgument",
    "templateBool", "templateEq", "templateIneq", "dummy", "unknown", "empty")
  val nodeTypesAbbrev = Map("relationSymbol" -> "rs", "initial" -> "initial", "false" -> "false",
    "relationSymbolArgument" -> "rsa", "variable" -> "var", "operator" -> "op", "constant" -> "c", "guard" -> "g",
    "clause" -> "cla", "clauseHead" -> "ch", "clauseBody" -> "cb", "clauseArgument" -> "ca",
    "templateBool" -> "tb", "templateEq" -> "teq", "templateIneq" -> "tineq", "dummy" -> "dm", "unknown" -> "unk",
    "empty" -> "e")

  // edge definition
  val ternaryEdgeTypes = Seq("controlFlow", "dataFlow", "ternary").map(_ + "HyperEdge")
  val binaryEdgeTypes = Seq("guard", "relationSymbolArgument", "ASTLeft", "ASTRight",
    "AST", "relationSymbolInstance", "argumentInstance", "clauseHead", "clauseBody",
    "clauseArgument", "data", "quantifier", "binary").map(_ + "Edge")
  val templateEdgeTypes = Seq("template", "templateAST").map(_ + "Edge")
  val edgeTypes = ternaryEdgeTypes ++ binaryEdgeTypes ++ templateEdgeTypes
  val edgeTypesAbbrev = Map("controlFlowHyperEdge" -> "CFHE", "dataFlowHyperEdge" -> "DFHE", "ternaryHyperEdge" -> "te",
    "guardEdge" -> "G", "relationSymbolArgumentEdge" -> "RSA", "ASTLeftEdge" -> "ASTL", "ASTRightEdge" -> "ASTR"
    , "ASTEdge" -> "AST", "relationSymbolInstanceEdge" -> "RSI", "argumentInstanceEdge" -> "AI", "clauseHeadEdge" -> "CH",
    "clauseBodyEdge" -> "CB", "clauseArgumentEdge" -> "CA", "dataEdge" -> "data", "quantifierEdge" -> "quan", "binaryEdge" -> "be"
    , "templateEdge" -> "t", "templateASTEdge" -> "tAST")

  val nodeShapeMap: Map[String, String] = getNodeAttributeMap(Map("relationSymbol" -> "component","false"->"component",
    "initial" -> "tab", "dummy" -> "box", "guard" -> "octagon", "clause" -> "octagon", "operator" -> "box",
    "relationSymbolArgument" -> "hexagon", "clauseArgument" -> "hexagon", "clauseHead" -> "box", "clauseBody" -> "box",
    "templateEq" -> "box", "templateIneq" -> "box", "templateBool" -> "box", "variable" -> "doublecircle"),
    elementTypes = nodeTypes, "circle")
  val nodeColorMap: Map[String, String] = getNodeAttributeMap(Map("relationSymbol" -> "black",
    "relationSymbolArgument" -> "black", "constant" -> "black"), elementTypes = nodeTypes, "black")
  val nodeFillColorMap: Map[String, String] = getNodeAttributeMap(Map("relationSymbol" -> "white",
    "relationSymbolArgument" -> "white", "constant" -> "white", "variable" -> "white",
    "templateEq" -> rgb(100, 100, 100), "templateIneq" -> rgb(150, 150, 150), "templateBool" -> rgb(200, 200, 200)), elementTypes = nodeTypes, "white")
  val edgeColorMap: Map[String, String] = getNodeAttributeMap(Map("dataEdge" -> "black",
    "quantifierEdge" -> "red", "templateASTEdge" -> "black"),
    elementTypes = edgeTypes, "black")
  val edgeStyleMap: Map[String, String] = getNodeAttributeMap(Map("dataEdge" -> "solid"),
    elementTypes = edgeTypes, "solid")

}


case class Node(nodeID: Int, canonicalName: String, dotGraphName: String, typeName: String, element: NodeElement,
                var readName: String,
                shape: String, labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array(),
                color: String = "black", fillColor: String = "while", argumentIndex: Int = -1,
                rsName: String = "", clauseID: Int = -1)

case class Edge(edge: Array[Int], dotGraphName: String, typeName: String, style: String = "solid", color: String = "black")

sealed trait NodeElement

final case class PredicateNode(pred: Predicate) extends NodeElement

final case class FalseNode(pred: Predicate) extends NodeElement

final case class PredicateArgumentNode(pred: Predicate, i: Int, c: IConstant) extends NodeElement

final case class IConstantNode(c: IConstant) extends NodeElement

final case class IVariableNode(v: IVariable) extends NodeElement

final case class IBoolLitNode(b: IBoolLit) extends NodeElement

final case class IIntLitNode(i: IIntLit) extends NodeElement

final case class AbstractNode(a: String) extends NodeElement


class HornGraph(originalSimplifiedClauses: Clauses) {
  val clauses = getClausesAccordingToLabels(originalSimplifiedClauses)
  var labelIndices: Array[Int] = Array()
  var labelList: Array[Int] = Array()
  var labelMask: Array[Int] = Array()
  var globalNodeID = 0
  val canonicalNodeTypeIDMap = new mutable.HashMap[String, Int]
  (for (n <- nodeTypes) canonicalNodeTypeIDMap(n) = 0)


  val nodeMap = new mutable.HashMap[Int, Node]
  val currentClauseIVariableNodeMap = new mutable.HashMap[IVariable, Node]
  val currentClauseIConstantNodeMap = new mutable.HashMap[IConstant, Node]
  val currentClauseArgumentNodesMap = new mutable.HashMap[IConstant, Node]
  val quantifierStack = new mutable.Stack[Node]
  val globalPredicateNodeMap = new mutable.HashMap[Predicate, Node]
  val globalPredicateArgumentNodeMap = new mutable.HashMap[(Predicate, Int), Node]
  //val currentClauseNodeMap = new mutable.HashMap[Int, Node]
  val dummyNode = createNode("dummy", "dummy", element = AbstractNode("dummy"))()
  var currentPred: Predicate = new Predicate("", 0)
  var edgeMap = new mutable.HashMap[String, Array[Edge]]
  //add dummy edge to edgeMap
  for (t <- edgeTypes) {
    if (ternaryEdgeTypes.contains(t))
      edgeMap(t) = Array(Edge(Array(0, 0, 0), "dummy:" + t, t))
    else
      edgeMap(t) = Array(Edge(Array(0, 0), "dummy:" + t, t))
  }

  //create global constants
  val globalConstantNodeMap = new mutable.HashMap[String, Node]()

  val clauseConstraintSubExpressionMap = new mutable.HashMap[IExpression, Node]

  //global parameter for construct templates
  var astSource = ASTSouce.clause

  def createNode(nodeType: String, readName: String, element: NodeElement, argumentIndex: Int = -1, rsName: String = "", clauseID: Int = -1,
                 labelList: Array[Float] = Array(), predictedLabelList: Array[Float] = Array())
                (shape: String = nodeShapeMap(nodeType), color: String = nodeColorMap(nodeType), fillColor: String = nodeFillColorMap(nodeType)): Node = {
    val nodeTypeCanonicalID = canonicalNodeTypeIDMap(nodeType)
    val canonicalIDName = getCanonicalName(nodeType, nodeTypeCanonicalID)
    val dotGraphName = globalNodeID.toString + ":" + getAbbrevCanonicalName(nodeType, nodeTypeCanonicalID) + ":" + readName
    val newNode = Node(globalNodeID, canonicalName = canonicalIDName, dotGraphName = dotGraphName, typeName = nodeType, readName = readName, element = element, shape = shape,
      argumentIndex = argumentIndex, rsName = rsName, clauseID = clauseID, color = color, fillColor = fillColor)
    globalNodeID += 1
    canonicalNodeTypeIDMap(nodeType) = canonicalNodeTypeIDMap(nodeType) + 1

    element match {
      case PredicateNode(pred) => {
        if (nodeType == "relationSymbol")
          globalPredicateNodeMap(pred) = newNode
      }
      case PredicateArgumentNode(pred, i, c) => {
        currentClauseIConstantNodeMap(c) = newNode
        if (nodeType == "relationSymbolArgument")
          globalPredicateArgumentNodeMap((pred, i)) = newNode
        else //clause argument
          currentClauseArgumentNodesMap(c) = newNode

      }
      case IConstantNode(c) => currentClauseIConstantNodeMap(c) = newNode
      case IVariableNode(v) => currentClauseIVariableNodeMap(v) = newNode
      case IBoolLitNode(b) => globalConstantNodeMap(newNode.readName) = newNode
      case IIntLitNode(i) => globalConstantNodeMap(newNode.readName) = newNode
      case AbstractNode(a) => {}
      case FalseNode(f) => {
        globalPredicateNodeMap(f) = newNode
      }
    }

    nodeMap += (newNode.nodeID -> newNode)
    //currentClauseNodeMap += (newNode.nodeID -> newNode)

    newNode
  }

  def createEdge(edgeType: String, edge: Array[Int])
                (color: String = edgeColorMap(edgeType), style: String = edgeStyleMap(edgeType)): Unit = {
    val newEdge = Edge(edge = edge, dotGraphName = edgeTypesAbbrev(edgeType), typeName = edgeType, color = color, style = style)
    edgeMap += (edgeType -> edgeMap(edgeType).+:(newEdge))
    if (edge.length == 2) { //add global AST and binary edges
      if (edgeType == "ASTLeftEdge" || edgeType == "ASTRightEdge") {
        val etype = "ASTEdge"
        edgeMap(etype) = edgeMap(etype).+:(Edge(edge, edgeTypesAbbrev(etype), etype))
      }
      //add global binary edges, This can be added in GNN HornGraphDataset get
      //      val etype = "binaryEdge"
      //      edgeMap(etype) = edgeMap(etype).+:(Edge(edge, edgeTypesAbbrev(etype), etype))
    } else {
      //add global ternary edges. This can be added in GNN HornGraphDataset get
      //      val etype = "ternaryHyperEdge"
      //      edgeMap(etype) = edgeMap(etype).+:(Edge(edge, edgeTypesAbbrev(etype), etype))
    }
  }


  def drawDotGraph(nodeList: Array[Node], edgeMap: mutable.HashMap[String, Array[Edge]]): Unit = {
    val dotFileName = GlobalParameters.get.fileName + "." + graphFileNameMap(GlobalParameters.get.hornGraphType) + ".gv"

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

  def outputJson(nodeList: Array[Node], edgeMap: mutable.HashMap[String, Array[Edge]], labelList: Array[Int], labelIndices: Array[Int]): Unit = {
    val nodeIndicesList = for (nt <- nodeTypes) yield {
      nt + "Indices" -> nodeList.filter(_.typeName == nt)
    }
    val nodeSymbolList = nodeList.sortBy(_.nodeID)

    val jsonFileName = GlobalParameters.get.fileName + "." + graphFileNameMap(GlobalParameters.get.hornGraphType) + ".JSON"
    val writer = new PrintWriter(new File(jsonFileName))
    writer.write("{\n")


    //write labels
    writeOneLineJson("labelNumber", Seq(labelList.length).toString, writer, changeLine = false)
    writeOneLineJson("labelList", labelList.toSeq.toString, writer)
    writeOneLineJson("labelMaskNumber", Seq(labelMask.length).toString, writer, changeLine = false)
    writeOneLineJson("labelMask", labelMask.toSeq.toString, writer)
    writeOneLineJson("labelIndicesNumber", Seq(labelIndices.length).toString, writer, changeLine = false)
    writeOneLineJson("labelIndices", labelIndices.toSeq.toString, writer)
    //write nodeID
    writeOneLineJson("nodeNumber", Seq(nodeSymbolList.length).toString, writer, changeLine = false)
    writeOneLineJson("nodeIDList", nodeSymbolList.map(_.nodeID).toSeq.toString, writer)
    //write nodeSymbolList
    writeOneLineJson("nodeSymbolList", nodeSymbolList.map("\"" + _.canonicalName + "\"").toSeq.toString, writer)
    //write indices
    for ((nt, nl) <- nodeIndicesList) {
      val listString = nl.map(_.nodeID).toSeq.toString()
      writeOneLineJson(nt + "Number", Seq(nl.length).toString, writer, changeLine = false)
      writeOneLineJson(nt, listString, writer)
    }
    //write edges
    for ((edgeType, edges) <- edgeMap) {
      val filterDummyEdges = if (edges.length == 1) edges else edges.filterNot(x => x.edge.sum == 0)
      val listString = filterDummyEdges.map(x => seqToString(x.edge.toSeq.toString())).toSeq.toString()
      writeOneLineJson(edgeType + "Number", Seq(edges.length).toString, writer, changeLine = false)
      writeOneLineJson(edgeType, listString, writer)
    }
    writeOneLineJson("endField", "[0]", writer, changeLine = false, lastEntry = true)

    writer.write("}")
    writer.close()

  }

  def createRelationSymbolNodesAndArguments(atom: IAtom): (Node, Seq[Node]) = {

    //merge rs and their arguments globally
    try {
      val rsNode = globalPredicateNodeMap(atom.pred)
      val argumentList = for ((a, i) <- atom.args.zipWithIndex) yield globalPredicateArgumentNodeMap((atom.pred, i))
      (rsNode, argumentList)
    } catch {
      case _ => {
        if (atom.pred == HornClauses.FALSE) { //if the head is false
          val rsNode = createNode("false", "false", rsName = "false", element = FalseNode(atom.pred))()
          (rsNode, Seq())
        } else {
          createNewRelationSymbolNodesAndArguments(atom, "relationSymbol",
            argumenNodeType = "relationSymbolArgument", argumentEdgeType = "relationSymbolArgumentEdge")
        }
      }
    }
  }

  def createNewRelationSymbolNodesAndArguments(atom: IAtom, atomType: String, argumenNodeType: String,
                                               argumentEdgeType: String, inverseEdgeDirection: Boolean = false):
  (Node, Seq[Node]) = {
    val atomName = atom.pred.name
    val rsNode: Node = createNode(atomType, atomName, rsName = atomName, element = PredicateNode(atom.pred))()
    val argumentNodeList = for ((a, i) <- atom.args.zipWithIndex) yield {
      //create rs argument nodes
      val argumentNode = createNode(argumenNodeType, a.toString, argumentIndex = i, rsName = atomName,
        element = PredicateArgumentNode(atom.pred, i, a.asInstanceOf[IConstant]))()
      // add edges with from argument to rs
      val edge = if (inverseEdgeDirection == true) Array(rsNode.nodeID, argumentNode.nodeID) else Array(argumentNode.nodeID, rsNode.nodeID)
      createEdge(argumentEdgeType, edge)()
      argumentNode
    }
    (rsNode, argumentNodeList)
  }

  def parseConstraint(clause: Clause): (Set[IFormula], mutable.HashMap[Node, (ITerm, IFormula)]) = {

    val bodyArguments = (for (body <- clause.body; z <- SymbolCollector.constants(body)) yield z).toSet
    val separatedFormulas = LineariseVisitor(clause.constraint, IBinJunctor.And)
    val dataFlowFormula = mutable.HashMap[Node, (ITerm, IFormula)]()
    for ((arg, i) <- clause.head.args.zipWithIndex; f <- separatedFormulas) {
      val SE = IExpression.SymbolEquation(arg)
      f match {
        case SE(coefficient, rhs) if !coefficient.isZero => {
          val rhsSymbol = SymbolCollector.constants(rhs)
          if (!Seqs.disjoint(rhsSymbol, bodyArguments)) {
            // if rhs symbol appear in body argument return headArgumentNode -> formula
            dataFlowFormula += globalPredicateArgumentNodeMap((clause.head.pred, i)) -> (arg, f)
          }
        }
        case _ =>
      }
    }
    val guardFormula = separatedFormulas.toSet.diff(dataFlowFormula.values.map(_._2).toSet)

    (guardFormula, dataFlowFormula)
  }

  def constructAST(e: IExpression): Node = {
    try {//merge sub tree
      clauseConstraintSubExpressionMap(e)
    } //find e in clauseConstraintSubExpressionMap
    catch {
      case _ => {
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
          case IQuantified(quan, subf) => {
            val opNode = createNode("operator", quan.toString, element = AbstractNode("operator"))(fillColor = "red")
            quantifierStack.push(opNode)
            val subExpressionNode = constructAST(subf)
            quantifierStack.pop()
            createEdge("ASTLeftEdge", Array(subExpressionNode.nodeID, opNode.nodeID))()
            opNode

          }
          case INot(subf) => constructUnaryRelation("!", subf)
          case IBoolLit(c) => constructEndNode(nodeType = "constant", readName = c.toString, element = IBoolLitNode(IBoolLit(c)))
          case IIntLit(c) => constructEndNode(nodeType = "constant", readName = c.toString, element = IIntLitNode(IIntLit(c)))
          case IConstant(c) => {
            constructEndNode(nodeType = "variable", readName = c.toString, element = IConstantNode(IConstant(c)))
          }
          case IVariable(v) => {
            //println(Console.RED + v)
            constructEndNode(nodeType = "variable", readName = v.toString, element = IVariableNode(IVariable(v)))
          }
          case BoolADT.True=>{//from IFunApp(fun,args)
            constructEndNode("constant", "true", element = IBoolLitNode(IBoolLit(true)))
          }
          case BoolADT.False => {//from IFunApp(fun,args)
            constructEndNode("constant", "false", element = IBoolLitNode(IBoolLit(false)))
          }
          case _ => {
            println(Console.RED+"unknown node",e,e.getClass)
            createNode("unknown", "unkown", element = AbstractNode("unkown"))()}
        }
        clauseConstraintSubExpressionMap += (e -> astRootNode)
        astRootNode
      }
    }
  }

  def constructBinaryRelation(op: String, left: IExpression, right: IExpression): Node = {
    val opNode = createNode("operator", op, element = AbstractNode(op))()
    val leftNode = constructAST(left)
    val rightNode = constructAST(right)
    createEdge("ASTLeftEdge", Array(leftNode.nodeID, opNode.nodeID))()
    createEdge("ASTRightEdge", Array(rightNode.nodeID, opNode.nodeID))()
    opNode
  }

  def constructUnaryRelation(op: String, e: IExpression): Node = {
    val opNode = createNode("operator", op, element = AbstractNode(op))()
    val subExpressionNode = constructAST(e)
    createEdge("ASTLeftEdge", Array(subExpressionNode.nodeID, opNode.nodeID))()
    opNode
  }

  def constructEndNode(nodeType: String, readName: String, element: NodeElement): Node = {
    try {
      element match {
        case IConstantNode(c) => {
          if (GlobalParameters.get.hornGraphType == HornGraphType.CG) {
            // if it has corresponding ca node
            val correspondingArg = currentClauseArgumentNodesMap(c)
            val endNode = createNode(nodeType, readName, element)()
            createEdge("dataEdge", Array(endNode.nodeID, correspondingArg.nodeID))()
            endNode
          }
          else
            currentClauseIConstantNodeMap(c)
        }
        case IVariableNode(v) => {
          if (astSource == ASTSouce.clause) {
            try {
              currentClauseIVariableNodeMap(v)
            } catch {
              case _ => {
                val newNode = createNode(nodeType, readName = readName, element)()
                createEdge("quantifierEdge", Array(newNode.nodeID, quantifierStack.top.nodeID))()
                newNode
              }
            }

          } else //astSource == ASTSouce.template, merge with rsa
            globalPredicateArgumentNodeMap(currentPred, v.index)
        }
        case IBoolLitNode(b) => globalConstantNodeMap(b.toString())
        case IIntLitNode(i) => globalConstantNodeMap(i.toString())
      }
    }
    catch {
      case _ => createNode(nodeType, readName = readName, element)()
    }

  }


  def constructTemplates(templateMap: Map[String, VerificationHints]): Array[(Int, Int)] = {
    astSource = ASTSouce.template

    val unlabeledTemplate = templateMap("unlabeled")
    val labeledTemplates = templateMap("labeled")

    val templateRelevanceLabelList = for ((pred, temps) <- unlabeledTemplate.predicateHints.toSeq; t <- temps) yield {
      val transformedTemplate = transformBooleanTermToVerifHintTplPredPosNeg(t)

      currentPred = pred
      val currentRsaNodeList = for (i <- Array.range(0, pred.arity)) yield globalPredicateArgumentNodeMap((pred, i))
      //for (a <- (currentRsaNodeList ++ globalConstantNodeMap.values)) currentClauseNodeMap(a.nodeID) = a
      val (templateRelevanceLabel, labelIndex) = transformedTemplate match {
        case VerifHintTplEqTerm(e, cost) => createTemplateNodeAndCorrespondingEdges("templateEq", pred, e, transformedTemplate, labeledTemplates)
        case VerifHintTplInEqTerm(e, cost) => createTemplateNodeAndCorrespondingEdges("templateIneq", pred, e, transformedTemplate, labeledTemplates)
        case VerifHintTplPredPosNeg(e, cost) => createTemplateNodeAndCorrespondingEdges("templateBool", pred, e, transformedTemplate, labeledTemplates)
      }
      clauseConstraintSubExpressionMap.clear()
      //currentClauseNodeMap.clear()
      (templateRelevanceLabel, labelIndex)
    }
    templateRelevanceLabelList.toArray

  }

  def createTemplateNodeAndCorrespondingEdges(templateType: String, pred: Predicate, e: IExpression,
                                              t: VerifHintElement,
                                              labeledTemplates: VerificationHints): (Int, Int) = {
    val labeledTemplateInPred = if (labeledTemplates.predicateHints.keys.toSeq.contains(pred)) labeledTemplates.predicateHints(pred) else Seq()
    val templateLabelBoolean = verifHintElementContains(labeledTemplateInPred, t)
    val templateLabel = if (templateLabelBoolean == true) 1 else 0
    val templateNodeColor = if (templateLabelBoolean == true) "green" else "red"
    val templateNode = createNode(templateType, templateType, element = AbstractNode(templateType))(color = templateNodeColor)
    //edge from rs to templates
    createEdge("templateEdge", Array(globalPredicateNodeMap(pred).nodeID, templateNode.nodeID))()
    //ast root node
    val astRootNode = constructAST(e)
    //edge from ast note to template node
    createEdge("templateASTEdge", Array(astRootNode.nodeID, templateNode.nodeID))()


    (templateLabel, templateNode.nodeID)
  }

  def getLabel(bodyReplacedClauses: Seq[Clauses] = Seq()): Unit = {
    GlobalParameters.get.hornGraphLabelType match {
      case HornGraphLabelType.template => {
        val templates = readTemplateMap(clauses)
        val labelPair = logTime(constructTemplates(templates), "construct templates")
        labelList = labelPair.map(_._1)
        labelIndices = labelPair.map(_._2)
      }

      case HornGraphLabelType.unsatCore => {
        val clauseNodeName = GlobalParameters.get.hornGraphType match {
          case HornGraphType.CDHG => "guard"
          case HornGraphType.CG => "clause"
        }
        val clauseIndicesList = nodeMap.values.toArray.filter(_.typeName == clauseNodeName).map(_.nodeID)
        labelIndices = clauseIndicesList

        val counterExampleIndexFileName = GlobalParameters.get.fileName + ".counterExampleIndex.JSON"
        val readLabelList =
          if (new java.io.File(counterExampleIndexFileName).exists) { //if there is label file
            readJsonFieldInt(counterExampleIndexFileName, readLabelName = "counterExampleLabels")
          } else { // no label file
            (for (x <- labelIndices) yield 0).toArray
          }

        labelList = GlobalParameters.get.hornGraphType match {
          case HornGraphType.CDHG => {
            var originalClausesCounter = 0
            labelMask = (for ((c, ci) <- bodyReplacedClauses.zipWithIndex) yield {
              println(ci, c.length, c)
              val index = originalClausesCounter
              for (i <- (0 until c.length)) yield {
                originalClausesCounter += 1
                index
              }
            }).flatten.toArray

            val extendedLabelList = for ((l, c) <- readLabelList.zip(bodyReplacedClauses)) yield {
              for (i <- (0 until c.length)) yield l
            }
            extendedLabelList.flatten
          }

          case HornGraphType.CG => {
            readLabelList
          }
        }

      }

    }
    if (GlobalParameters.get.log) {
      println("labelIndices", labelIndices.length, labelIndices.mkString)
      println("labelList", labelList.length, labelList.mkString)
    }

  }


}


class CDHG(clauses: Clauses) extends HornGraph(clauses: Clauses) {

  //notice: templates are only correspond to the original clauses
  val (normalizedClauses, bodyReplacedClauses) = normalizeClauses(clauses, VerificationHints(Map()))

  //create initial rs node
  val initialNode = createNode("initial", "initial", element = AbstractNode("initial"))()
  //create true constant node
  globalConstantNodeMap("true") = createNode("constant", "true", element = IBoolLitNode(IBoolLit(true)))()
  var clauseCount = 0

  for (clause <- normalizedClauses) {

    //create head relation symbol node
    val rsHeadNode = createRelationSymbolNodesAndArguments(clause.head)
    //create body nodes
    val rsBodyNodeList = for (b <- clause.body) yield createRelationSymbolNodesAndArguments(b)

    for (atom <- clause.allAtoms; (arg, i) <- atom.args.zipWithIndex) currentClauseIConstantNodeMap +=
      (arg.asInstanceOf[IConstant] -> globalPredicateArgumentNodeMap((atom.pred, i)))

    //parse guard and data formula
    val (guardFormula, dataFlowFormula) = parseConstraint(clause)

    //construct guard node
    val guardNode = createNode("guard", "G", clauseID = clauseCount, element = AbstractNode("guard"))()
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
          //println("coefficient",coefficient,"rhs", rhs)
          val rhsASTRoot =
            if (coefficient.isZero)
              globalConstantNodeMap("0")
            else
              constructAST(sp(rhs *** coefficient))
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
      for (rsb <- rsBodyNodeList) {
        createEdge("controlFlowHyperEdge", Array(rsb._1.nodeID, guardNode.nodeID, rsHeadNode._1.nodeID))()
      }

    currentClauseIVariableNodeMap.clear()
    currentClauseIConstantNodeMap.clear()
    clauseConstraintSubExpressionMap.clear()

    clauseCount += 1


    if (GlobalParameters.get.log) {
      println(Console.BLUE + clause.toPrologString)
      println("guardFormula", guardFormula.map(_.toString))
      println("dataFlowFormula", dataFlowFormula.map(_._2._2.toString))
      //      for ((k, v) <- clauseConstraintSubExpressionMap)
      //        println(k, v.readName)
    }

  }

  getLabel(bodyReplacedClauses)

  if (GlobalParameters.get.visualizeHornGraph)
    logTime(drawDotGraph(nodeList = nodeMap.values.toArray, edgeMap = edgeMap), "write dot graph")
  logTime(outputJson(nodeList = nodeMap.values.toArray, edgeMap = edgeMap, labelList, labelIndices), "write graph to JSON")

}

class CG(clauses: Clauses) extends HornGraph(clauses: Clauses) {
  //notice: templates are only correspond to the original clauses
  val simplifiedClauses = simplifyClauses(clauses, VerificationHints(Map()))
  var clauseCount = 0
  //predicate layer
  val rsNodes = for (clause <- simplifiedClauses; atom <- clause.allAtoms) yield {
    createRelationSymbolNodesAndArguments(atom)
  }

  for (clause <- simplifiedClauses) {
    for (atom <- clause.allAtoms; (arg, i) <- atom.args.zipWithIndex) currentClauseIConstantNodeMap +=
      (arg.asInstanceOf[IConstant] -> globalPredicateArgumentNodeMap((atom.pred, i)))
    //clause layer
    // create clause head and body and their argument nodes
    val clauseHeadNode = createNewRelationSymbolNodesAndArguments(clause.head, "clauseHead",
      argumenNodeType = "clauseArgument", argumentEdgeType = "clauseArgumentEdge")
    val clauseBodyNodeList = for (b <- clause.body) yield createNewRelationSymbolNodesAndArguments(b,
      "clauseBody", argumenNodeType = "clauseArgument", argumentEdgeType = "clauseArgumentEdge")

    //create clause node
    val clauseNode = createNode("clause", "clause_" + clauseCount.toString, element = AbstractNode("clause"))()
    //connect clause head and body to clause node
    createEdge("clauseHeadEdge", Array(clauseHeadNode._1.nodeID, clauseNode.nodeID))()
    for (cbn <- clauseBodyNodeList)
      createEdge("clauseBodyEdge", Array(cbn._1.nodeID, clauseNode.nodeID))()

    //connect from clause layer to predicate layer
    for ((atom, rsNode) <- clause.allAtoms zip Seq(clauseHeadNode) ++ clauseBodyNodeList) {
      val correspondingRs = globalPredicateNodeMap(atom.pred)
      createEdge("relationSymbolInstanceEdge", Array(rsNode._1.nodeID, correspondingRs.nodeID))()
      for (((a, i), argNode) <- atom.args.zipWithIndex zip rsNode._2) {
        val correspondingArg = globalPredicateArgumentNodeMap((atom.pred, i))
        createEdge("argumentInstanceEdge", Array(argNode.nodeID, correspondingArg.nodeID))()
      }
    }

    //constraint layer and connections
    val subConstraintFormulas = LineariseVisitor(clause.constraint, IBinJunctor.And)
    val constraintRootNodes = for (subf <- subConstraintFormulas) yield constructAST(subf)
    for (r <- constraintRootNodes)
      createEdge("guardEdge", Array(r.nodeID, clauseNode.nodeID))()


    currentClauseArgumentNodesMap.clear()
    currentClauseIVariableNodeMap.clear()
    currentClauseIConstantNodeMap.clear()
    clauseConstraintSubExpressionMap.clear()

    clauseCount += 1

    if (GlobalParameters.get.log) {
      println(Console.BLUE + clause.toPrologString)
    }
  }

  getLabel()

  if (GlobalParameters.get.visualizeHornGraph)
    logTime(drawDotGraph(nodeList = nodeMap.values.toArray, edgeMap = edgeMap), "write dot graph")
  logTime(outputJson(nodeList = nodeMap.values.toArray, edgeMap = edgeMap, labelList, labelIndices), "write graph to JSON")

}