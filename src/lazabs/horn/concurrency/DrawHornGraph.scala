/**
 * Copyright (c) 2011-2020 Philipp Ruemmer, Chencheng Liang All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 * list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
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
package lazabs.horn.concurrency

import java.io.{File, PrintWriter}
import ap.basetypes.IdealInt
import ap.parser.IExpression._
import ap.parser.{IExpression, _}
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints.VerifHintInitPred
import lazabs.horn.bottomup.HornClauses.{Clause, FALSE}
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import lazabs.horn.concurrency.DrawHornGraph.{HornGraphType, addQuotes, isNumeric}
import lazabs.horn.concurrency.HintsSelection.{detectIfAJSONFieldExists, spAPI}

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap, Map => MuMap}

object DrawHornGraph {

  object HornGraphType extends Enumeration {
    //type HornGraphType = Value
    val hyperEdgeGraph,concretizedHyperedgeGraph,equivalentHyperedgeGraph, monoDirectionLayerGraph,biDirectionLayerGraph, hybridDirectionLayerGraph, clauseRelatedTaskLayerGraph, fineGrainedEdgeTypeLayerGraph= Value
  }

  def addQuotes(str: String): String = {
    return "\"" + str + "\""
  }

  def isNumeric(input: String): Boolean = {
    if (input != "" && input.forall(_.isDigit)) true
    else false
  }
}


class argumentInfoHronGraph(headName: String, ind: Int, globalIndex: Int) {
  var ID = 0
  val head = headName
  val index = ind
  val name = "argument" + ind.toString
  var score = 0
  var bound: Pair[String, String] = (addQuotes("None"),addQuotes("None"))
  val globalIndexInGraph = globalIndex
  var binaryOccurrenceInTemplates=0
  var constNames=Array[String]()
  var canonicalName=""
}

class Adjacency(edge_name: String, edge_number: Int) {
  val edgeName = edge_name
  val edgeNumber = edge_number

  //var edgeList=new ListBuffer[ListBuffer[Int]]()
  var binaryEdge = Array[Tuple2[Int, Int]]()
  var ternaryEdge = Array[Tuple3[Int, Int, Int]]()

  def incrementBinaryEdge(from: Int, to: Int): Unit =
    binaryEdge :+= Tuple2(from, to)

  def incrementTernaryEdge(from: Int, to1: Int, to2: Int): Unit =
    ternaryEdge :+= Tuple3(from, to1, to2)
}

class GNNInput(clauseCollection:ClauseInfo) {
  val simpClauses=clauseCollection.simplifiedClause
  val clausesInCE = clauseCollection.clausesInCounterExample
  var GNNNodeID = 0
  var hyperEdgeNodeID = 0
  var TotalNodeID = 0
  //canonical node category for hyperedge horn graph
  var CONTROLCanonicalID, argumentCanonicalID, predicateCanonicalID, iEpsilonCanonicalID, iFormulaITECanonicalID, iFunAppCanonicalID,
  iNamePartCanonicalID, iTermITECanonicalID, iTriggerCanonicalID, variableCanonicalID, symbolicConstantCanonicalID,
  controlFlowHyperEdgeCanonicalID, dataFlowHyperEdgeCanonicalID = 0

  //canonical node category for layer horn graph
  var clauseHeadCanonicalID, clauseBodyCanonicalID, clauseArgCanonicalID, clauseCanonicalID, predicateNameCanonicalID,
  predicateArgumentCanonicalID, operatorUniqueID, constantUniqueID = 0

  //canonical node category for both graph
  var templateCanonicalID=0

  var nodeIds = Array[Int]()
  //var nodeSymbols = new ListBuffer[String]()
  var nodeSymbols = Array[String]()

  var binaryAdjacency = new Adjacency("binaryEdge", edge_number = 2)
  var ternaryAdjacency = new Adjacency("ternaryEdge", 3)
  //edge category for hyperedge horn graph
  val dataFlowASTEdges = new Adjacency("dataFlowASTEdge", 2)
  val guardASTEdges = new Adjacency("guardASTEdge", 2)
  val ASTEdges = new Adjacency("ASTEdge", 2)
  val AST_1Edges = new Adjacency("AST_1Edges", 2)
  val AST_2Edges = new Adjacency("AST_2Edges", 2)
  val templateASTEdges = new Adjacency("templateASTEdge", 2)
  val templateEdges = new Adjacency("templateEdge", 2)
  //val dataFlowEdges = new Adjacency("dataFlowEdge", 2)
  val argumentEdges = new Adjacency("argumentEdge", 2)
  val controlFlowHyperEdges = new Adjacency("controlFlowHyperEdge", 3)
  val dataFlowHyperEdges = new Adjacency("dataFlowHyperEdge", 3)
  val clauseEdges = new Adjacency("clauseEdge", 2)

  //edge category for layer version horn graph
  val predicateArgumentEdges = new Adjacency("predicateArgument", 2)
  val predicateInstanceEdges = new Adjacency("predicateInstance", 2)
  val argumentInstanceEdges = new Adjacency("argumentInstance", 2)
  val controlHeadEdges = new Adjacency("controlHead", 2)
  val controlBodyEdges = new Adjacency("controlBody", 2)
  val controlEdges = new Adjacency("controlBody", 2)
  val controlArgumentEdges = new Adjacency("controlArgument", 2)
  val guardEdges = new Adjacency("guard", 2)
  val dataEdges = new Adjacency("data", 2)
  val subTermEdges = new Adjacency("subTerm", 2)
  val unknownEdges = new Adjacency("unknownEdges", 2)

  val predicateInstanceHeadEdges = new Adjacency("predicateInstanceHead", 2)
  val predicateInstanceBodyEdges = new Adjacency("predicateInstanceBody", 2)
  val controlArgumentHeadEdges = new Adjacency("controlArgumentHead", 2)
  val controlArgumentBodyEdges = new Adjacency("controlArgumentBody", 2)
  val guardConstantEdges = new Adjacency("guardConstant", 2)
  val guardOperatorEdges = new Adjacency("guardOperator", 2)
  val guardScEdges = new Adjacency("guardSc", 2)
  val dataConstantEdges = new Adjacency("dataConstant", 2)
  val dataOperatorEdges = new Adjacency("dataOperator", 2)
  val dataScEdges = new Adjacency("dataSc", 2)
  val subTermConstantOperatorEdges = new Adjacency("subTermConstantOperator", 2)
  val subTermOperatorOperatorEdges = new Adjacency("subTermOperatorOperator", 2)
  val subTermScOperatorEdges = new Adjacency("subTermScOperator", 2)

  var controlLocationIndices = Array[Int]()
  var falseIndices = Array[Int]()
  var argumentIndices = Array[Int]()
  var templateIndices = Array[Int]()
  var templateRelevanceLabel = Array[Int]()
  var clauseIndices = Array[Int]()
  var predicateIndices = Array[Int]()
  var predicateOccurrenceInClause = Array[Int]()
  var clausesOccurrenceInCounterExample = Array[Int]()
  var predicateStrongConnectedComponent = Array[Int]()
  var argumentInfoHornGraphList = new ArrayBuffer[argumentInfoHronGraph]
  var nodeNameToIDMap = MuMap[String, Int]()

  val learningLabel= new FormLearningLabels(clauseCollection)
  val predicateOccurrenceInClauseLabel=learningLabel.getPredicateOccurenceInClauses()
  val predicateStrongConnectedComponentLabel=learningLabel.getStrongConnectedComponentPredicateList()

  def incrementBinaryEdge(from: String, to: String, label: String): Unit = {
    val fromID = nodeNameToIDMap(from)
    val toID = nodeNameToIDMap(to)
    GlobalParameters.get.hornGraphType match {
      case HornGraphType.hyperEdgeGraph | HornGraphType.equivalentHyperedgeGraph | HornGraphType.concretizedHyperedgeGraph=> {
        label match {
          // hyperedge graph
          case "dataFlowAST" => dataFlowASTEdges.incrementBinaryEdge(fromID, toID)
          case "guardAST" => guardASTEdges.incrementBinaryEdge(fromID, toID)
          case "AST" => ASTEdges.incrementBinaryEdge(fromID, toID)
          case "AST_1" => AST_1Edges.incrementBinaryEdge(fromID, toID)
          case "AST_2" => AST_2Edges.incrementBinaryEdge(fromID, toID)
          case "templateAST" => templateASTEdges.incrementBinaryEdge(fromID, toID)
          case "template" => templateEdges.incrementBinaryEdge(fromID, toID)
          case "argument" => argumentEdges.incrementBinaryEdge(fromID, toID)
          case "clause" => clauseEdges.incrementBinaryEdge(fromID,toID)
          case "controlFlowHyperEdge"=> controlFlowHyperEdges.incrementBinaryEdge(fromID,toID)
          case "dataFlowHyperEdge" => dataFlowHyperEdges.incrementBinaryEdge(fromID,toID)
          case _ => unknownEdges.incrementBinaryEdge(fromID, toID)
        }
      }
      case _ => {
        label match {
          //layer graph
          case "predicateArgument" => predicateArgumentEdges.incrementBinaryEdge(fromID, toID)
          case "predicateInstance" => predicateInstanceEdges.incrementBinaryEdge(fromID, toID)
          case "argumentInstance" => argumentInstanceEdges.incrementBinaryEdge(fromID, toID)
          case "controlHead" => controlHeadEdges.incrementBinaryEdge(fromID, toID)
          case "controlBody" => controlBodyEdges.incrementBinaryEdge(fromID, toID)
          case "control" => controlEdges.incrementBinaryEdge(fromID, toID)
          case "controlArgument" => controlArgumentEdges.incrementBinaryEdge(fromID, toID)
          case "guard" => guardEdges.incrementBinaryEdge(fromID, toID)
          case "data" => dataEdges.incrementBinaryEdge(fromID, toID)
          case "subTerm" => subTermEdges.incrementBinaryEdge(fromID, toID)
          case "templateAST" => templateASTEdges.incrementBinaryEdge(fromID, toID)
          case "template" => templateEdges.incrementBinaryEdge(fromID, toID)
          case "predicateInstanceHead"=> predicateInstanceHeadEdges.incrementBinaryEdge(fromID, toID)
          case "predicateInstanceBody"=> predicateInstanceBodyEdges.incrementBinaryEdge(fromID, toID)
          case "controlArgumentHead"=> controlArgumentHeadEdges.incrementBinaryEdge(fromID, toID)
          case "controlArgumentBody"=>controlArgumentBodyEdges.incrementBinaryEdge(fromID, toID)
          case "guardConstant"=>guardConstantEdges.incrementBinaryEdge(fromID, toID)
          case "guardOperator"=>guardOperatorEdges.incrementBinaryEdge(fromID, toID)
          case "guardSc"=>guardScEdges.incrementBinaryEdge(fromID, toID)
          case "dataConstant"=>dataConstantEdges.incrementBinaryEdge(fromID, toID)
          case "dataOperator"=>dataOperatorEdges.incrementBinaryEdge(fromID, toID)
          case "dataSc"=>dataScEdges.incrementBinaryEdge(fromID, toID)
          case "subTermConstantOperator"=>subTermConstantOperatorEdges.incrementBinaryEdge(fromID, toID)
          case "subTermOperatorOperator"=>subTermOperatorOperatorEdges.incrementBinaryEdge(fromID, toID)
          case "subTermScOperator"=>subTermScOperatorEdges.incrementBinaryEdge(fromID, toID)

        }
      }
    }
    binaryAdjacency.incrementBinaryEdge(fromID, toID)
  }

  def incrementTernaryEdge(from: String, middle: String, to: String, label: String): Unit = {
    val fromID = nodeNameToIDMap(from)
    val middleID = nodeNameToIDMap(middle)
    val toID = nodeNameToIDMap(to)
    label match {
      // hyperedge graph
      case "controlFlowHyperEdge" => controlFlowHyperEdges.incrementTernaryEdge(fromID, middleID, toID)
      case "dataFlowHyperEdge" => dataFlowHyperEdges.incrementTernaryEdge(fromID, middleID, toID)
      case _ => unknownEdges.incrementTernaryEdge(fromID, middleID, toID)
    }
    ternaryAdjacency.incrementTernaryEdge(fromID, middleID, toID)
  }

  def incrementFalseIndicesAndNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String): Unit = {
    falseIndices :+= GNNNodeID
    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
  }

  def incrementArgumentIndicesAndNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String): Unit = {
    argumentIndices :+= GNNNodeID
    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
  }
  def incrementTemplateIndicesAndNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String,hintLabel:Boolean): Unit = {
    templateIndices :+= GNNNodeID
    hintLabel match {
      case true =>templateRelevanceLabel:+=1
      case false =>templateRelevanceLabel:+=0
    }
    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
  }
  def updateTemplateIndicesAndNodeIds(nodeUniqueName:String,hintLabel:Boolean): Unit ={
    templateIndices :+= nodeNameToIDMap(nodeUniqueName)
    hintLabel match {
      case true =>templateRelevanceLabel:+=1
      case false =>templateRelevanceLabel:+=0
    }
    templateCanonicalID += 1
  }
  def incrementClauseIndicesAndNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String,clauseInfo:Clauses): Unit ={
    clauseIndices :+=GNNNodeID
    if (!clauseInfo.isEmpty && clausesInCE.map(_.toString).contains(clauseInfo.head.toString)) {
      clausesOccurrenceInCounterExample :+=1
    } else
      clausesOccurrenceInCounterExample :+=0
    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
  }

  def incrementControlLocationIndicesAndNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String): Unit = {
    controlLocationIndices :+= GNNNodeID
    for (l<-predicateOccurrenceInClauseLabel) if (l._1.name==nodeName) {
      predicateIndices :+= GNNNodeID
      predicateOccurrenceInClause :+= l._2
      predicateStrongConnectedComponent:+=predicateStrongConnectedComponentLabel(nodeName)
    }

    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
  }

  def incrementPredicateIndicesAndNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String): Unit = {
    for (l<-predicateOccurrenceInClauseLabel) if (l._1.name==nodeName) {
      predicateIndices :+= GNNNodeID
      predicateOccurrenceInClause :+= l._2
      predicateStrongConnectedComponent:+=predicateStrongConnectedComponentLabel(nodeName)
    }
    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
  }

  def incrementNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String): Unit = {
    //check if total node number larger than max_node
    if(nodeIds.size>GlobalParameters.get.maxNode){
      println(Console.RED + "-"*10 +"node number >= maxNode" + "-"*10)
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/exceed-max-node/" + GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/"),GlobalParameters.get.fileName.length))
      HintsSelection.removeRelativeFiles(GlobalParameters.get.fileName)
      sys.exit()
    }
    nodeIds :+= GNNNodeID
    nodeNameToIDMap(nodeUniqueName) = GNNNodeID
    GNNNodeID += 1
    nodeClass match {
      case "CONTROL" => {
        nodeSymbols :+= nodeClass + "_" + CONTROLCanonicalID.toString
        CONTROLCanonicalID += 1
      }
      case "argument" => {
        nodeSymbols :+= nodeClass + "_" + argumentCanonicalID.toString
        argumentCanonicalID += 1
      }
      case "predicate" => {
        nodeSymbols :+= nodeClass + "_" + predicateCanonicalID.toString
        predicateCanonicalID += 1
      }
      case "IEpsilon" => {
        nodeSymbols :+= nodeClass + "_" + iEpsilonCanonicalID.toString
        iEpsilonCanonicalID += 1
      }
      case "IFormulaITE" => {
        nodeSymbols :+= nodeClass + "_" + iFormulaITECanonicalID.toString
        iFormulaITECanonicalID += 1
      }
      case "IFunApp" => {
        nodeSymbols :+= nodeClass + "_" + iFunAppCanonicalID.toString
        iFunAppCanonicalID += 1
      }
      case "INamePart" => {
        nodeSymbols :+= nodeClass + "_" + iNamePartCanonicalID.toString
        iNamePartCanonicalID += 1
      }
      case "ITermITE" => {
        nodeSymbols :+= nodeClass + "_" + iTermITECanonicalID.toString
        iTermITECanonicalID += 1
      }
      case "ITrigger" => {
        nodeSymbols :+= nodeClass + "_" + iTriggerCanonicalID.toString
        iTriggerCanonicalID += 1
      }
      case "variable" => {
        nodeSymbols :+= nodeClass + "_" + variableCanonicalID.toString
        variableCanonicalID += 1
      }
      case "symbolicConstant" => {
        nodeSymbols :+= nodeClass + "_" + symbolicConstantCanonicalID.toString
        symbolicConstantCanonicalID += 1
      }
      case "clauseHead" => {
        nodeSymbols :+= nodeClass + "_" + clauseHeadCanonicalID.toString
        clauseHeadCanonicalID += 1
      }
      case "clauseBody" => {
        nodeSymbols :+= nodeClass + "_" + clauseBodyCanonicalID.toString
        clauseBodyCanonicalID += 1
      }
      case "clauseArgument" => {
        nodeSymbols :+= nodeClass + "_" + clauseArgCanonicalID.toString
        clauseArgCanonicalID += 1
      }
      case "clause" => {
        nodeSymbols :+= nodeClass + "_" + clauseCanonicalID.toString
        clauseCanonicalID += 1
      }
      case "predicateName" => {
        nodeSymbols :+= nodeClass + "_" + predicateNameCanonicalID.toString
        predicateNameCanonicalID += 1
      }
      case "predicateArgument" => {
        nodeSymbols :+= nodeClass + "_" + predicateArgumentCanonicalID.toString
        predicateArgumentCanonicalID += 1
      }
      case "template" => {
        nodeSymbols :+= nodeClass + "_" + templateCanonicalID.toString
        templateCanonicalID += 1
      }
      case "controlFlowHyperEdge"=>
        nodeSymbols :+= nodeClass + "_" + controlFlowHyperEdgeCanonicalID.toString
      case "dataFlowHyperEdge"=>
        nodeSymbols :+= nodeClass + "_" + dataFlowHyperEdgeCanonicalID.toString
      case "FALSE" => nodeSymbols :+= nodeName
      case "operator" => nodeSymbols :+= nodeName
      case "constant" => nodeSymbols :+= nodeName
      case _ => nodeSymbols :+= nodeName
    }
  }
}

class DrawHornGraph(file: String, clausesCollection: ClauseInfo, hints: VerificationHintsInfo, argumentInfoList: ArrayBuffer[argumentInfo]) {
  val sp = new Simplifier()
  val spAPI = ap.SimpleAPI.spawn
  val simpClauses = clausesCollection.simplifiedClause
  val clausesInCE = clausesCollection.clausesInCounterExample
  val graphType = GlobalParameters.get.hornGraphType match {
    case DrawHornGraph.HornGraphType.hyperEdgeGraph => "hyperEdgeHornGraph"
    case DrawHornGraph.HornGraphType.hybridDirectionLayerGraph => "hybrid-layerHornGraph"
    case DrawHornGraph.HornGraphType.biDirectionLayerGraph => "bi-layerHornGraph"
    case DrawHornGraph.HornGraphType.monoDirectionLayerGraph => "mono-layerHornGraph"
    case DrawHornGraph.HornGraphType.clauseRelatedTaskLayerGraph => "clause-related-task-layerHornGraph"
    case DrawHornGraph.HornGraphType.fineGrainedEdgeTypeLayerGraph => "fine-grained-edge-type-layerHornGraph"
    case DrawHornGraph.HornGraphType.equivalentHyperedgeGraph => "equivalent-hyperedgeGraph"
    case DrawHornGraph.HornGraphType.concretizedHyperedgeGraph => "concretized-hyperedgeGraph"
  }
  val templateNodePrefix = "template_"
  var edgeNameMap: Map[String, String] = Map()
  var edgeDirectionMap: scala.collection.immutable.Map[String,Boolean] = Map()
  var nodeShapeMap: Map[String, String] = Map()
  val binaryOperatorSubGraphSetInOneClause = scala.collection.mutable.Map[String, Tuple2[String,String]]()
  val unaryOperatorSubGraphSetInOneClause = scala.collection.mutable.Map[String, String]()
  val constantNodeSetCrossGraph = scala.collection.mutable.Map[String, String]()
  val constantNodeSetInOneClause = scala.collection.mutable.Map[String, String]() //map[constantName->constantNameWithCanonicalNumber]
  val argumentNodeSetInPredicates = scala.collection.mutable.Map[String, String]() //map[argumentConstantName->argumentNameWithCanonicalNumber]
  val controlFlowNodeSetInOneClause = scala.collection.mutable.Map[String, String]()// predicate.name -> canonical name
  val argumentNodeSetInOneClause = scala.collection.mutable.Map[String, Array[String]]() //predicateName:String -> arguments Array[String]
  var astEdgeType = ""
  var astEndNodeType=""
  val gnn_input = new GNNInput(clausesCollection)
  val writerGraph = new PrintWriter(new File(file + "." + graphType + ".gv"))

  edgeNameMap += ("templateAST"->"pAST")
  edgeNameMap += ("template"->"predicate")
  edgeDirectionMap += ("templateAST"->false)
  edgeDirectionMap += ("template" -> false)
  nodeShapeMap += ("template" -> "component")

  writerGraph.write("digraph dag {" + "\n")


  def addBinaryEdge(from: String, to: String, label: String, biDirection: Boolean = false): Unit =
    biDirection match {
      case true => {
        writerGraph.write(addQuotes(from) + " -> " + addQuotes(to) +
          " [dir=\"both\", label=" + addQuotes(edgeNameMap(label)) + "]" + "\n")
        gnn_input.incrementBinaryEdge(from, to, label)
        gnn_input.incrementBinaryEdge(to, from, label)
      }
      case false => {
        writerGraph.write(addQuotes(from) + " -> " + addQuotes(to) +
          " [label=" + addQuotes(edgeNameMap(label)) + "]" + "\n")
        gnn_input.incrementBinaryEdge(from, to, label)
      }
    }

  def drawTernaryEdge(from: String, guard: String, to: String, hyperEdgeName: String, label: String): Unit ={
    //fromNode to hyperedge
    writerGraph.write(addQuotes(from) + " -> " + addQuotes(hyperEdgeName) +
      " [label=" + addQuotes(edgeNameMap(label)) + "]" + "\n")
    //guardNode to hyperedge
    writerGraph.write(addQuotes(guard) + " -> " + addQuotes(hyperEdgeName) +
      " [label=" + addQuotes(edgeNameMap(label)) + "]" + "\n")
    //hyperedge to toNode
    writerGraph.write(addQuotes(hyperEdgeName) + " -> " + addQuotes(to) +
      " [label=" + addQuotes(edgeNameMap(label)) + "]" + "\n")
  }

  def addTernaryEdge(from: String, guard: String, to: String, hyperEdgeName: String, label: String): Unit = {
    drawTernaryEdge(from,guard,to,hyperEdgeName,label)
    //form gnn input
    gnn_input.incrementTernaryEdge(from, guard, to, label)
  }

  def addConcretinizedTernaryEdge(from: String, guard: String, to: String, hyperEdgeName: String, label: String): Unit ={
    drawTernaryEdge(from,guard,to,hyperEdgeName,label)
    gnn_input.incrementBinaryEdge(from,hyperEdgeName,label)
    gnn_input.incrementBinaryEdge(guard,hyperEdgeName,label)
    gnn_input.incrementBinaryEdge(hyperEdgeName,to,label)
  }

  def updateTernaryEdge(from: String, guard: String, to: String, hyperEdgeName: String, label: String): Unit = {
    //guardNode to hyperedge
    writerGraph.write(addQuotes(guard) + " -> " + addQuotes(hyperEdgeName) +
      " [label=" + addQuotes(edgeNameMap(label)) + "]" + "\n")
    gnn_input.incrementTernaryEdge(from, guard, to, label)
  }
  def updateConcretinizedTernaryEdge(from: String, guard: String, to: String, hyperEdgeName: String, label: String): Unit ={
    writerGraph.write(addQuotes(guard) + " -> " + addQuotes(hyperEdgeName) +
      " [label=" + addQuotes(edgeNameMap(label)) + "]" + "\n")
    gnn_input.incrementBinaryEdge(from,hyperEdgeName,label)
    gnn_input.incrementBinaryEdge(guard,hyperEdgeName,label)
    gnn_input.incrementBinaryEdge(hyperEdgeName,to,label)
  }

  def addEdgeInSubTerm(from: String, to: String, fromNodeLabel: String = ""): Unit = {
    if (!to.isEmpty) {
      GlobalParameters.get.hornGraphType match {
        case HornGraphType.hyperEdgeGraph | HornGraphType.equivalentHyperedgeGraph | HornGraphType.concretizedHyperedgeGraph => addBinaryEdge(from, to, astEdgeType, edgeDirectionMap(astEdgeType))
        case HornGraphType.clauseRelatedTaskLayerGraph => {
          astEdgeType match {
            case "templateAST" => addBinaryEdge(from, to, "templateAST", edgeDirectionMap("templateAST"))
            case "data" => addBinaryEdge(from, to, "data", edgeDirectionMap("data"))
            case "guard" => addBinaryEdge(from, to, "guard", edgeDirectionMap("guard"))
          }
        }
        case HornGraphType.fineGrainedEdgeTypeLayerGraph => {
          val toNodeClass = to.substring(0, to.indexOf("_"))
          toNodeClass match {
            case "clause" => {
              fromNodeLabel match {
                case "operator" => addBinaryEdge(from, to, "guardOperator", edgeDirectionMap("guardOperator"))
                case "constant" => addBinaryEdge(from, to, "guardConstant", edgeDirectionMap("guardConstant"))
                case "symbolicConstant" => addBinaryEdge(from, to, "guardSc", edgeDirectionMap("guardSc"))
                case _ => addBinaryEdge(from, to, "guard", edgeDirectionMap("guard"))
              }
            }
            case "clauseArgument" => {
              //addBinaryEdge(from, to, "data",edgeDirectionMap("data"))
              astEndNodeType match {
                case "clauseHead" => {
                  fromNodeLabel match {
                    case "constant" => addBinaryEdge(to, from, "dataConstant", edgeDirectionMap("dataConstant"))
                    case "operator" => addBinaryEdge(to, from, "dataOperator", edgeDirectionMap("dataOperator"))
                    case "symbolicConstant" => addBinaryEdge(to, from, "dataSc", edgeDirectionMap("dataSc"))
                    case _ => addBinaryEdge(to, from, "data", edgeDirectionMap("data"))
                  }
                }
                case "clauseBody" => {
                  fromNodeLabel match {
                    case "constant" => addBinaryEdge(from, to, "dataConstant", edgeDirectionMap("dataConstant"))
                    case "operator" => addBinaryEdge(from, to, "dataOperator", edgeDirectionMap("dataOperator"))
                    case "symbolicConstant" => addBinaryEdge(from, to, "dataSc", edgeDirectionMap("dataSc"))
                    case _ => addBinaryEdge(from, to, "data", edgeDirectionMap("data"))
                  }
                }
              }
            }
            case _ => {
              astEdgeType match {
                case "templateAST" => {
                  addBinaryEdge(from, to, "templateAST", edgeDirectionMap("templateAST"))
                }
                case _ => {
                  fromNodeLabel match {
                    case "constant" => addBinaryEdge(from, to, "subTermConstantOperator", edgeDirectionMap("subTermConstantOperator"))
                    case "operator" => addBinaryEdge(from, to, "subTermOperatorOperator", edgeDirectionMap("subTermOperatorOperator"))
                    case "symbolicConstant" => addBinaryEdge(from, to, "subTermScOperator", edgeDirectionMap("subTermScOperator"))
                    case _ => addBinaryEdge(from, to, "subTerm", edgeDirectionMap("subTerm"))
                  }
                }
              }
            }
          }
        }
        case _ => { //mono, hybrid layer graph
          val toNodeClass = to.substring(0, to.indexOf("_"))
          toNodeClass match {
            case "clause" => addBinaryEdge(from, to, "guard", edgeDirectionMap("guard"))
            case "clauseArgument" => {
              //addBinaryEdge(from, to, "data",edgeDirectionMap("data"))
              astEndNodeType match {
                case "clauseHead" => addBinaryEdge(to, from, "data", edgeDirectionMap("data"))
                case "clauseBody" => addBinaryEdge(from, to, "data", edgeDirectionMap("data"))
              }
            }
            case _ => {
              astEdgeType match {
                case "templateAST" => {
                  addBinaryEdge(from, to, "templateAST", edgeDirectionMap("templateAST"))
                }
                case _ => {
                  addBinaryEdge(from, to, "subTerm", edgeDirectionMap("subTerm"))
                }
              }
            }
          }
        }
      }
    }
  }

  def drawASTBinaryRelation(op: String, previousNodeName: String, e1: IExpression, e2: IExpression,astArity:String=""): String = {
    val e1Peek = peekAST(e1)
    val e2Peek = peekAST(e2)
    val existedNodeName = for ((k, v) <- binaryOperatorSubGraphSetInOneClause; if v._1 == e1Peek && v._2 == e2Peek && k.substring(0,k.indexOf("_"))==op) yield k
    val condName = if (existedNodeName.isEmpty) {
      val operatorNodeName=op + "_" + gnn_input.GNNNodeID
      createNode(operatorNodeName, op, "operator", nodeShapeMap("operator"))
      astEdgeType="AST_1"
      val e1Name=drawAST(e1, operatorNodeName,"AST_1")
      astEdgeType="AST_2"
      val e2Name=drawAST(e2, operatorNodeName,"AST_2")
      //remember sub-graph
      binaryOperatorSubGraphSetInOneClause(operatorNodeName)=Tuple2(e1Name,e2Name)//condName->Tuple2(e1Name,e2Name)
      operatorNodeName
    } else {existedNodeName.head}
    astEdgeType=astArity
    if (previousNodeName != "") addEdgeInSubTerm(condName, previousNodeName, "operator")
    condName
  }

  def drawASTUnaryRelation(op: String, previousNodeName: String, e: IExpression,astArity:String="AST_1"): String = {
    val ePeek = peekAST(e)
    val existedNodeName = for ((k, v) <- unaryOperatorSubGraphSetInOneClause; if v == ePeek && k.substring(0,k.indexOf("_"))==op) yield k
    astEdgeType="AST_1"
    val opName = if (existedNodeName.isEmpty) {
      val operatorNodeName = op + "_" + gnn_input.GNNNodeID
      createNode(operatorNodeName, op, "operator", nodeShapeMap("operator"))
      val eName=drawAST(e, operatorNodeName,"AST_1")
      unaryOperatorSubGraphSetInOneClause(operatorNodeName)=eName
      operatorNodeName
    } else {existedNodeName.head}
    if (previousNodeName != "") addEdgeInSubTerm(opName, previousNodeName,"operator")
    opName
  }

  def drawASTEndNode(constantStr: String, previousNodeName: String, className: String,draw:Boolean=true): String = {
    if (argumentNodeSetInPredicates.isEmpty){ //not drawing templates
      drawAndMergeConstantNode(constantStr,previousNodeName,className,draw)
    }else{ //when create template nodes, argumentNodeSetInPredicates store argument node name
      if(argumentNodeSetInPredicates.keySet.contains(constantStr)){//if this node is a argument, merge argument
        if (draw==true)
          addEdgeInSubTerm(argumentNodeSetInPredicates(constantStr), previousNodeName,className)
        argumentNodeSetInPredicates(constantStr)
      }else{//if this node is a constant, treat with regular constant. constantNodeSetInOneClause range in one predicate
        drawAndMergeConstantNode(constantStr,previousNodeName,className,draw)
      }
    }
  }

  def drawAndMergeConstantNode(constantStr:String,previousNodeName:String,className:String,draw:Boolean=true): String = {
    if (constantNodeSetCrossGraph.keySet.contains(constantStr)){ //if a constant is a global constant
      if (draw==true)
        addEdgeInSubTerm(constantNodeSetCrossGraph(constantStr), previousNodeName,className)
      constantNodeSetCrossGraph(constantStr)
    } else if (constantNodeSetInOneClause.keySet.contains(constantStr)) { //if a constant is a local clause constant
      if (draw==true)
        addEdgeInSubTerm(constantNodeSetInOneClause(constantStr), previousNodeName,className)
      constantNodeSetInOneClause(constantStr)
    } else {
      val constantName =
      if (draw==true){
        val constantNodeName=constantStr + "_" + gnn_input.GNNNodeID
        createNode(constantNodeName, constantStr, className, nodeShapeMap(className))
        addEdgeInSubTerm(constantNodeName, previousNodeName,className)
        //constantNodeSetInOneClause(constantStr) = constantNodeName
        className match {
          case "constant" => constantNodeSetCrossGraph(constantStr) = constantNodeName
          case _ => constantNodeSetInOneClause(constantStr) = constantNodeName
        }
        constantNodeName
      } else ""
      constantName
    }
  }

  def createNode(canonicalName: String, labelName: String, className: String, shape: String, clauseLabelInfo:Clauses=Seq(),hintLabel:Boolean=false): Unit = {
    writerGraph.write(addQuotes(canonicalName) +
      " [label=" + addQuotes(labelName) + " nodeName=" + addQuotes(canonicalName) + " class=" + className + " shape=" + addQuotes(shape) + "];" + "\n")
    className match {
      case "predicateArgument" => gnn_input.incrementArgumentIndicesAndNodeIds(canonicalName, className, labelName)
      case "CONTROL" => gnn_input.incrementControlLocationIndicesAndNodeIds(canonicalName, className, labelName)
      case "predicateName" => gnn_input.incrementPredicateIndicesAndNodeIds(canonicalName, className, labelName)
      case "FALSE" => gnn_input.incrementFalseIndicesAndNodeIds(canonicalName, className, labelName)
      case "template"=>gnn_input.incrementTemplateIndicesAndNodeIds(canonicalName, className, labelName,hintLabel)
      case "clause"=> gnn_input.incrementClauseIndicesAndNodeIds(canonicalName, className, labelName,clauseLabelInfo)
      case _ => gnn_input.incrementNodeIds(canonicalName, className, labelName)
    }
  }

  def createHyperEdgeNode(canonicalName: String, labelName: String, className: String, shape: String): Unit = {
    writerGraph.write(addQuotes(canonicalName) +
      " [label=" + addQuotes(labelName) + " nodeName=" + addQuotes(canonicalName) + " class=" + className + " shape=" + addQuotes(shape) + "];" + "\n")
    className match {
      case "controlFlowHyperEdge" => gnn_input.controlFlowHyperEdgeCanonicalID += 1
      case "dataFlowHyperEdge" => gnn_input.dataFlowHyperEdgeCanonicalID += 1
    }
  }
  def createConcretinizedHyperEdgeNode(canonicalName: String, labelName: String, className: String, shape: String): Unit = {
    createNode(canonicalName,labelName,className,shape)
    className match {
      case "controlFlowHyperEdge" => gnn_input.controlFlowHyperEdgeCanonicalID += 1
      case "dataFlowHyperEdge" => gnn_input.dataFlowHyperEdgeCanonicalID += 1
    }
  }

  def peekAST(e: IExpression):String=
    e match {
      case IBoolLit(v) =>  drawASTEndNode(v.toString(), "", "constant",draw = false)
      case IConstant(c) => drawASTEndNode(c.name, "", "symbolicConstant",draw = false)
      case IIntLit(v) => drawASTEndNode(v.toString(), "", "constant",draw = false)
      case Const(t) => drawASTEndNode(t.toString(), "", "constant",draw = false)
      case IVariable(index) => drawASTEndNode("_"+index.toString(), "", "symbolicConstant",draw = false)
      case _ => "other than single node"
    }

  def drawAST(e: IExpression, previousNodeName: String = "",astArity:String="AST_1"): String = {
    val rootName = e match {
      case Eq(t1, t2) => drawASTBinaryRelation("=", previousNodeName, t1, t2,astArity)
      case EqLit(term, lit) => drawASTBinaryRelation("=", previousNodeName, term, lit,astArity)
      case EqZ(t) =>  drawASTUnaryRelation("=0", previousNodeName, t,astArity)//drawASTBinaryRelation("=", previousNodeName, t, IdealInt.ZERO)


      case Geq(t1, t2) => drawASTBinaryRelation(">=", previousNodeName, t1, t2,astArity)
      case GeqZ(t) => drawASTUnaryRelation(">=0", previousNodeName, t,astArity)//drawASTBinaryRelation(">=", previousNodeName, t, IdealInt.ZERO)


      case Conj(a, b) => drawASTBinaryRelation("&", previousNodeName, a, b,astArity)
      case Disj(a, b) => drawASTBinaryRelation("|", previousNodeName, a, b,astArity)
      //case SignConst(t)=>{println("SignConst")}
      //case SimpleTerm(t)=>{println("SimpleTerm")}
      //      case LeafFormula(t)=>{
      //        //println("LeafFormula")
      //        drawAST(t,previousNodeName)
      //      }
      case IBinFormula(j, f1, f2) => drawASTBinaryRelation(j.toString, previousNodeName, f1, f2)
      case IFormulaITE(cond, left, right) => {
        drawAST(cond, previousNodeName)
        drawAST(right, previousNodeName)
        drawAST(left, previousNodeName)
      }
      case INot(subformula) =>  drawASTUnaryRelation("!", previousNodeName, subformula,astArity)
      case IQuantified(quan, subformula) =>  drawASTUnaryRelation(quan.toString, previousNodeName, subformula,astArity)
      case IEpsilon(cond) => drawASTUnaryRelation("eps", previousNodeName, cond,astArity)
      case IConstant(c) => drawASTEndNode(c.name, previousNodeName, "symbolicConstant")
      case IBoolLit(v) =>  drawASTEndNode(v.toString(), previousNodeName, "constant")
      case IIntLit(v) => drawASTEndNode(v.toString(), previousNodeName, "constant")
      case Const(t) => drawASTEndNode(t.toString(), previousNodeName, "constant")
      case IPlus(t1, t2) =>  drawASTBinaryRelation("+", previousNodeName, t1, t2,astArity)
      case IIntFormula(rel, term) => drawASTUnaryRelation(rel.toString, previousNodeName, term,astArity)
      case ITermITE(cond, left, right) => {
        drawAST(cond, previousNodeName)
        drawAST(right, previousNodeName)
        drawAST(left, previousNodeName)
      }
      case ITimes(coeff, subterm) => drawASTBinaryRelation("*", previousNodeName, subterm, coeff,astArity)
      case IVariable(index) => drawASTEndNode("_"+index.toString(), previousNodeName, "symbolicConstant")//constant////add _ to differentiate index with other constants
      case Difference(t1, t2) => drawASTBinaryRelation("-", previousNodeName, t1, t2,astArity)
      case INamedPart(pname, subformula) => drawASTUnaryRelation(pname.toString, previousNodeName, subformula,astArity)
      case IFunApp(fun, args) => {""}
      case ITrigger(patterns, subformula) => {""}
      case IAtom(pred, args) => {""}
      case _ => drawASTEndNode("unknown", previousNodeName, "constant")

    }
    rootName
  }

  def writeGNNInputToJSONFile(argumentIDList: ArrayBuffer[Int], argumentNameList: ArrayBuffer[String],
                              argumentOccurrenceList: ArrayBuffer[Int],argumentBoundList:ArrayBuffer[(String, String)],argumentIndicesList:ArrayBuffer[Int],argumentBinaryOccurrenceList:ArrayBuffer[Int]): Unit = {
    println("Write GNNInput to file")
    var lastFiledFlag = false
    val writer = new PrintWriter(new File(file + "." + graphType + ".JSON"))
    writer.write("{\n")
    writeGNNInputFieldToJSONFile("nodeIds", IntArray(gnn_input.nodeIds), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("nodeSymbolList", StringArray(gnn_input.nodeSymbols), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("falseIndices", IntArray(gnn_input.falseIndices), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("argumentIndices", IntArray(argumentIndicesList.toArray), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("argumentBoundList", PairStringArray(argumentBoundList.toArray), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("argumentBinaryOccurrenceList", IntArray(argumentBinaryOccurrenceList.toArray), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("argumentOccurrence", IntArray(argumentOccurrenceList.toArray), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("templateIndices", IntArray(gnn_input.templateIndices), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("templateRelevanceLabel", IntArray(gnn_input.templateRelevanceLabel), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("clauseIndices", IntArray(gnn_input.clauseIndices), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("clauseBinaryOccurrenceInCounterExampleList", IntArray(gnn_input.clausesOccurrenceInCounterExample), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("controlLocationIndices", IntArray(gnn_input.controlLocationIndices), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("binaryAdjacentList", PairArray(gnn_input.binaryAdjacency.binaryEdge.sorted), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("ternaryAdjacencyList", TripleArray(gnn_input.ternaryAdjacency.ternaryEdge), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("unknownEdges", PairArray(gnn_input.unknownEdges.binaryEdge), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("argumentIDList", IntArray(argumentIDList.toArray), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("argumentNameList", StringArray(argumentNameList.toArray), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("predicateIndices", IntArray(gnn_input.predicateIndices), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("predicateOccurrenceInClause", IntArray(gnn_input.predicateOccurrenceInClause), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("predicateStrongConnectedComponent", IntArray(gnn_input.predicateStrongConnectedComponent), writer, lastFiledFlag)
    GlobalParameters.get.hornGraphType match {
      case DrawHornGraph.HornGraphType.hyperEdgeGraph=> {
        writeGNNInputFieldToJSONFile("argumentEdges", PairArray(gnn_input.argumentEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("guardASTEdges", PairArray(gnn_input.guardASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("ASTEdges", PairArray(gnn_input.ASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("AST_1Edges", PairArray(gnn_input.AST_1Edges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("AST_2Edges", PairArray(gnn_input.AST_2Edges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("templateASTEdges", PairArray(gnn_input.templateASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("templateEdges", PairArray(gnn_input.templateEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("dataFlowASTEdges", PairArray(gnn_input.dataFlowASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("controlFlowHyperEdges", TripleArray(gnn_input.controlFlowHyperEdges.ternaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("dataFlowHyperEdges", TripleArray(gnn_input.dataFlowHyperEdges.ternaryEdge), writer, lastFiledFlag)
      }
      case DrawHornGraph.HornGraphType.equivalentHyperedgeGraph| DrawHornGraph.HornGraphType.concretizedHyperedgeGraph=>{
        writeGNNInputFieldToJSONFile("argumentEdges", PairArray(gnn_input.argumentEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("guardASTEdges", PairArray(gnn_input.guardASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("ASTEdges", PairArray(gnn_input.ASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("AST_1Edges", PairArray(gnn_input.AST_1Edges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("AST_2Edges", PairArray(gnn_input.AST_2Edges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("templateASTEdges", PairArray(gnn_input.templateASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("templateEdges", PairArray(gnn_input.templateEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("dataFlowASTEdges", PairArray(gnn_input.dataFlowASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("controlFlowHyperEdges", PairArray(gnn_input.controlFlowHyperEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("dataFlowHyperEdges", PairArray(gnn_input.dataFlowHyperEdges.binaryEdge), writer, lastFiledFlag)
      }
      case _ => {
        writeGNNInputFieldToJSONFile("predicateArgumentEdges", PairArray(gnn_input.predicateArgumentEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("predicateInstanceEdges", PairArray(gnn_input.predicateInstanceEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("argumentInstanceEdges", PairArray(gnn_input.argumentInstanceEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("controlHeadEdges", PairArray(gnn_input.controlHeadEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("controlBodyEdges", PairArray(gnn_input.controlBodyEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("controlEdges", PairArray(gnn_input.controlEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("controlArgumentEdges", PairArray(gnn_input.controlArgumentEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("subTermEdges", PairArray(gnn_input.subTermEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("guardEdges", PairArray(gnn_input.guardEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("dataEdges", PairArray(gnn_input.dataEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("predicateInstanceHeadEdges", PairArray(gnn_input.predicateInstanceHeadEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("predicateInstanceBodyEdges", PairArray(gnn_input.predicateInstanceBodyEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("controlArgumentHeadEdges", PairArray(gnn_input.controlArgumentHeadEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("controlArgumentBodyEdges", PairArray(gnn_input.controlArgumentBodyEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("guardConstantEdges", PairArray(gnn_input.guardConstantEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("guardOperatorEdges", PairArray(gnn_input.guardOperatorEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("guardScEdges", PairArray(gnn_input.guardScEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("dataConstantEdges", PairArray(gnn_input.dataConstantEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("dataOperatorEdges", PairArray(gnn_input.dataOperatorEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("dataScEdges", PairArray(gnn_input.dataScEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("subTermConstantOperatorEdges", PairArray(gnn_input.subTermConstantOperatorEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("subTermOperatorOperatorEdges", PairArray(gnn_input.subTermOperatorOperatorEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("subTermScOperatorEdges", PairArray(gnn_input.subTermScOperatorEdges.binaryEdge), writer, lastFiledFlag)
      }
    }
    lastFiledFlag = true
    writeGNNInputFieldToJSONFile("dummyFiled", IntArray(Array[Int]()), writer, lastFiledFlag)
    writer.write("}")
    writer.close()
  }

  def matchArguments(): (ArrayBuffer[Int], ArrayBuffer[String], ArrayBuffer[Int], ArrayBuffer[(String, String)],ArrayBuffer[Int],ArrayBuffer[Int]) = {
    //match by argument name
    for (argHornGraph <- gnn_input.argumentInfoHornGraphList; arg <- argumentInfoList) {
      if (arg.headName == argHornGraph.head && arg.index == argHornGraph.index) {
        argHornGraph.score = arg.score
        argHornGraph.ID = arg.ID
        argHornGraph.bound=arg.bound
        argHornGraph.binaryOccurrenceInTemplates=arg.binaryOccurenceLabel
      }
    }
    val argumentIDList = for (argHornGraph <- gnn_input.argumentInfoHornGraphList; if argHornGraph.bound._1!="\"False\"") yield argHornGraph.ID
    val argumentIndicesList = for (argHornGraph <- gnn_input.argumentInfoHornGraphList; if argHornGraph.bound._1!="\"False\"") yield argHornGraph.globalIndexInGraph
    val argumentNameList = for (argHornGraph <- gnn_input.argumentInfoHornGraphList if argHornGraph.bound._1!="\"False\"") yield argHornGraph.head + ":" + argHornGraph.name
    val argumentOccurrenceList = for (argHornGraph <- gnn_input.argumentInfoHornGraphList if argHornGraph.bound._1!="\"False\"") yield argHornGraph.score
    val argumentBinaryOccurrenceList = for (argHornGraph <- gnn_input.argumentInfoHornGraphList if argHornGraph.bound._1!="\"False\"") yield argHornGraph.binaryOccurrenceInTemplates
    val argumentBoundList = for (argHornGraph <- gnn_input.argumentInfoHornGraphList if argHornGraph.bound._1!="\"False\"") yield argHornGraph.bound
    (argumentIDList, argumentNameList, argumentOccurrenceList,argumentBoundList,argumentIndicesList,argumentBinaryOccurrenceList)
  }

  def writeGNNInputFieldToJSONFile(fieldName: String, fiedlContent: Arrays, writer: PrintWriter, lastFiledFlag: Boolean): Unit = {
    fiedlContent match {
      case StringArray(x) => writeOneField(fieldName, x, writer)
      case IntArray(x) => writeOneField(fieldName, x, writer)
      case PairArray(x) => writeOneField(fieldName, x, writer)
      case TripleArray(x) => writeOneField(fieldName, x, writer)
      case PairStringArray(x)=> writePairStringArrayField(fieldName, x, writer)
    }
    if (lastFiledFlag == false)
      writer.write(",\n")
    else
      writer.write("\n")
  }

  sealed abstract class Arrays

  case class StringArray(x: Array[String]) extends Arrays

  case class IntArray(x: Array[Int]) extends Arrays

  case class PairArray(x: Array[Pair[Int, Int]]) extends Arrays
  case class PairStringArray(x: Array[Pair[String, String]]) extends Arrays

  case class TripleArray(x: Array[Triple[Int, Int, Int]]) extends Arrays

  def writeOneField(fieldName: String, fiedlContent: Array[Pair[Int, Int]], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write("[")
      writer.write(p._1.toString)
      writer.write(",")
      writer.write(p._2.toString)
      writer.write("]")
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }
  def writePairStringArrayField(fieldName: String, fiedlContent: Array[Pair[String, String]], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write("[")
      writer.write(p._1)
      writer.write(",")
      writer.write(p._2)
      writer.write("]")
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }

  def writeOneField(fieldName: String, fiedlContent: Array[Triple[Int, Int, Int]], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write("[")
      writer.write(p._1.toString)
      writer.write(",")
      writer.write(p._2.toString)
      writer.write(",")
      writer.write(p._3.toString)
      writer.write("]")
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }

  def writeOneField(fieldName: String, fiedlContent: Array[Int], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write(p.toString)
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }

  def writeOneField(fieldName: String, fiedlContent: Array[String], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write(addQuotes(p.toString))
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }
  def drawTemplates(clauseGuardMap: Map[Predicate, Seq[Tuple2[String,IFormula]]]=Map()): Seq[(String,Seq[String])] ={
    val quantifiedClauseGuardMap = {
      for ((k, v) <- clauseGuardMap) yield k -> {
        for (p <- v) yield Tuple2(p._1,HintsSelection.predicateQuantify(p._2))
      }.filter(!_._2.isTrue).filter(!_._2.isFalse)
    }

    val tempHeadMap=
    for((hp,templates)<-hints.initialHints.toInitialPredicates.toSeq.sortBy(_._1.name)) yield {
      constantNodeSetInOneClause.clear()
      val templateNameList=
      for (t<-templates) yield {
        val templateNodeName=templateNodePrefix+gnn_input.templateCanonicalID.toString
        val templateNodeLabelName="predicate_"+gnn_input.templateCanonicalID.toString
        //templateNameList:+=templateNodeName
        val hintLabel = if (hints.positiveHints.toInitialPredicates.keySet.map(_.toString).contains(hp.toString) && HintsSelection.wrappedContainsPred(t,hints.positiveHints.toInitialPredicates(hp))) true else false
        createNode(templateNodeName,templateNodeLabelName,"template",nodeShapeMap("template"),hintLabel=hintLabel)
        //drawAST(e,templateNodeName)
        val existedSubGraphRoot = for ((s, f) <- quantifiedClauseGuardMap(hp) if (HintsSelection.wrappedContainsPred(t, Seq(f)))) yield s
        if (existedSubGraphRoot.isEmpty) {
          val predicateASTRootName=drawAST(t)
          addBinaryEdge(predicateASTRootName,templateNodeName,"templateAST")
        } else
          addBinaryEdge(existedSubGraphRoot.head,templateNodeName,"templateAST")//astEdgeType
        templateNodeName
      }
      hp.name->templateNameList
    }
    tempHeadMap
  }

  def drawPredicate(): Seq[(String,Seq[String])] ={
    val tempHeadMap=
      for((hp,templates)<-hints.initialHints.toInitialPredicates.toSeq.sortBy(_._1.name)) yield {
        constantNodeSetInOneClause.clear()
        val templateNameList=
          for (t<-templates) yield {
            val predicateASTRootName=drawAST(t)
            //update JSON
            val hintLabel = if (hints.positiveHints.toInitialPredicates.keySet.map(_.toString).contains(hp.toString) && HintsSelection.wrappedContainsPred(t,hints.positiveHints.toInitialPredicates(hp))) true else false
            gnn_input.updateTemplateIndicesAndNodeIds(predicateASTRootName,hintLabel)
            predicateASTRootName
          }
        hp.name->templateNameList
      }
    tempHeadMap
  }

  def updateArgumentInfoHornGraphList(pre:String,tempID:Int,argumentnodeName:String,arg:ITerm): Unit ={
    val localArgInfo=new argumentInfoHronGraph(pre, tempID,gnn_input.GNNNodeID-1)
    localArgInfo.canonicalName=argumentnodeName
    localArgInfo.constNames:+=arg.toString
    gnn_input.argumentInfoHornGraphList += localArgInfo
  }

}



