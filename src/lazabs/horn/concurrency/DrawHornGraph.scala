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
import ap.parser.IExpression._
import ap.parser.{IExpression, _}
import lazabs.GlobalParameters
import lazabs.horn.abstractions.{TemplateType, TemplateTypeUsefulNess}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import lazabs.horn.concurrency.DrawHornGraph.{HornGraphType, addQuotes, isNumeric}
import lazabs.horn.concurrency.HintsSelection.{detectIfAJSONFieldExists, getParametersFromVerifHintElement, replaceMultiSamePredicateInBody, spAPI}
import play.api.libs.json.{JsSuccess, Json}

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
case class NodeInfo(canonicalName:String,labelName:String,className:String,shape:String,_fillColor:String="while"){
  var labelList:Seq[Int]=Seq()
  var predictedLabelList:Seq[Int]=Seq()
  var color="black"
  var fillColor=_fillColor
}

class GNNInput(simpClauses:Clauses,clausesInCE:Clauses) {
  var GNNNodeID = 0
  var hyperEdgeNodeID = 0
  var TotalNodeID = 0
  //canonical node category for hyperedge horn graph
  var CONTROLCanonicalID, argumentCanonicalID, predicateCanonicalID, iEpsilonCanonicalID, iFormulaITECanonicalID, iFunAppCanonicalID,
  iNamePartCanonicalID, iTermITECanonicalID, iTriggerCanonicalID, variableCanonicalID, symbolicConstantCanonicalID,
  controlFlowHyperEdgeCanonicalID, dataFlowHyperEdgeCanonicalID,guardCanonicalID = 0

  //canonical node category for layer horn graph
  var clauseHeadCanonicalID, clauseBodyCanonicalID, clauseArgCanonicalID, clauseCanonicalID, predicateNameCanonicalID,
  predicateArgumentCanonicalID, operatorUniqueID, constantUniqueID = 0

  //canonical node category for both graph
  var templateCanonicalID=0
  var nodeInfoList=Map[String,NodeInfo]()
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
  val verifHintTplPredEdges = new Adjacency("verifHintTplPredEdges", 2)
  val verifHintTplPredPosNegEdges = new Adjacency("verifHintTplPredPosNegEdges", 2)
  val verifHintTplEqTermEdges =new Adjacency("verifHintTplEqTermEdges", 2)
  val verifHintTplInEqTermEdges = new Adjacency("verifHintTplInEqTermEdges", 2)
  val verifHintTplInEqTermPosNegEdges = new Adjacency("verifHintTplInEqTermPosNegEdges", 2)
  //val dataFlowEdges = new Adjacency("dataFlowEdge", 2)
  val argumentEdges = new Adjacency("argumentEdge", 2)
  val controlFlowHyperEdges = new Adjacency("controlFlowHyperEdge", 3)
  val dataFlowHyperEdges = new Adjacency("dataFlowHyperEdge", 3)
  val clauseEdges = new Adjacency("clauseEdge", 2)
  val controlLocationEdgeForSCC = new Adjacency("controlLocationEdgeForSCC", 2)

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
  val predicateTransitiveEdges = new Adjacency("transitive", 2)

  var controlLocationIndices = Array[Int]()
  var falseIndices = Array[Int]()
  var initialIndices = Array[Int]()
  var argumentIndices = Array[Int]()
  var guardIndices = Array[Int]()
  var templateIndices = Array[Int]()
  var templateRelevanceLabel = Array[Int]()
  var templateCostLabel = Array[Int]()
  var clauseIndices = Array[Int]()
  var predicateIndices = Array[Int]()
  var predicateOccurrenceInClause = Array[Int]()
  var clausesOccurrenceInCounterExample = Array[Int]()
  var predicateStrongConnectedComponent = Array[Int]()
  var argumentInfoHornGraphList = new ArrayBuffer[argumentInfoHronGraph]
  var nodeNameToIDMap = MuMap[String, Int]()

  val learningLabel= new FormLearningLabels(simpClauses,clausesInCE)
  val predicateOccurrenceInClauseLabel=learningLabel.getPredicateOccurenceInClauses()
  val (predicateStrongConnectedComponentLabel,transitiveEdgeList)=learningLabel.getStrongConnectedComponentPredicateList()
  def incrementTemplates(element:String,fromID:Int,toID:Int): Unit ={
    element match {
      case "verifHintTplPred"=>verifHintTplPredEdges.incrementBinaryEdge(fromID, toID)
      case "verifHintTplPredPosNeg" =>verifHintTplPredPosNegEdges.incrementBinaryEdge(fromID, toID)
      case "verifHintTplEqTerm" => verifHintTplEqTermEdges.incrementBinaryEdge(fromID, toID)
      case "verifHintTplInEqTerm" => verifHintTplInEqTermEdges.incrementBinaryEdge(fromID, toID)
      case "verifHintTplInEqTermPosNeg" => verifHintTplInEqTermPosNegEdges.incrementBinaryEdge(fromID, toID)
      case _ =>
    }
    templateEdges.incrementBinaryEdge(fromID, toID)
  }
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
          case "verifHintTplPred" => incrementTemplates("verifHintTplPred",fromID, toID)
          case "verifHintTplPredPosNeg" => incrementTemplates("verifHintTplPredPosNeg",fromID, toID)
          case "verifHintTplEqTerm" => incrementTemplates("verifHintTplEqTerm",fromID, toID)
          case "verifHintTplInEqTerm" => incrementTemplates("verifHintTplInEqTerm",fromID, toID)
          case "verifHintTplInEqTermPosNeg" => incrementTemplates("verifHintTplInEqTermPosNeg",fromID, toID)
          case "argument" => argumentEdges.incrementBinaryEdge(fromID, toID)
          case "clause" => clauseEdges.incrementBinaryEdge(fromID,toID)
          case "controlFlowHyperEdge"=> controlFlowHyperEdges.incrementBinaryEdge(fromID,toID)
          case "dataFlowHyperEdge" => dataFlowHyperEdges.incrementBinaryEdge(fromID,toID)
          case "controlLocationEdgeForSCC" => controlLocationEdgeForSCC.incrementBinaryEdge(fromID,toID)
          case "transitive" => predicateTransitiveEdges.incrementBinaryEdge(fromID,toID)
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
  def incrementInitialIndicesAndNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String): Unit = {
    initialIndices :+= GNNNodeID
    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
  }

  def incrementArgumentIndicesAndNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String): Unit = {
    argumentIndices :+= GNNNodeID
    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
  }

  def modifyTemplateLabel(hintLabel: Int, cost: Int, nodeUniqueName: String): Unit = {
    hintLabel match {
      case 0 => nodeInfoList(nodeUniqueName).color = "red"
      case 1 => nodeInfoList(nodeUniqueName).color = "green"
      case 2 => nodeInfoList(nodeUniqueName).color = "blue"
      case 3 => nodeInfoList(nodeUniqueName).color = "yellow"
      case 4 => nodeInfoList(nodeUniqueName).color = "black"
    }
    nodeInfoList(nodeUniqueName).labelList :+= hintLabel
    templateRelevanceLabel :+= hintLabel
    templateCostLabel :+= cost
  }
  def incrementTemplateIndicesAndNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String,hintLabel:Int,cost:Int=0): Unit = {
    templateIndices :+= GNNNodeID
    modifyTemplateLabel(hintLabel,cost,nodeUniqueName)
    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
  }
  def updateTemplateIndicesAndNodeIds(nodeUniqueName:String,hintLabel:Int,cost:Int=0): Unit ={ //use operator node as template node
    templateIndices :+= nodeNameToIDMap(nodeUniqueName)
    modifyTemplateLabel(hintLabel,cost,nodeUniqueName)
    templateCanonicalID += 1
  }
  def incrementGuardIndicesAndNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String,clauseInfo:Clauses): Unit ={
    guardIndices :+=GNNNodeID
    if (!clauseInfo.isEmpty && clausesInCE.map(_.toString).contains(clauseInfo.head.toString)) {
      clausesOccurrenceInCounterExample :+=1
    } else
      clausesOccurrenceInCounterExample :+=0
    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
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
    //println("predicateOccurrenceInClauseLabel",predicateOccurrenceInClauseLabel)
    for (l<-predicateOccurrenceInClauseLabel) if (l._1==nodeName) {
      predicateIndices :+= GNNNodeID
      predicateOccurrenceInClause :+= l._2
      predicateStrongConnectedComponent:+=predicateStrongConnectedComponentLabel(nodeName)
    }

    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
  }

  def incrementPredicateIndicesAndNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String): Unit = {
    for (l<-predicateOccurrenceInClauseLabel) if (l._1==nodeName) {
      predicateIndices :+= GNNNodeID
      predicateOccurrenceInClause :+= l._2
      predicateStrongConnectedComponent:+=predicateStrongConnectedComponentLabel(nodeName)
    }
    incrementNodeIds(nodeUniqueName, nodeClass, nodeName)
  }

  def incrementNodeIds(nodeUniqueName: String, nodeClass: String, nodeName: String): Unit = {
    //check if total node number larger than max_node
    if(nodeIds.size>GlobalParameters.get.maxNode){
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/exceed-max-node/" + GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/"),GlobalParameters.get.fileName.length),message = "node number >= maxNode" )
      //HintsSelection.removeRelativeFiles(GlobalParameters.get.fileName)
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
      case "guard" => {
        nodeSymbols :+= nodeClass + "_" + guardCanonicalID.toString
        guardCanonicalID += 1
      }
      case "controlFlowHyperEdge"=>
        nodeSymbols :+= nodeClass + "_" + controlFlowHyperEdgeCanonicalID.toString
      case "dataFlowHyperEdge"=>
        nodeSymbols :+= nodeClass + "_" + dataFlowHyperEdgeCanonicalID.toString
      case "Initial" => nodeSymbols :+= nodeName
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
  val simpClauses= clausesCollection.simplifiedClause
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
  val constantNodeSetInOneClause = scala.collection.mutable.Map[String, String]() //map[constantName->constantNameWithCanonicalNumber]
  val controlFlowNodeSetCrossGraph = scala.collection.mutable.Map[String, String]()// predicate.name -> canonical name
  val argumentNodeSetCrossGraph = scala.collection.mutable.Map[String, Array[(String,String)]]() //predicateName:String -> arguments Array[String]
  val argumentNodeSetInPredicates = scala.collection.mutable.Map[String, String]() //map[argumentConstantName->argumentNameWithCanonicalNumber]
  val constantNodeSetCrossGraph = scala.collection.mutable.Map[String, String]()
  var astEdgeType = ""
  var astEndNodeType=""
  val gnn_input = new GNNInput(simpClauses,clausesInCE)
  val writerGraph = new PrintWriter(new File(file + "." + graphType + ".gv"))

  edgeNameMap += ("templateAST"->"tplAST")
  edgeNameMap += ("template"->"predicate")
  edgeDirectionMap += ("templateAST"->false)
  edgeDirectionMap += ("template" -> false)
  nodeShapeMap += ("template" -> "component")

  //writerGraph.write("digraph dag { " +"graph [pad=\"1\", nodesep=\"0.5\", ranksep=\"1\"]; splines=\"true\";"+ "\n")
  writerGraph.write("digraph dag { " + "\n")

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
    val e1Peek = peekAST(e1,astArity="AST_1")
    val e2Peek = peekAST(e2,astArity="AST_2")
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
    val ePeek = peekAST(e,astArity=astArity)
    val existedNodeName = for ((k, v) <- unaryOperatorSubGraphSetInOneClause; if v == ePeek && k.substring(0,k.indexOf("_"))==op) yield k
    astEdgeType=astArity
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

  def createNode(canonicalName: String, labelName: String, className: String, shape: String, clauseLabelInfo:Clauses=Seq(),hintLabel:Int=0,nodeLabel:Int=0): Unit = {
    val NInfo= if(nodeLabel==1) new NodeInfo(canonicalName,labelName+":"+gnn_input.GNNNodeID.toString,className,shape,_fillColor = "green")
    else NodeInfo(canonicalName,labelName+":"+gnn_input.GNNNodeID.toString,className,shape,_fillColor = "white")
    gnn_input.nodeInfoList+=(canonicalName->NInfo)
//    writerGraph.write(addQuotes(canonicalName) +
//      " [label=" + addQuotes(labelName) + " nodeName=" + addQuotes(canonicalName) + " class=" + className + " shape=" + addQuotes(shape) + "];" + "\n")
    className match {
      case "predicateArgument" => gnn_input.incrementArgumentIndicesAndNodeIds(canonicalName, className, labelName)
      case "CONTROL" => gnn_input.incrementControlLocationIndicesAndNodeIds(canonicalName, className, labelName)
      case "predicateName" => gnn_input.incrementPredicateIndicesAndNodeIds(canonicalName, className, labelName)
      case "FALSE" => gnn_input.incrementFalseIndicesAndNodeIds(canonicalName, className, labelName)
      case "Initial" => gnn_input.incrementInitialIndicesAndNodeIds(canonicalName, className, labelName)
      case "template"=>gnn_input.incrementTemplateIndicesAndNodeIds(canonicalName, className, labelName,hintLabel)
      case "clause"=> gnn_input.incrementClauseIndicesAndNodeIds(canonicalName, className, labelName,clauseLabelInfo)
      case "guard"=> gnn_input.incrementGuardIndicesAndNodeIds(canonicalName, className, labelName,clauseLabelInfo)
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

  def peekAST(e: IExpression,astArity:String="AST_1"):String=
    e match {
      case IBoolLit(v) =>  drawASTEndNode(v.toString(), "", "constant",draw = false)
      case IConstant(c) => drawASTEndNode(c.name, "", "symbolicConstant",draw = false)
      case IIntLit(v) => drawASTEndNode(v.toString(), "", "constant",draw = false)
      case Const(t) => drawASTEndNode(t.toString(), "", "constant",draw = false)
      case IVariable(index) => drawASTEndNode("_"+index.toString(), "", "symbolicConstant",draw = false)
      //todo: check unary and binary drawing logic
      case _ => drawAST(e,astArity = astArity)//"other than single node"
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
      case ITimes(coeff, subterm) => {
        if(coeff.intValue == -1)
          drawASTUnaryRelation("-", previousNodeName, subterm,astArity)
        else if (coeff.intValue == 1)
          drawAST(subterm, previousNodeName,astArity)
        else
          drawASTBinaryRelation("*", previousNodeName, subterm, coeff,astArity)
      }
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
                              argumentOccurrenceList: ArrayBuffer[Int],argumentBoundList:ArrayBuffer[(String, String)],
                              argumentIndicesList:ArrayBuffer[Int],argumentBinaryOccurrenceList:ArrayBuffer[Int]): Unit = {
    println("Write GNNInput to file")
    var lastFiledFlag = false
    val writer = new PrintWriter(new File(file + "." + graphType + ".JSON"))
    writer.write("{\n")
    writeGNNInputFieldToJSONFile("nodeIds", IntArray(gnn_input.nodeIds), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("nodeSymbolList", StringArray(gnn_input.nodeSymbols), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("falseIndices", IntArray(gnn_input.falseIndices), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("initialIndices", IntArray(gnn_input.initialIndices), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("argumentIndices", IntArray(argumentIndicesList.toArray), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("argumentBoundList", PairStringArray(argumentBoundList.toArray), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("argumentBinaryOccurrenceList", IntArray(argumentBinaryOccurrenceList.toArray), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("argumentOccurrence", IntArray(argumentOccurrenceList.toArray), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("templateIndices", IntArray(gnn_input.templateIndices), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("templateRelevanceLabel", IntArray(gnn_input.templateRelevanceLabel), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("templateCostLabel", IntArray(gnn_input.templateCostLabel), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("clauseIndices", IntArray(gnn_input.clauseIndices), writer, lastFiledFlag)
    writeGNNInputFieldToJSONFile("guardIndices", IntArray(gnn_input.guardIndices), writer, lastFiledFlag)
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
//        if (gnn_input.AST_1Edges.binaryEdge.length==0 || gnn_input.AST_2Edges.binaryEdge.length==0){
//          println("gnn_input.AST_1Edges.binaryEdge",gnn_input.AST_1Edges.binaryEdge.length)
//        }
        writeGNNInputFieldToJSONFile("argumentEdges", PairArray(gnn_input.argumentEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("guardASTEdges", PairArray(gnn_input.guardASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("ASTEdges", PairArray(gnn_input.ASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("AST_1Edges", PairArray(gnn_input.AST_1Edges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("AST_2Edges", PairArray(gnn_input.AST_2Edges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("templateASTEdges", PairArray(gnn_input.templateASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("templateEdges", PairArray(gnn_input.templateEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("verifHintTplPredEdges", PairArray(gnn_input.verifHintTplPredEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("verifHintTplPredPosNegEdges", PairArray(gnn_input.verifHintTplPredPosNegEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("verifHintTplEqTermEdges", PairArray(gnn_input.verifHintTplEqTermEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("verifHintTplInEqTermEdges", PairArray(gnn_input.verifHintTplInEqTermEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("verifHintTplInEqTermPosNegEdges", PairArray(gnn_input.verifHintTplInEqTermPosNegEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("dataFlowASTEdges", PairArray(gnn_input.dataFlowASTEdges.binaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("controlFlowHyperEdges", TripleArray(gnn_input.controlFlowHyperEdges.ternaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("dataFlowHyperEdges", TripleArray(gnn_input.dataFlowHyperEdges.ternaryEdge), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("controlLocationEdgeForSCC", PairArray(gnn_input.controlLocationEdgeForSCC.binaryEdge.distinct), writer, lastFiledFlag)
        writeGNNInputFieldToJSONFile("predicateTransitiveEdges", PairArray(gnn_input.predicateTransitiveEdges.binaryEdge.distinct), writer, lastFiledFlag)
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
        writeGNNInputFieldToJSONFile("controlLocationEdgeForSCC", PairArray(gnn_input.controlLocationEdgeForSCC.binaryEdge.distinct), writer, lastFiledFlag)
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
  def drawPredicatesWithNode(clauseGuardMap: Map[Predicate, Seq[Tuple2[String,IFormula]]]=Map()): Seq[(String,Seq[String])] ={ //with template node
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
        val hintLabel = if (hints.positiveHints.toInitialPredicates.keySet.map(_.toString).contains(hp.toString) && HintsSelection.containsPred(t,hints.positiveHints.toInitialPredicates(hp))) 1 else 0
        createNode(templateNodeName,templateNodeLabelName,"template",nodeShapeMap("template"),hintLabel=hintLabel)
        //drawAST(e,templateNodeName)
        val existedSubGraphRoot = for ((s, f) <- quantifiedClauseGuardMap(hp) if (HintsSelection.containsPred(t, Seq(f)))) yield s
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

  def drawPredicate(): Seq[(String,Seq[(String,String)])] ={
    val tempHeadMap=
      for((hp,templates)<-hints.initialHints.toInitialPredicates.toSeq.sortBy(_._1.name)) yield {
        constantNodeSetInOneClause.clear()
        val templateNameList=
          for (t<-templates) yield {
            val predicateASTRootName=drawAST(t)
            //update JSON
            val hintLabel = if (hints.positiveHints.toInitialPredicates.keySet.map(_.toString).contains(hp.toString) && HintsSelection.containsPred(t,hints.positiveHints.toInitialPredicates(hp))) 1 else 0
            gnn_input.updateTemplateIndicesAndNodeIds(predicateASTRootName,hintLabel)
            (predicateASTRootName,"template")
          }
        hp.name->templateNameList
      }
    tempHeadMap
  }
  def transformBooleanPredicateToTerm(t: (IExpression, Int, TemplateType.Value)): (IExpression, Int, TemplateType.Value) =t._3 match {
    case TemplateType.TplEqTerm  => (t._1,t._2,t._3)
    case TemplateType.TplInEqTerm=> (t._1,t._2,t._3)
    case TemplateType.TplPredPosNeg=> t._1 match {
      case Eq(x,y)=>(x,t._2,TemplateType.TplPredPosNeg)
    }
  }


  def drawTemplates(): Seq[(String,Seq[(String,String)])]={
    val unlabeledTemplates = hints.initialHints.predicateHints.transform((k,v)=>v.map(getParametersFromVerifHintElement(_))).toSeq.sortBy(_._1.name)
    val positiveTemplates = hints.positiveHints.predicateHints.transform((k,v)=>v.map(getParametersFromVerifHintElement(_)))
    val predictedTemplates = hints.predictedHints.predicateHints.transform((k, v) => v.map(getParametersFromVerifHintElement(_)))

    val input_file=GlobalParameters.get.fileName+".hyperEdgeHornGraph.JSON"
    val predictedLabel=if(new java.io.File(input_file).exists&&detectIfAJSONFieldExists("predictedLabel",GlobalParameters.get.fileName)==true){
      val json_content = scala.io.Source.fromFile(input_file).mkString
      val json_data = Json.parse(json_content)
      val predictedLabel= (json_data \ "predictedLabel").validate[Array[Int]] match {
        case JsSuccess(templateLabel,_)=> templateLabel
      }
      predictedLabel
    }else Array()


    var counter=0
    val tempHeadMap=
      for((hp,templates)<-unlabeledTemplates) yield {
        argumentNodeSetInPredicates.clear()
        for (a<-argumentNodeSetCrossGraph(hp.name)){
          argumentNodeSetInPredicates(a._1)=a._2
        }
        constantNodeSetInOneClause.clear()
        binaryOperatorSubGraphSetInOneClause.clear()
        unaryOperatorSubGraphSetInOneClause.clear()
        val templateNameList=
          for (t<-templates) yield {
            //encode label to multi-class
            //val (hintLabel,cost) = getHintLabelAndCost(positiveTemplates,t,hp)
            val (hintLabel,cost) = encodeLabelToMultiClass(positiveTemplates,t,hp,templates)
            //draw boolean predicate as single term node
            val transfomedT=transformBooleanPredicateToTerm(t)
            val templateASTRootName=drawAST(transfomedT._1)
            //println(t,hintLabel,templateASTRootName)
            gnn_input.updateTemplateIndicesAndNodeIds(templateASTRootName,hintLabel,cost = cost)//update JSON
            //println(t._1,hintLabel)

            //read predicted label from JSON
            if (predictedLabel.isEmpty)
              gnn_input.nodeInfoList(templateASTRootName).predictedLabelList :+= 0
            else
              gnn_input.nodeInfoList(templateASTRootName).predictedLabelList :+= predictedLabel(counter)
            counter=counter+1

            (templateASTRootName,"verifHint"+t._3.toString)
          }
        hp.name->templateNameList
      }
    tempHeadMap
  }

  def drawTemplatesWithNode(): Seq[(String,Seq[(String,String)])]={
    val unlabeledTemplates = hints.initialHints.predicateHints.transform((k,v)=>v.map(getParametersFromVerifHintElement(_))).toSeq.sortBy(_._1.name)
    val positiveTemplates = hints.positiveHints.predicateHints.transform((k,v)=>v.map(getParametersFromVerifHintElement(_)))
    val predictedTemplates = hints.predictedHints.predicateHints.transform((k, v) => v.map(getParametersFromVerifHintElement(_)))
    val tempHeadMap=
      for((hp,templates)<-unlabeledTemplates) yield {
        constantNodeSetInOneClause.clear()
        val templateNameList=
          for (t<-templates) yield {
            val templateASTRootName=drawAST(t._1)
            val (hintLabel,cost) = getHintLabelAndCost(positiveTemplates,t,hp)


            val templateNodeName=templateNodePrefix+gnn_input.templateCanonicalID.toString
            val templateNodeLabelName="template_"+gnn_input.templateCanonicalID.toString
            createNode(templateNodeName,templateNodeLabelName,"template",nodeShapeMap("template"),hintLabel=hintLabel)
            addBinaryEdge(templateASTRootName,templateNodeName,"templateAST")


            //            gnn_input.updateTemplateIndicesAndNodeIds(templateASTRootName,hintLabel,cost = cost)//update JSON
            //            //println(t._1,hintLabel)
            //            //draw predicted label color
            //            val (predictedHintLabel,predictedCost) = getHintLabelAndCost(predictedTemplates,t,hp)
            //            if (predictedHintLabel)
            //              gnn_input.nodeInfoList(templateASTRootName).fillColor = "green"

            //(templateASTRootName,"verifHint"+t._3.toString)
            (templateNodeName,"verifHint"+t._3.toString)
          }
        hp.name->templateNameList
      }
    tempHeadMap
  }
  def encodeLabelToMultiClass(positiveMap: Map[Predicate, Seq[(IExpression, Int, TemplateType.Value)]],t:(IExpression, Int, TemplateType.Value),
                              hp:Predicate,currentTemplateSeq:Seq[(IExpression, Int, TemplateType.Value)]): (Int,Int) ={
    val encodingMap=Map(
      (TemplateTypeUsefulNess.TplEqTermUseless,TemplateTypeUsefulNess.TplInEqTermUseless,TemplateTypeUsefulNess.TplPredPosNegUseless)->0,
      (TemplateTypeUsefulNess.TplEqTermUseful,TemplateTypeUsefulNess.TplInEqTermUseless,TemplateTypeUsefulNess.TplPredPosNegUseless)->1,
      (TemplateTypeUsefulNess.TplEqTermUseless,TemplateTypeUsefulNess.TplInEqTermUseful,TemplateTypeUsefulNess.TplPredPosNegUseless)->2,
      (TemplateTypeUsefulNess.TplEqTermUseful,TemplateTypeUsefulNess.TplInEqTermUseful,TemplateTypeUsefulNess.TplPredPosNegUseless)->3,
      (TemplateTypeUsefulNess.TplEqTermUseless,TemplateTypeUsefulNess.TplInEqTermUseless,TemplateTypeUsefulNess.TplPredPosNegUseful)->4)
    if (positiveMap.keySet.map(_.toString).contains(hp.toString)) {
      t._3 match {
        case TemplateType.TplEqTerm=>{
          val tUsefulness=getHintLabelUsefulness(positiveMap(hp),t)
          val correspondingT=currentTemplateSeq.filter(x=>x._1==t._1&&x._3==TemplateType.TplInEqTerm)
          val correspondingTUsefulness=if(correspondingT.isEmpty){(TemplateTypeUsefulNess.TplInEqTermUseless,100)}else getHintLabelUsefulness(positiveMap(hp),correspondingT.head)
          (encodingMap(tUsefulness._1,correspondingTUsefulness._1,TemplateTypeUsefulNess.TplPredPosNegUseless),tUsefulness._2)
        }
        case TemplateType.TplInEqTerm=>{
          val tUsefulness=getHintLabelUsefulness(positiveMap(hp),t)
          val correspondingT=currentTemplateSeq.filter(x=>x._1==t._1&&x._3==TemplateType.TplEqTerm)
          val correspondingTUsefulness=if(correspondingT.isEmpty){(TemplateTypeUsefulNess.TplEqTermUseless,100)}else getHintLabelUsefulness(positiveMap(hp),correspondingT.head)
          (encodingMap(correspondingTUsefulness._1,tUsefulness._1,TemplateTypeUsefulNess.TplPredPosNegUseless),tUsefulness._2)
        }
        case TemplateType.TplPredPosNeg=>{
          val tUsefulness=getHintLabelUsefulness(positiveMap(hp),t)
          (encodingMap(TemplateTypeUsefulNess.TplEqTermUseless,TemplateTypeUsefulNess.TplInEqTermUseless,tUsefulness._1),tUsefulness._2)
        }
      }
    }else (4, 100)
  }

  def getHintLabelUsefulness(positiveSeq: Seq[(IExpression, Int, TemplateType.Value)],t:(IExpression, Int, TemplateType.Value)):
  (TemplateTypeUsefulNess.Value,Int) ={
      val (b, c) = HintsSelection.termContains(positiveSeq, t)
      b match {
        case true=>
          t._3 match {
            case TemplateType.TplEqTerm=>(TemplateTypeUsefulNess.TplEqTermUseful, c)
            case TemplateType.TplInEqTerm=>(TemplateTypeUsefulNess.TplInEqTermUseful,c)
            case TemplateType.TplPredPosNeg=>(TemplateTypeUsefulNess.TplPredPosNegUseful,c)
          }
        case false=>
          t._3 match {
            case TemplateType.TplEqTerm=>(TemplateTypeUsefulNess.TplEqTermUseless, c)
            case TemplateType.TplInEqTerm=>(TemplateTypeUsefulNess.TplInEqTermUseless,c)
            case TemplateType.TplPredPosNeg=>(TemplateTypeUsefulNess.TplPredPosNegUseless,c)
          }
      }
  }


  def getHintLabelAndCost(tpl: Map[Predicate, Seq[(IExpression, Int, TemplateType.Value)]],t:(IExpression, Int, TemplateType.Value),
                          hp:Predicate): (Int,Int) ={

    if (tpl.keySet.map(_.toString).contains(hp.toString)) {
      val (b, c) = HintsSelection.termContains(tpl(hp), t)
      b match {
        case true=>
          t._3 match {
            case TemplateType.TplPredPosNeg=>(3,c)
            case TemplateType.TplEqTerm=>(1, c)
            case TemplateType.TplInEqTerm=>(2,c)
            case _=>(0,c)
          }
        case false=>(0, 100)
      }
    } else {
      (0, 100)
    }
  }

  def updateArgumentInfoHornGraphList(pre:String,tempID:Int,argumentnodeName:String,arg:ITerm): Unit ={
    val localArgInfo=new argumentInfoHronGraph(pre, tempID,gnn_input.GNNNodeID-1)
    localArgInfo.canonicalName=argumentnodeName
    localArgInfo.constNames:+=arg.toString
    gnn_input.argumentInfoHornGraphList += localArgInfo
  }

}



