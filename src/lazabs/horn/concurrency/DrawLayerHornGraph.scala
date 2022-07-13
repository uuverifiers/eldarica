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

import ap.parser.{IAtom, IBinJunctor, LineariseVisitor}
import lazabs.GlobalParameters
import lazabs.horn.concurrency.DrawHornGraph.addQuotes

import scala.collection.mutable.ArrayBuffer

class DrawLayerHornGraph(file: String, clausesCollection: ClauseInfo, hints: VerificationHintsInfo, argumentInfoList: ArrayBuffer[argumentInfo]) extends DrawHornGraph(file: String, clausesCollection: ClauseInfo, hints: VerificationHintsInfo, argumentInfoList: ArrayBuffer[argumentInfo]) {
  println("Write " + GlobalParameters.get.hornGraphType.toString + " to file")
  GlobalParameters.get.hornGraphType match {
    case DrawHornGraph.HornGraphType.clauseRelatedTaskLayerGraph => {
      edgeNameMap += ("predicateInstance" -> "PI")
      edgeNameMap += ("argumentInstance" -> "AI")
      edgeNameMap += ("control" -> "CTRL")
      edgeNameMap += ("controlArgument" -> "ARG")
      edgeNameMap += ("guard" -> "guard")
      edgeNameMap += ("data" -> "data")
    }
    case DrawHornGraph.HornGraphType.fineGrainedEdgeTypeLayerGraph => {
      edgeNameMap += ("predicateArgument" -> "PA")
      edgeNameMap += ("predicateInstanceHead" -> "PIH")
      edgeNameMap += ("predicateInstanceBody" -> "PIB")
      edgeNameMap += ("argumentInstance" -> "AI")
      edgeNameMap += ("controlHead" -> "CH")
      edgeNameMap += ("controlBody" -> "CB")
      edgeNameMap += ("controlArgumentHead" -> "CAH")
      edgeNameMap += ("controlArgumentBody" -> "CAB")
      edgeNameMap += ("guardConstant" -> "guard_const")
      edgeNameMap += ("guardOperator" -> "guard_op")
      edgeNameMap += ("guardSc" -> "guard_sc")
      edgeNameMap += ("dataConstant" -> "data_const")
      edgeNameMap += ("dataOperator" -> "data_op")
      edgeNameMap += ("dataSc" -> "data_sc")
      edgeNameMap += ("subTermConstantOperator" -> "ste_const_op")
      edgeNameMap += ("subTermOperatorOperator" -> "ste_op_op")
      edgeNameMap += ("subTermScOperator" -> "ste_sc_op")
    }
    case _ => {
      edgeNameMap += ("predicateArgument" -> "PA")
      edgeNameMap += ("predicateInstance" -> "PI")
      edgeNameMap += ("argumentInstance" -> "AI")
      edgeNameMap += ("controlHead" -> "CH")
      edgeNameMap += ("controlBody" -> "CB")
      edgeNameMap += ("controlArgument" -> "CA")
      edgeNameMap += ("guard" -> "guard")
      edgeNameMap += ("data" -> "data")
      edgeNameMap += ("subTerm" -> "st")
    }
  }
  //turn on/off edge's label
  var edgeNameSwitch = true
  if (edgeNameSwitch == false) {
    for (key <- edgeNameMap.keys)
      edgeNameMap += (key -> "")
  }
  GlobalParameters.get.hornGraphType match {
    case DrawHornGraph.HornGraphType.hybridDirectionLayerGraph => {
      edgeDirectionMap += ("predicateArgument" -> false)
      edgeDirectionMap += ("predicateInstance" -> false)
      edgeDirectionMap += ("argumentInstance" -> true)
      edgeDirectionMap += ("controlHead" -> false)
      edgeDirectionMap += ("controlBody" -> false)
      edgeDirectionMap += ("controlArgument" -> false)
      edgeDirectionMap += ("guard" -> false)
      edgeDirectionMap += ("data" -> false)
      edgeDirectionMap += ("subTerm" -> false)
    }
    case DrawHornGraph.HornGraphType.biDirectionLayerGraph => {
      for (edgeName <- edgeNameMap.keySet)
        edgeDirectionMap += (edgeName -> true)
    }
    case _ => {
      for (edgeName <- edgeNameMap.keySet)
        edgeDirectionMap += (edgeName -> false)
    }
  }
  //node shape map
  nodeShapeMap += ("constant" -> "circle")
  nodeShapeMap += ("operator" -> "square")
  nodeShapeMap += ("predicateName" -> "box")
  nodeShapeMap += ("FALSE" -> "box")
  nodeShapeMap += ("predicateArgument" -> "ellipse")
  nodeShapeMap += ("clause" -> "box")
  nodeShapeMap += ("clauseHead" -> "box")
  nodeShapeMap += ("clauseBody" -> "box")
  nodeShapeMap += ("clauseArgument" -> "ellipse")
  nodeShapeMap += ("symbolicConstant" -> "circle")
  //node cotegory: Operator and Constant don't need canonical name. FALSE is unique category
  val predicateNamePrefix = "predicate_"
  val predicateArgumentPrefix = "predicateArgument_"
  val clausePrefix = "clause_"
  val clauseHeadPrefix = "clauseHead_"
  val clauseBodyPrefix = "clauseBody_"
  val clauseArgumentPrefix = "clauseArgument_"
  val symbolicConstantPrefix = "symbolicConstant_"

  var predicateNameMap = Map[String, predicateInfo]() //original name -> canonical name
  class predicateInfo(predicateName: String) {
    val predicateCanonicalName = predicateName
    var argumentCanonicalNameList = new ArrayBuffer[Pair[String, Int]]() //(canonicalName, ID)
  }
  for (clause <- simpClauses; a <- clause.allAtoms) {
    createPredicateLayerNodesAndEdges(a)
  }
  //simpClauses.take(2).tail.foreach(println(_))
  for (clause <- simpClauses) {
    constantNodeSetInOneClause.clear()
    //clause layer: create clause node
    val clauseNodeName = clausePrefix + gnn_input.clauseCanonicalID.toString
    createNode(clauseNodeName,
      "C" + gnn_input.clauseCanonicalID.toString, "clause", nodeShapeMap("clause"), Seq(clause))
    //draw constraints and connect to clause node
    for (conjunct <- LineariseVisitor(clause.constraint, IBinJunctor.And)) {
      GlobalParameters.get.hornGraphType match {
        case DrawHornGraph.HornGraphType.clauseRelatedTaskLayerGraph => astEdgeType = "guard"
        case _ =>
      }
      drawAST(conjunct, clauseNodeName)
    }

    //clause layer: create clause head node
    val clauseHeadNodeName = clauseHeadPrefix + gnn_input.clauseHeadCanonicalID.toString
    createNode(clauseHeadNodeName,
      "HEAD", "clauseHead", nodeShapeMap("clauseHead"))
    //clause layer: create edge between head and clause node
    GlobalParameters.get.hornGraphType match {
      case DrawHornGraph.HornGraphType.clauseRelatedTaskLayerGraph => addBinaryEdge(clauseNodeName, clauseHeadNodeName, "control", edgeDirectionMap("control"))
      case _ => addBinaryEdge(clauseNodeName, clauseHeadNodeName, "controlHead", edgeDirectionMap("controlHead"))
    }
    //predicateLayer->clauseLayer: connect predicate to clause head
    GlobalParameters.get.hornGraphType match {
      case DrawHornGraph.HornGraphType.clauseRelatedTaskLayerGraph => addBinaryEdge(clauseHeadNodeName, predicateNameMap(clause.head.pred.name).predicateCanonicalName, "predicateInstance", edgeDirectionMap("predicateInstance"))
      case DrawHornGraph.HornGraphType.fineGrainedEdgeTypeLayerGraph => addBinaryEdge(predicateNameMap(clause.head.pred.name).predicateCanonicalName, clauseHeadNodeName, "predicateInstanceHead", edgeDirectionMap("predicateInstanceHead"))
      case _ => addBinaryEdge(predicateNameMap(clause.head.pred.name).predicateCanonicalName, clauseHeadNodeName, "predicateInstance", edgeDirectionMap("predicateInstance"))
    }
    createAndConnectAguments(clauseHeadNodeName, clause.head)

    //clause layer: create clause arguments node in body
    var tempIDForPredicate = 0
    for (bodyPredicate <- clause.body) {
      //clause layer: create clause body node
      val clauseBodyNodeName = clauseBodyPrefix + gnn_input.clauseBodyCanonicalID.toString
      createNode(clauseBodyNodeName,
        "BODY" + tempIDForPredicate.toString, "clauseBody", nodeShapeMap("clauseBody"))
      tempIDForPredicate += 1
      //clause layer: create edge between body and clause node
      GlobalParameters.get.hornGraphType match {
        case DrawHornGraph.HornGraphType.clauseRelatedTaskLayerGraph => addBinaryEdge(clauseNodeName, clauseBodyNodeName, "control", edgeDirectionMap("control"))
        case _ => addBinaryEdge(clauseBodyNodeName, clauseNodeName, "controlBody", edgeDirectionMap("controlBody"))
      }
      //predicateLayer->clauseLayer: connect predicate to clause body
      GlobalParameters.get.hornGraphType match {
        case DrawHornGraph.HornGraphType.fineGrainedEdgeTypeLayerGraph=>addBinaryEdge(clauseBodyNodeName, predicateNameMap(bodyPredicate.pred.name).predicateCanonicalName, "predicateInstanceBody", edgeDirectionMap("predicateInstanceBody"))
        case _ =>addBinaryEdge(clauseBodyNodeName, predicateNameMap(bodyPredicate.pred.name).predicateCanonicalName, "predicateInstance", edgeDirectionMap("predicateInstance"))
      }


      createAndConnectAguments(clauseBodyNodeName, bodyPredicate)
    }
  }

  //draw templates
  astEdgeType = "subTerm"//templateAST"
  val templateNameList=if(GlobalParameters.get.extractPredicates) drawPredicate() else drawTemplates()
  for ((head,templateNodeNameList)<-templateNameList;templateNodeName<-templateNodeNameList) {
    addBinaryEdge(from=predicateNameMap(head).predicateCanonicalName,to=templateNodeName._1,label=templateNodeName._2)
  }

  drawAllNodes()


  writerGraph.write("}" + "\n")
  writerGraph.close()
  //form label here
  val (argumentIDList, argumentNameList, argumentOccurrenceList, argumentBoundList, argumentIndicesList, argumentBinaryOccurrenceList) = matchArguments()
  writeGNNInputToJSONFile(argumentIDList, argumentNameList, argumentOccurrenceList, argumentBoundList, argumentIndicesList, argumentBinaryOccurrenceList)
  /*
  //write JSON file by json library
  val layerVersionGraphGNNInput=Json.obj("nodeIds" -> gnn_input.nodeIds,"nodeSymbolList"->gnn_input.nodeSymbols,
    "argumentIndices"->gnn_input.argumentIndices,
    "binaryAdjacentList"->gnn_input.binaryAdjacency.binaryEdge.toVector.toString(),
    "ternaryAdjacencyList"->gnn_input.ternaryAdjacency.ternaryEdge.toString,
    "predicateArgumentEdges"->gnn_input.predicateArgumentEdges.binaryEdge.toString,
    "predicateInstanceEdges"->gnn_input.predicateInstanceEdges.binaryEdge.toString,
    "argumentInstanceEdges"->gnn_input.argumentInstanceEdges.binaryEdge.toString,
    "controlHeadEdges"->gnn_input.controlHeadEdges.binaryEdge.toString,
    "controlBodyEdges"->gnn_input.controlBodyEdges.binaryEdge.toString,
    "controlArgumentEdges"->gnn_input.controlArgumentEdges.binaryEdge.toString,
    "guardEdges"->gnn_input.guardEdges.binaryEdge.toString,
    "dataEdges"->gnn_input.dataEdges.binaryEdge.toString,
    "unknownEdges"->gnn_input.unknownEdges.binaryEdge.toString,
    "argumentIDList"->argumentIDList,
    "argumentNameList"->argumentNameList,
    "argumentOccurrence"->argumentOccurrenceList)
  println("Write GNNInput to file")
  val writer = new PrintWriter(new File(file + ".layerHornGraph.JSON")) //python path
  writer.write(layerVersionGraphGNNInput.toString())
  writer.close()
*/

  def createAndConnectAguments(clauseHeadOrBodyName: String, pred: IAtom): Unit = {

    var tempIDForArgument = 0
    for ((bodyArgument, predicateArgument) <- pred.args zip predicateNameMap(pred.pred.name).argumentCanonicalNameList) {
      //clause layer: create clause body/head argument node
      val clauseArgumentNodeName = clauseArgumentPrefix + gnn_input.clauseArgCanonicalID.toString
      createNode(clauseArgumentNodeName,
        "ARG" + tempIDForArgument.toString, "clauseArgument", nodeShapeMap("clauseArgument"))
      //clause layer: create edge between body/head and argument
      GlobalParameters.get.hornGraphType match {
        case DrawHornGraph.HornGraphType.clauseRelatedTaskLayerGraph => addBinaryEdge(clauseArgumentNodeName, clauseHeadOrBodyName, "controlArgument", edgeDirectionMap("controlArgument"))
        case DrawHornGraph.HornGraphType.fineGrainedEdgeTypeLayerGraph =>{
          clauseHeadOrBodyName.substring(0, clauseHeadOrBodyName.indexOf("_")) match {
            case "clauseHead" => addBinaryEdge(clauseHeadOrBodyName, clauseArgumentNodeName, "controlArgumentHead", edgeDirectionMap("controlArgumentHead"))
            case "clauseBody" => addBinaryEdge(clauseArgumentNodeName, clauseHeadOrBodyName, "controlArgumentBody", edgeDirectionMap("controlArgumentBody"))
          }
        }
        case _ => {
          clauseHeadOrBodyName.substring(0, clauseHeadOrBodyName.indexOf("_")) match {
            case "clauseHead" => addBinaryEdge(clauseHeadOrBodyName, clauseArgumentNodeName, "controlArgument", edgeDirectionMap("controlArgument"))
            case "clauseBody" => addBinaryEdge(clauseArgumentNodeName, clauseHeadOrBodyName, "controlArgument", edgeDirectionMap("controlArgument"))
          }
        }
      }
      //predicateLayer->clauseLayer: connect predicate argument to clause argument
      GlobalParameters.get.hornGraphType match {
        case DrawHornGraph.HornGraphType.clauseRelatedTaskLayerGraph => {
          astEdgeType = "data"
          addBinaryEdge(clauseArgumentNodeName, predicateArgument._1, "argumentInstance", edgeDirectionMap("argumentInstance"))
        }
        case _ => addBinaryEdge(predicateArgument._1, clauseArgumentNodeName, "argumentInstance", edgeDirectionMap("argumentInstance"))
      }
      clauseHeadOrBodyName.substring(0, clauseHeadOrBodyName.indexOf("_")) match {
        case "clauseHead" => {
          astEndNodeType = "clauseHead"
        }
        case "clauseBody" => {
          astEndNodeType = "clauseBody"
        }
      }
      drawAST(bodyArgument, clauseArgumentNodeName)
      tempIDForArgument += 1
    }
  }


  def createPredicateLayerNodesAndEdges(pred: IAtom): Unit = {
    //predicate layer: create predicate and argument node
    if (!predicateNameMap.contains(pred.pred.name)) {
      if (pred.pred.name != "FALSE") {
        val predicateNodeCanonicalName = predicateNamePrefix + gnn_input.predicateNameCanonicalID.toString
        predicateNameMap += (pred.pred.name -> new predicateInfo(predicateNodeCanonicalName))
        createNode(predicateNodeCanonicalName,
          pred.pred.name, "predicateName", nodeShapeMap("predicateName"))
        var tempID = 0
        var argumentNodeArray = Array[(String,String)]()
        for ((headArg,i) <- pred.args.zipWithIndex) {
          val argumentNodeCanonicalName = predicateArgumentPrefix + gnn_input.predicateArgumentCanonicalID.toString
          //create argument node
          createNode(argumentNodeCanonicalName,
            "Arg" + tempID.toString, "predicateArgument", nodeShapeMap("predicateArgument"))
          argumentNodeArray :+= ("_"+i.toString,argumentNodeCanonicalName)
          //create edge from argument to predicate
          GlobalParameters.get.hornGraphType match {
            case DrawHornGraph.HornGraphType.clauseRelatedTaskLayerGraph => addBinaryEdge(argumentNodeCanonicalName, predicateNodeCanonicalName, "controlArgument", edgeDirectionMap("controlArgument"))
            case _ => addBinaryEdge(predicateNodeCanonicalName, argumentNodeCanonicalName, "predicateArgument", edgeDirectionMap("predicateArgument"))
          }
          predicateNameMap(pred.pred.name).argumentCanonicalNameList += Pair(argumentNodeCanonicalName, tempID)
          //gnn_input.argumentInfoHornGraphList += new argumentInfoHronGraph(pred.pred.name, tempID,gnn_input.GNNNodeID-1)
          updateArgumentInfoHornGraphList(pred.pred.name, tempID, argumentNodeCanonicalName, headArg)
          tempID += 1
        }
        argumentNodeSetCrossGraph(pred.pred.name) = argumentNodeArray
      } else {
        val predicateNodeCanonicalName = "FALSE"
        predicateNameMap += (pred.pred.name -> new predicateInfo(predicateNodeCanonicalName))
        createNode(predicateNodeCanonicalName,
          pred.pred.name, "FALSE", nodeShapeMap("FALSE"))
      }


    }
  }


}

