/**
 * Copyright (c) 2011-2020 Philipp Ruemmer, Chencheng Liang.
 * All rights reserved.
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
import ap.parser.ConstantSubstVisitor
import ap.SimpleAPI
import ap.basetypes.IdealInt
import ap.parser._
import ap.parser.smtlib.Absyn.ConstantTerm
import ap.terfor.preds.Predicate
import ap.types.Sort.Integer.newConstant
import lazabs.GlobalParameters
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs
import lazabs.horn.concurrency.DrawHornGraph.{HornGraphType, addQuotes}
import lazabs.horn.concurrency.DrawHyperEdgeHornGraph.HyperEdgeType
import lazabs.horn.concurrency.HintsSelection.{predicateQuantify, replaceMultiSamePredicateInBody, timeoutForPredicateDistinct}

import java.io.{BufferedWriter, File, FileWriter, PrintWriter}
import scala.collection.mutable.ArrayBuffer

object DrawHyperEdgeHornGraph {

  object HyperEdgeType extends Enumeration {
    val controlFlow, dataFlow = Value
  }

  def replaceIntersectArgumentInBody(clause: Clause): Clause = {
    var f: IFormula = clause.constraint
    def replaceArgumentInBody(body: IAtom): IAtom = {
      var argList: Seq[ITerm] = Seq()
      for (arg <- body.args) {
        if ((for (a<-clause.head.args) yield a.toString).contains(arg.toString)) {
          val ic = IConstant(newConstant(arg.toString + "__"))
          //replace argument
          argList :+= ic
          //add equation in constrains
          f = f &&& (arg === ic)
        } else
          argList :+= arg
      }
      IAtom(body.pred, argList)
    }

    Clause(IAtom(clause.head.pred, clause.head.args),
      for (body <- clause.body) yield replaceArgumentInBody(body),
      f)
  }

}

class hyperEdgeInfo(name: String, from: String = "", to: String, nodeType: HyperEdgeType.Value) {
  val hyperEdgeNodeName = name
  val fromName = from
  var guardName = Set[String]()
  val toName = to
  val hyperEdgeType = nodeType
}

class DrawHyperEdgeHornGraph(file: String, clausesCollection: ClauseInfo, hints: VerificationHintsInfo, argumentInfoList: ArrayBuffer[argumentInfo]) extends DrawHornGraph(file: String, clausesCollection: ClauseInfo, hints: VerificationHintsInfo, argumentInfoList: ArrayBuffer[argumentInfo]) {
  println("Write " + GlobalParameters.get.hornGraphType.toString + " to file")
  val withOutAndConnectionToHyperedge = false
  edgeNameMap += ("controlFlowHyperEdge" -> "CFHE")
  edgeNameMap += ("dataFlowHyperEdge" -> "DFHE")
  edgeNameMap += ("dataFlowAST" -> "data")
  edgeNameMap += ("guardAST" -> "guard")
  edgeNameMap += ("AST" -> "AST")
  edgeNameMap += ("AST_1" -> "AST_1")
  edgeNameMap += ("AST_2" -> "AST_2")
  edgeNameMap += ("argument" -> "arg")
  edgeNameMap += ("clause" -> "clause")
  edgeNameMap += ("template" -> "template")
  edgeNameMap += ("verifHintTplPred" -> "Pred")
  edgeNameMap += ("verifHintTplPredPosNeg" -> "PredPosNeg")
  edgeNameMap += ("verifHintTplEqTerm" -> "EqTerm (tpl)")
  edgeNameMap += ("verifHintTplInEqTerm" -> "InEqTerm (tpl)")
  edgeNameMap += ("verifHintTplInEqTermPosNeg" -> "InEqTermPosNeg")
  //turn on/off edge's label
  var edgeNameSwitch = true
  if (edgeNameSwitch == false) {
    for (key <- edgeNameMap.keys)
      edgeNameMap += (key -> "")
  }
  edgeDirectionMap += ("controlFlowHyperEdge" -> false)
  edgeDirectionMap += ("dataFlowHyperEdge" -> false)
  edgeDirectionMap += ("dataFlowAST" -> false)
  edgeDirectionMap += ("guardAST" -> false)
  edgeDirectionMap += ("AST" -> false)
  edgeDirectionMap += ("AST_1" -> false)
  edgeDirectionMap += ("AST_2" -> false)
  edgeDirectionMap += ("argument" -> false)
  edgeDirectionMap += ("clause" -> false)
  //node cotegory: Operator and Constant don't need canonical name. FALSE is unique category
  val controlNodePrefix = "CONTROLN_"
  val symbolicConstantNodePrefix = "SYMBOLIC_CONSTANT_"
  val argumentNodePrefix = "predicateArgument"
  val controlFlowHyperEdgeNodePrefix = "CFHE_"
  val dataFlowHyperEdgeNodePrefix = "DFHE_"
  val clauseNodePrefix = "clause_"
  //node shape map
  nodeShapeMap += ("CONTROL" -> "component")
  nodeShapeMap += ("operator" -> "square")
  nodeShapeMap += ("symbolicConstant" -> "circle")
  nodeShapeMap += ("constant" -> "circle")
  nodeShapeMap += ("predicateArgument" -> "ellipse")
  nodeShapeMap += ("FALSE" -> "component")
  nodeShapeMap += ("controlFlowHyperEdge" -> "diamond")
  nodeShapeMap += ("dataFlowHyperEdge" -> "diamond")
  nodeShapeMap += ("clause" -> "component")

  //val sp = new Simplifier()
  var tempID = 0
  var clauseNumber = 0
  var hyperEdgeList = scala.collection.mutable.ArrayBuffer[hyperEdgeInfo]()
  //create unique Initial and FALSE node
  val initialControlFlowNodeName = controlNodePrefix + gnn_input.CONTROLCanonicalID.toString
  createNode(canonicalName = initialControlFlowNodeName, labelName = "Initial", className = "CONTROL", shape = nodeShapeMap("CONTROL"))
  controlFlowNodeSetCrossGraph("Initial") = initialControlFlowNodeName
  //  val falseControlFlowNodeName = controlNodePrefix + gnn_input.CONTROLCanonicalID.toString
  //  createNode(canonicalName=falseControlFlowNodeName, labelName="FALSE", className="CONTROL", shape=nodeShapeMap("CONTROL"))
  //  controlFlowNodeSetCrossGraph("FALSE") = falseControlFlowNodeName
  var guardSubGraph:Map[Predicate,Seq[Tuple2[String,IFormula]]] = (for (clause <- simpClauses; a <- clause.allAtoms; if a.pred.name != "FALSE") yield a.pred -> Seq()).toMap

  val bodyReplacedClauses=(for (c<-simpClauses) yield replaceMultiSamePredicateInBody(c)).flatten// replace multiple same predicate in body
  //bodyReplacedClauses.foreach(println)
  for (clause <- bodyReplacedClauses) {
    //simplify clauses by quantifiers and replace arguments to _0,_1,...
    val (dataFlowSet, guardSet, normalizedClause) = getDataFlowAndGuard(clause)
    //draw head predicate node and argument node
    val headNodeName =
      if (normalizedClause.head.pred.name == "FALSE") {
        //draw predicate node
        drawPredicateNode("FALSE", "FALSE", "FALSE")
        "FALSE"
        //falseControlFlowNodeName
      } else {
        if (!controlFlowNodeSetCrossGraph.keySet.contains(normalizedClause.head.pred.name)) {
          //draw predicate node
          val controlFlowNodeName = controlNodePrefix + gnn_input.CONTROLCanonicalID.toString
          drawPredicateNode(controlFlowNodeName, normalizedClause.head.pred.name, "CONTROL")
          //draw argument node
          drawArgumentNodeForPredicate(normalizedClause.head, controlFlowNodeName)
          controlFlowNodeName

        } else {
          for (controlNodeName <- argumentNodeSetCrossGraph.keySet) if (controlNodeName == normalizedClause.head.pred.name) {
            for ((argNodeName, arg) <- argumentNodeSetCrossGraph(controlNodeName).map(_._2) zip normalizedClause.head.args) {
              constantNodeSetInOneClause(arg.toString) = argNodeName
            }
          }
          controlFlowNodeSetCrossGraph(normalizedClause.head.pred.name)
        }
      }
    //draw body predicate node and argument node
    var bodyNodeNameList: Array[String] = Array()
    if (normalizedClause.body.isEmpty) {
      //draw predicate node: initial node
      //val initialControlFlowNodeName = controlNodePrefix + gnn_input.CONTROLCanonicalID.toString
      //drawPredicateNode(initialControlFlowNodeName, "Initial", "CONTROL")

      //draw control flow hyperedge node between body and head
      val controlFlowHyperedgeName = controlFlowHyperEdgeNodePrefix + gnn_input.controlFlowHyperEdgeCanonicalID.toString
      matchAndCreateHyperEdgeNode(controlFlowHyperedgeName, "guarded CFHE Clause " + clauseNumber.toString, "controlFlowHyperEdge")
      //store control flow hyperedge connection between body and head
      hyperEdgeList :+= new hyperEdgeInfo(controlFlowHyperedgeName, initialControlFlowNodeName, controlFlowNodeSetCrossGraph(normalizedClause.head.pred.name), HyperEdgeType.controlFlow)
      bodyNodeNameList :+= initialControlFlowNodeName
    } else {
      for (body <- normalizedClause.body) {
        if (!controlFlowNodeSetCrossGraph.keySet.contains(body.pred.name)) {
          //draw predicate node
          val controlFlowNodeName = controlNodePrefix + gnn_input.CONTROLCanonicalID.toString
          bodyNodeNameList :+= controlFlowNodeName
          drawPredicateNode(controlFlowNodeName, body.pred.name, "CONTROL")
          //draw control flow hyperedge node between body and head
          val controlFlowHyperedgeName = controlFlowHyperEdgeNodePrefix + gnn_input.controlFlowHyperEdgeCanonicalID.toString
          matchAndCreateHyperEdgeNode(controlFlowHyperedgeName, "guarded CFHE Clause " + clauseNumber.toString, "controlFlowHyperEdge")
          //store control flow hyperedge connection between body and head
          hyperEdgeList :+= new hyperEdgeInfo(controlFlowHyperedgeName, controlFlowNodeName, controlFlowNodeSetCrossGraph(normalizedClause.head.pred.name), HyperEdgeType.controlFlow)
          //draw argument node
          drawArgumentNodeForPredicate(body, controlFlowNodeName)
        } else {
          for (controlNodeName <- argumentNodeSetCrossGraph.keySet) if (controlNodeName == body.pred.name) {
            for ((argNodeName, arg) <- argumentNodeSetCrossGraph(controlNodeName).map(_._2) zip body.args) {
              constantNodeSetInOneClause(arg.toString) = argNodeName
            }
            bodyNodeNameList :+= controlFlowNodeSetCrossGraph(controlNodeName)
          }
          //draw control flow hyperedge node between body and head
          val controlFlowHyperedgeName = controlFlowHyperEdgeNodePrefix + gnn_input.controlFlowHyperEdgeCanonicalID.toString
          matchAndCreateHyperEdgeNode(controlFlowHyperedgeName, "guarded CFHE Clause " + clauseNumber.toString, "controlFlowHyperEdge")
          //store control flow hyperedge connection between body and head
          hyperEdgeList :+= new hyperEdgeInfo(controlFlowHyperedgeName, controlFlowNodeSetCrossGraph(body.pred.name), controlFlowNodeSetCrossGraph(normalizedClause.head.pred.name), HyperEdgeType.controlFlow)
        }
      }
    }
    //draw dataflow
    for (arg <- normalizedClause.head.args)
      drawDataFlow(arg, dataFlowSet)
    var guardRootNodeList: Array[String] = Array()
    if (withOutAndConnectionToHyperedge == true) {
      if (guardSet.isEmpty) {
        guardRootNodeList :+= drawTrueGuardCondition()
      } else {
        //astEdgeType = "guardAST"
        astEdgeType = "AST"
        for (guard <- guardSet) {
          val guardRootNodeName = drawAST(guard)
          for (a <- normalizedClause.allAtoms; if a.pred.name != "FALSE") {
            guardSubGraph = guardSubGraph ++ Map(a.pred -> (guardSubGraph(a.pred) ++ Seq(Tuple2(guardRootNodeName,guard))))
          }

          guardRootNodeList :+= guardRootNodeName
          for (hyperEdgeNode <- hyperEdgeList) {
            hyperEdgeNode.guardName += guardRootNodeName
            if (hyperEdgeNode.guardName.size <= 1) {
              GlobalParameters.get.hornGraphType match {
                case HornGraphType.concretizedHyperedgeGraph => drawHyperEdge(hyperEdgeNode, guardRootNodeName, addConcretinizedTernaryEdge)
                case HornGraphType.hyperEdgeGraph | HornGraphType.equivalentHyperedgeGraph => drawHyperEdge(hyperEdgeNode, guardRootNodeName, addTernaryEdge)
              }
            } else
              GlobalParameters.get.hornGraphType match {
                case HornGraphType.concretizedHyperedgeGraph => drawHyperEdge(hyperEdgeNode, guardRootNodeName, updateConcretinizedTernaryEdge)
                case HornGraphType.hyperEdgeGraph | HornGraphType.equivalentHyperedgeGraph => drawHyperEdge(hyperEdgeNode, guardRootNodeName, updateTernaryEdge)
              }
          }
        }
      }
    } else {
      if (guardSet.isEmpty) {
        guardRootNodeList :+= drawTrueGuardCondition()
      } else if (guardSet.size == 1) {
        //astEdgeType = "guardAST"
        astEdgeType = "AST"
        for (guard <- guardSet) {
          if (guard.isTrue)
            guardRootNodeList :+= drawTrueGuardCondition()
          else{
            val guardRootNodeName = drawAST(guard)
            guardRootNodeList :+=guardRootNodeName
            for (a <- normalizedClause.allAtoms; if a.pred.name != "FALSE") {
              guardSubGraph = guardSubGraph ++ Map(a.pred -> (guardSubGraph(a.pred) ++ Seq(Tuple2(guardRootNodeName,guard))))
            }
            for (hyperEdgeNode <- hyperEdgeList) {
              hyperEdgeNode.guardName += guardRootNodeName
              GlobalParameters.get.hornGraphType match {
                case HornGraphType.concretizedHyperedgeGraph => drawHyperEdge(hyperEdgeNode, guardRootNodeName, addConcretinizedTernaryEdge)
                case HornGraphType.hyperEdgeGraph | HornGraphType.equivalentHyperedgeGraph => drawHyperEdge(hyperEdgeNode, guardRootNodeName, addTernaryEdge)
              }
            }
          }
        }
      } else {
        //astEdgeType = "guardAST"
        astEdgeType = "AST"
        //draw all guardSet
        for (guard <- guardSet) {
          val guardRootNodeName = drawAST(guard)
          for (a <- normalizedClause.allAtoms; if a.pred.name != "FALSE") {
            guardSubGraph = guardSubGraph ++ Map(a.pred -> (guardSubGraph(a.pred) ++ Seq(Tuple2(guardRootNodeName,guard))))
          }
          guardRootNodeList :+= guardRootNodeName
        }
        //connect guards by &
        val andName = "&" + "_" + gnn_input.GNNNodeID
        createNode(andName, labelName = "&", "operator", nodeShapeMap("operator"))
        for (frn <- guardRootNodeList)
          addBinaryEdge(frn, andName, "guardAST", edgeDirectionMap("guardAST")) //AST,guardAST
        //connect & to hyperedge
        for (hyperEdgeNode <- hyperEdgeList) {
          val rootASTForHyperedge=andName //andName
          hyperEdgeNode.guardName += rootASTForHyperedge
          GlobalParameters.get.hornGraphType match {
            case HornGraphType.concretizedHyperedgeGraph => drawHyperEdge(hyperEdgeNode, rootASTForHyperedge, addConcretinizedTernaryEdge)
            case HornGraphType.hyperEdgeGraph | HornGraphType.equivalentHyperedgeGraph => drawHyperEdge(hyperEdgeNode, rootASTForHyperedge, addTernaryEdge)//updateTernaryEdge
          }
        }
      }
    }
    if (GlobalParameters.get.getLabelFromCounterExample == true) {
      //create clause node and connect with guards
      val clauseNodeName = clauseNodePrefix + gnn_input.clauseCanonicalID.toString
      createNode(clauseNodeName, clauseNodeName, "clause", nodeShapeMap("clause"), Seq(clause))
      //add edges to the clause
      for (guardRootNode <- guardRootNodeList) { //from guards to clause
        addBinaryEdge(guardRootNode, clauseNodeName, "AST")//guardAST
      }
      addBinaryEdge(clauseNodeName, headNodeName, label = "clause") //from clause to head
      for (bodyNodeName <- bodyNodeNameList) //from body to clause
        addBinaryEdge(bodyNodeName, clauseNodeName, "clause")
    }
    clauseNumber += 1

    hyperEdgeList.clear()
    constantNodeSetInOneClause.clear()
    binaryOperatorSubGraphSetInOneClause.clear()
    unaryOperatorSubGraphSetInOneClause.clear()
  }


    //draw templates
    astEdgeType = "AST"//"templateAST"
    val templateNameList=if(GlobalParameters.get.extractPredicates) drawPredicate() else drawTemplates()//drawTemplatesWithNode()
    for ((head, templateNodeNameList) <- templateNameList; templateNodeName <- templateNodeNameList)
      addBinaryEdge(controlFlowNodeSetCrossGraph(head), templateNodeName._1, templateNodeName._2)
    for (n<-gnn_input.nodeInfoList){ //draw all nodes

      if (n._2.labelList.isEmpty) {
        writerGraph.write(addQuotes(n._2.canonicalName) +
          " [label=" + addQuotes(n._2.labelName) + " nodeName=" + addQuotes(n._2.canonicalName) +
          " class=" + n._2.className + " shape=" + addQuotes(n._2.shape) +" color="+n._2.color+ " fillcolor="+n._2.fillColor + " style=filled"+"];" + "\n")
      } else {
        var labelContent=""
        var predictedLabelContent=""
        for (l<-n._2.labelList)
          labelContent=labelContent+l.toString+"|"
        labelContent=labelContent.dropRight(1)
        for (l<-n._2.predictedLabelList)
          predictedLabelContent=predictedLabelContent+l.toString+"|"
        predictedLabelContent=predictedLabelContent.dropRight(1)
        val finalLabelContent=(n._2.labelName+"|" + labelContent)
        val finalPredictedLabelContent=(n._2.labelName+"|" + predictedLabelContent)
        writerGraph.write(addQuotes(n._2.canonicalName) + "[shape=record label="+"\"{"+"{"+finalLabelContent+"}|{"+finalPredictedLabelContent+"}"+"}\""+"];"+"\n")
      }

  }

  writerGraph.write("}" + "\n")
  writerGraph.close()


  if (GlobalParameters.get.withoutGraphJSON==false){
    val (argumentIDList, argumentNameList, argumentOccurrenceList, argumentBoundList, argumentIndicesList, argumentBinaryOccurrenceList) = matchArguments()
    writeGNNInputToJSONFile(argumentIDList, argumentNameList, argumentOccurrenceList,
      argumentBoundList, argumentIndicesList, argumentBinaryOccurrenceList)
  }



  def matchAndCreateHyperEdgeNode(controlFlowHyperedgeName: String, labelName: String, className: String): Unit =
    GlobalParameters.get.hornGraphType match {
      case DrawHornGraph.HornGraphType.hyperEdgeGraph => createHyperEdgeNode(controlFlowHyperedgeName, labelName, className, nodeShapeMap(className))
      case DrawHornGraph.HornGraphType.equivalentHyperedgeGraph =>
      case DrawHornGraph.HornGraphType.concretizedHyperedgeGraph => createConcretinizedHyperEdgeNode(controlFlowHyperedgeName, labelName, className, nodeShapeMap(className))
    }

  def drawHyperEdgeWithTrueGuard(middleNodeName: String): Unit =
    GlobalParameters.get.hornGraphType match {
      case DrawHornGraph.HornGraphType.equivalentHyperedgeGraph => {
        for (hyperEdgeNode <- hyperEdgeList) {
          hyperEdgeNode.hyperEdgeType match {
            case HyperEdgeType.controlFlow => {
              addBinaryEdge(hyperEdgeNode.fromName, middleNodeName, label = "controlFlowHyperEdge")
              addBinaryEdge(middleNodeName, hyperEdgeNode.toName, label = "controlFlowHyperEdge")
              addBinaryEdge(hyperEdgeNode.toName, hyperEdgeNode.fromName, label = "controlFlowHyperEdge")
            }
            case HyperEdgeType.dataFlow => {
              addBinaryEdge(hyperEdgeNode.fromName, middleNodeName, label = "dataFlowHyperEdge")
              addBinaryEdge(middleNodeName, hyperEdgeNode.toName, label = "dataFlowHyperEdge")
              addBinaryEdge(hyperEdgeNode.toName, hyperEdgeNode.fromName, label = "dataFlowHyperEdge")
            }
          }
        }
      }
      case DrawHornGraph.HornGraphType.concretizedHyperedgeGraph => {
        for (hyperEdgeNode <- hyperEdgeList) {
          hyperEdgeNode.hyperEdgeType match {
            case HyperEdgeType.controlFlow => addConcretinizedTernaryEdge(hyperEdgeNode.fromName, middleNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "controlFlowHyperEdge")
            case HyperEdgeType.dataFlow => addConcretinizedTernaryEdge(hyperEdgeNode.fromName, middleNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "dataFlowHyperEdge")
          }
        }
      }
      case DrawHornGraph.HornGraphType.hyperEdgeGraph => {
        for (hyperEdgeNode <- hyperEdgeList) {
          hyperEdgeNode.hyperEdgeType match {
            case HyperEdgeType.controlFlow => addTernaryEdge(hyperEdgeNode.fromName, middleNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "controlFlowHyperEdge")
            case HyperEdgeType.dataFlow => addTernaryEdge(hyperEdgeNode.fromName, middleNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "dataFlowHyperEdge")
          }
        }
      }
    }

  def drawHyperEdge(hyperEdgeNode: hyperEdgeInfo, guardRootNodeName: String, f: (String, String, String, String, String) => Unit): Unit =
    hyperEdgeNode.hyperEdgeType match {
      case HyperEdgeType.controlFlow => {
        GlobalParameters.get.hornGraphType match {
          case DrawHornGraph.HornGraphType.equivalentHyperedgeGraph => {
            addBinaryEdge(hyperEdgeNode.fromName, guardRootNodeName, label = "controlFlowHyperEdge")
            addBinaryEdge(guardRootNodeName, hyperEdgeNode.toName, label = "controlFlowHyperEdge")
            addBinaryEdge(hyperEdgeNode.toName, hyperEdgeNode.fromName, label = "controlFlowHyperEdge")
          }
          //case DrawHornGraph.HornGraphType.concretizedHyperedgeGraph=> addConcretinizedTernaryEdge(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "controlFlowHyperEdge")
          case DrawHornGraph.HornGraphType.hyperEdgeGraph | DrawHornGraph.HornGraphType.concretizedHyperedgeGraph =>
            f(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "controlFlowHyperEdge")
        }
      }
      case HyperEdgeType.dataFlow => {
        GlobalParameters.get.hornGraphType match {
          case DrawHornGraph.HornGraphType.equivalentHyperedgeGraph => {
            addBinaryEdge(hyperEdgeNode.fromName, guardRootNodeName, label = "dataFlowHyperEdge")
            addBinaryEdge(guardRootNodeName, hyperEdgeNode.toName, label = "dataFlowHyperEdge")
            addBinaryEdge(hyperEdgeNode.toName, hyperEdgeNode.fromName, label = "dataFlowHyperEdge")
          }
          //case DrawHornGraph.HornGraphType.concretizedHyperedgeGraph=> addConcretinizedTernaryEdge(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "dataFlowHyperEdge")
          case DrawHornGraph.HornGraphType.hyperEdgeGraph | DrawHornGraph.HornGraphType.concretizedHyperedgeGraph =>
            f(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "dataFlowHyperEdge")
        }
      }
    }

  def drawArgumentNodeForPredicate(pre: IAtom, controlFlowNodeName: String): Unit = {
    var argumentNodeArray = Array[(String,String)]()// (_1,argumentnodeName)
    tempID = 0
    for ((arg,i) <- pre.args.zipWithIndex) {
      val argumentnodeName = argumentNodePrefix + gnn_input.predicateArgumentCanonicalID.toString
      createNode(argumentnodeName, "ARG_" + tempID.toString, "predicateArgument", nodeShapeMap("predicateArgument"))
      constantNodeSetInOneClause(arg.toString) = argumentnodeName
      argumentNodeArray :+= ("_"+i.toString,argumentnodeName)
      updateArgumentInfoHornGraphList(pre.pred.name, tempID, argumentnodeName, arg)
      tempID += 1
      //connect to control flow node
      addBinaryEdge(argumentnodeName, controlFlowNodeName, "argument")
    }
    argumentNodeSetCrossGraph(pre.pred.name) = argumentNodeArray

  }

  def drawPredicateNode(controlFlowNodeName: String, predicateName: String, className: String): Unit = {
    //draw predicate node
    createNode(controlFlowNodeName, predicateName, className, nodeShapeMap(className))
    controlFlowNodeSetCrossGraph(predicateName) = controlFlowNodeName
  }

  def drawDataFlow(arg: ITerm, dataFlowSet: Seq[IFormula]): Unit = {
    val SE = IExpression.SymbolEquation(arg)
    for (df <- dataFlowSet) df match {
      case SE(coefficient, rhs) if (!coefficient.isZero) => {
        //draw data flow hyperedge node
        val dataFlowHyperedgeName = dataFlowHyperEdgeNodePrefix + gnn_input.dataFlowHyperEdgeCanonicalID.toString
        matchAndCreateHyperEdgeNode(dataFlowHyperedgeName, "guarded DFHE Clause " + clauseNumber.toString, "dataFlowHyperEdge")
        //astEdgeType = "dataFlowAST"
        astEdgeType = "AST"
//        println("df",df)
//        println("coefficient",coefficient)
//        println("rhs",rhs)
        val dataFlowRoot =
          if (coefficient.isOne)
            drawAST(rhs)
          else if (coefficient > IdealInt(1))
            drawAST(coefficient * rhs)
          else
            drawAST((coefficient * rhs))//.minusSimplify
        //store data flow hyperedge connection
        hyperEdgeList :+= new hyperEdgeInfo(dataFlowHyperedgeName, dataFlowRoot, constantNodeSetInOneClause(arg.toString), HyperEdgeType.dataFlow)
      }
      case _ => {
        //println("debug df",df)
      }
    }
  }

  def getDataFlowAndGuard(clause: Clause):
  (Seq[IFormula], Seq[IFormula], Clause) = {
    /*
    Replace arguments in argumentInHead.intersect(argumentInBody) to arg' and add arg=arg' to constrains

   (1) x = f(\bar y) s.t.

   <1> x is one of the arguments of the clause head
   <2> every element of y occurs as an argument of an uninterpreted predicate in the body
   <3> any variable assignment (assignment of values to the variables occurring in C) that satisfies the constraint of C also satisfies (1).
   */

    val normalizedClause=clause.normalize()
    //replace intersect arguments in body and add arg=arg' to constrains
    val replacedClause = DrawHyperEdgeHornGraph.replaceIntersectArgumentInBody(normalizedClause)
    //val argumentCanonilizedClauses=getArgumentReplacedClause(replacedClause)
    //val simplifiedArgumentCanonilizedClauses=getSimplifiedClauses(argumentCanonilizedClauses)
    val simplifyedClauses=HintsSelection.getSimplifiedClauses(replacedClause) //quantify constraintand
    val finalSimplifiedClauses=simplifyedClauses //change to replacedClause see not simplified constraints

    //var guardList = Set[IFormula]()
    var dataflowList = Set[IFormula]()
    //var dataflowEquationList = Set[IExpression]()
    var bodySymbolsSet = (for (body <- finalSimplifiedClauses.body; arg <- body.args) yield arg).toSet
    //var bodySymbolsSet = bodySymbols.toSet
    //println(Console.GREEN + finalSimplifiedClauses)
    for (x <- finalSimplifiedClauses.head.args) {
      //println(Console.RED + x)
      val SE = IExpression.SymbolEquation(x)
      for (f <- LineariseVisitor(finalSimplifiedClauses.constraint, IBinJunctor.And)) f match {
        case SE(coefficient, rhs) if !coefficient.isZero=> { //<1>
          //println(Console.YELLOW + rhs)
          //println(Console.GREEN + bodySymbolsSet)
          if (!(dataflowList.map(_.toString) contains f.toString) // f is not in dataflowList
            //&& !SymbolCollector.constants(rhs).map(_.toString).contains(x.toString) // x is not in y
            && SymbolCollector.constants(rhs).map(_.toString).subsetOf(bodySymbolsSet.map(_.toString)) // <2>
            //&& (for (s <- SymbolCollector.constants(f)) yield s.name).contains(x.toString)// because match SE will match f that does not have head' arguments, make sure the whole dataflow formula includes x
          ) {
            // discovered dataflow from body to x
            //println(Console.RED + f)
            dataflowList += f //sp(IExpression.Eq(x,rhs))
            //dataflowEquationList += sp(IExpression.Eq(x,coefficient*rhs))
            //bodySymbolsSet += x
          }
        }
        case _ => { //guardList+=f//println(Console.BLUE + f)
        }//guardList+=f
      }
    }

    val guardList = (for (f <- LineariseVisitor(finalSimplifiedClauses.constraint, IBinJunctor.And)) yield f).toSet.diff(for (df <- dataflowList) yield df).map(sp(_))


    val dataFlowSeq = dataflowList.toSeq.sortBy(_.toString)
    val guardSeq = guardList.toSeq.sortBy(_.toString)

    if (GlobalParameters.get.debugLog==true){
      //val dataFlowInfoWriter = new PrintWriter(new File(file + ".HornGraph"))
      val dataFlowInfoWriter = new BufferedWriter(new FileWriter(new File(file + ".HornGraph"), true))
      dataFlowInfoWriter.write("--------------------\n")
      dataFlowInfoWriter.write("original clause:\n")
      dataFlowInfoWriter.write(clause.toPrologString + "\n")
      dataFlowInfoWriter.write("normalized clause:\n")
      dataFlowInfoWriter.write(normalizedClause.toPrologString + "\n")
      dataFlowInfoWriter.write("replaceIntersectArgumentInBody clause:\n")
      dataFlowInfoWriter.write(replacedClause.toPrologString + "\n")
      dataFlowInfoWriter.write("simplified clause:\n")
      dataFlowInfoWriter.write(simplifyedClauses.toPrologString + "\n")
      //    dataFlowInfoWriter.write("argument canonicalized  clauses:\n")
      //    dataFlowInfoWriter.write(argumentCanonilizedClauses.toPrologString + "\n")
      //    dataFlowInfoWriter.write("simplified argument canonilized clauses:\n")
      //    dataFlowInfoWriter.write(simplifiedArgumentCanonilizedClauses.toPrologString + "\n")
      dataFlowInfoWriter.write("dataflow:\n")
      for (df <- dataFlowSeq)
        dataFlowInfoWriter.write(df.toString + "\n")
      dataFlowInfoWriter.write("guard:\n")
      for (g <- guardSeq)
        dataFlowInfoWriter.write(g.toString + "\n")
      //    dataFlowInfoWriter.write("redundant:\n")
      //    for (r <- redundantFormulas)
      //      dataFlowInfoWriter.write(r.toString + "\n")
      dataFlowInfoWriter.close()
    }
    (dataFlowSeq, guardSeq, simplifyedClauses)
  }

  def getArgumentReplacedClause(clause:Clause): Clause ={
    //val subst=(for(const<-clause.constants;atom<-clause.allAtoms;(arg,n)<-atom.args.zipWithIndex; if const.name==arg.toString) yield const->IVariable(n)).toMap

    val subst = (for (atom<-clause.allAtoms;
                     val args = atom.args;
                     val sorts = HornPredAbs predArgumentSorts atom.pred;
                     ((IConstant(arg), s), n) <- (args zip sorts).zipWithIndex)  yield{
          arg -> IVariable(n, s)
    }).toMap

    val substKeyString=subst.map {case (key, value) => key.toString -> value}
    val head=IAtom(clause.head.pred,for(arg<-clause.head.args) yield substKeyString(arg.toString))
    val body = for (b<-clause.body) yield IAtom(b.pred, for(arg<-b.args) yield substKeyString(arg.toString))
    val argumentReplacedConstraint= ConstantSubstVisitor(clause.constraint,subst)
    Clause(head, body, argumentReplacedConstraint)
  }


  def drawTrueGuardCondition(): String ={
    val trueNodeName = "true_" + gnn_input.GNNNodeID.toString
    createNode(trueNodeName, "true", "constant", nodeShapeMap("constant"))
    constantNodeSetCrossGraph("true") = trueNodeName
    constantNodeSetInOneClause("true") = trueNodeName
    drawHyperEdgeWithTrueGuard(trueNodeName)
    trueNodeName
  }


}




