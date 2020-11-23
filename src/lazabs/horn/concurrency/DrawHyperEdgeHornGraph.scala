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

import java.io.{File, PrintWriter}

import ap.parser.IExpression.{ConstantTerm, Eq, Predicate}
import ap.parser.{IAtom, IBinJunctor, IConstant, IExpression, IFormula, ITerm, IVariable, LineariseVisitor, Simplifier, SymbolCollector}
import ap.types.Sort.Integer.newConstant
import jdk.nashorn.internal.objects.Global
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints.VerifHintInitPred
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.concurrency.DrawHornGraph.HornGraphType
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}

import scala.collection.mutable.ListBuffer
import lazabs.horn.concurrency.DrawHyperEdgeHornGraph.HyperEdgeType

object DrawHyperEdgeHornGraph {

  object HyperEdgeType extends Enumeration {
    val controlFlow, dataFlow = Value
  }

}

class hyperEdgeInfo(name: String, from: String = "", to: String, nodeType: HyperEdgeType.Value) {
  val hyperEdgeNodeName = name
  val fromName = from
  var guardName = Set[String]()
  val toName = to
  val hyperEdgeType = nodeType
}

class DrawHyperEdgeHornGraph(file: String, clausesCollection: ClauseInfo, hints: VerificationHintsInfo, argumentInfoList: ListBuffer[argumentInfo]) extends DrawHornGraph(file: String, clausesCollection: ClauseInfo, hints: VerificationHintsInfo, argumentInfoList: ListBuffer[argumentInfo]) {
  println("Write hyperedge horn graph to file")
  edgeNameMap += ("controlFlowHyperEdge" -> "CFHE")
  edgeNameMap += ("dataFlowHyperEdge" -> "DFHE")
  edgeNameMap += ("dataFlowAST" -> "data")
  edgeNameMap += ("guardAST" -> "guard")
  edgeNameMap += ("argument" -> "arg")
  edgeNameMap += ("clause" -> "clause")
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

  val sp = new Simplifier()
  val dataFlowInfoWriter = new PrintWriter(new File(file + ".HornGraph"))
  var tempID = 0
  var clauseNumber = 0
  var hyperEdgeList = scala.collection.mutable.ListBuffer[hyperEdgeInfo]()


  def drawArgumentNodeForPredicate(pre:IAtom,controlFlowNodeName:String): Unit ={
    var argumentNodeArray = Array[String]()
    tempID = 0
    for (arg <- pre.args) {
      val argumentnodeName = argumentNodePrefix + gnn_input.predicateArgumentCanonicalID.toString
      createNode(argumentnodeName, "ARG_" + tempID.toString, "predicateArgument", nodeShapeMap("predicateArgument"))
      constantNodeSetInOneClause(arg.toString) = argumentnodeName
      argumentNodeArray :+= argumentnodeName
      updateArgumentInfoHornGraphList(pre.pred.name,tempID,argumentnodeName,arg)
      tempID += 1
      //connect to control flow node
      addBinaryEdge(argumentnodeName, controlFlowNodeName, "argument")
    }
    argumentNodeSetInOneClause(pre.pred.name) = argumentNodeArray
  }

  for (clause <- simpClauses) {
    hyperEdgeList.clear()
    constantNodeSetInOneClause.clear()
    val (dataFlowSet, guardSet,normalizedClause) = getDataFlowAndGuard(clause, clause.normalize(), dataFlowInfoWriter)

    //draw head predicate node and argument node
    val headNodeName=
    if (normalizedClause.head.pred.name == "FALSE") {
      //draw predicate node
      drawPredicateNode("FALSE", "FALSE", "FALSE")
      "FALSE"
    } else {
      if (!controlFlowNodeSetInOneClause.keySet.contains(normalizedClause.head.pred.name)) {
        //draw predicate node
        val controlFlowNodeName = controlNodePrefix + gnn_input.CONTROLCanonicalID.toString
        drawPredicateNode(controlFlowNodeName, normalizedClause.head.pred.name, "CONTROL")
        //draw argument node
        drawArgumentNodeForPredicate(normalizedClause.head,controlFlowNodeName)
        controlFlowNodeName

      } else{
        for (controlNodeName <- argumentNodeSetInOneClause.keySet) if (controlNodeName == normalizedClause.head.pred.name) {
          for ((argNodeName, arg) <- argumentNodeSetInOneClause(controlNodeName) zip normalizedClause.head.args) {
            constantNodeSetInOneClause(arg.toString) = argNodeName
          }
        }
        controlFlowNodeSetInOneClause(normalizedClause.head.pred.name)
      }
    }


    //draw body predicate node and argument node
    var bodyNodeNameList:List[String]=List()
    if (normalizedClause.body.isEmpty) {
      //draw predicate node
      val initialControlFlowNodeName = controlNodePrefix + gnn_input.CONTROLCanonicalID.toString
      drawPredicateNode(initialControlFlowNodeName, "Initial", "CONTROL")
      //draw control flow hyperedge node between body and head
      val controlFlowHyperedgeName = controlFlowHyperEdgeNodePrefix + gnn_input.controlFlowHyperEdgeCanonicalID.toString
      createHyperEdgeNode(controlFlowHyperedgeName, "guarded CFHE Clause " + clauseNumber.toString, "controlFlowHyperEdge", nodeShapeMap("controlFlowHyperEdge"))
      //store control flow hyperedge connection between body and head
      hyperEdgeList :+= new hyperEdgeInfo(controlFlowHyperedgeName, initialControlFlowNodeName, controlFlowNodeSetInOneClause(normalizedClause.head.pred.name), HyperEdgeType.controlFlow)
      bodyNodeNameList:+=initialControlFlowNodeName
    } else {
      for (body <- normalizedClause.body) {
        if (!controlFlowNodeSetInOneClause.keySet.contains(body.pred.name)) {
          //draw predicate node
          val controlFlowNodeName = controlNodePrefix + gnn_input.CONTROLCanonicalID.toString
          bodyNodeNameList:+=controlFlowNodeName
          drawPredicateNode(controlFlowNodeName, body.pred.name, "CONTROL")
          //draw control flow hyperedge node between body and head
          val controlFlowHyperedgeName = controlFlowHyperEdgeNodePrefix + gnn_input.controlFlowHyperEdgeCanonicalID.toString
          createHyperEdgeNode(controlFlowHyperedgeName, "guarded CFHE Clause " + clauseNumber.toString, "controlFlowHyperEdge", nodeShapeMap("controlFlowHyperEdge"))
          //store control flow hyperedge connection between body and head
          hyperEdgeList :+= new hyperEdgeInfo(controlFlowHyperedgeName, controlFlowNodeName, controlFlowNodeSetInOneClause(normalizedClause.head.pred.name), HyperEdgeType.controlFlow)
          //draw argument node
          drawArgumentNodeForPredicate(body,controlFlowNodeName)
        } else {
          for (controlNodeName <- argumentNodeSetInOneClause.keySet) if (controlNodeName == body.pred.name) {
            for ((argNodeName, arg) <- argumentNodeSetInOneClause(controlNodeName) zip body.args) {
              constantNodeSetInOneClause(arg.toString) = argNodeName
            }
            bodyNodeNameList:+=controlFlowNodeSetInOneClause(controlNodeName)
          }
          //draw control flow hyperedge node between body and head
          val controlFlowHyperedgeName = controlFlowHyperEdgeNodePrefix + gnn_input.controlFlowHyperEdgeCanonicalID.toString
          createHyperEdgeNode(controlFlowHyperedgeName, "guarded CFHE Clause " + clauseNumber.toString, "controlFlowHyperEdge", nodeShapeMap("controlFlowHyperEdge"))
          //store control flow hyperedge connection between body and head
          hyperEdgeList :+= new hyperEdgeInfo(controlFlowHyperedgeName, controlFlowNodeSetInOneClause(body.pred.name), controlFlowNodeSetInOneClause(normalizedClause.head.pred.name), HyperEdgeType.controlFlow)
        }
      }
    }
    //draw dataflow
    for (arg <- normalizedClause.head.args)
      drawDataFlow(arg, dataFlowSet)

    var guardRootNodeList:List[String]=List()
    if (guardSet.isEmpty) {
      val trueNodeName = "true_" + gnn_input.GNNNodeID.toString
      guardRootNodeList:+=trueNodeName
      createNode(trueNodeName, "true", "constant", nodeShapeMap("constant"))
      constantNodeSetInOneClause("true") = trueNodeName
      for (hyperEdgeNode <- hyperEdgeList) {
        hyperEdgeNode.hyperEdgeType match {
          case HyperEdgeType.controlFlow => addTernaryEdge(hyperEdgeNode.fromName, trueNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "controlFlowHyperEdge")
          case HyperEdgeType.dataFlow => addTernaryEdge(hyperEdgeNode.fromName, trueNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "dataFlowHyperEdge")
        }
      }
    } else {
      astEdgeType = "guardAST"
      for (guard <- guardSet) {
        val guardRootNodeName = drawAST(guard)
        guardRootNodeList:+=guardRootNodeName
        for (hyperEdgeNode <- hyperEdgeList) {
          hyperEdgeNode.guardName += guardRootNodeName
          if (hyperEdgeNode.guardName.size <= 1) {
            hyperEdgeNode.hyperEdgeType match {
              case HyperEdgeType.controlFlow => addTernaryEdge(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "controlFlowHyperEdge")
              case HyperEdgeType.dataFlow => addTernaryEdge(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "dataFlowHyperEdge")
            }
          } else {
            hyperEdgeNode.hyperEdgeType match {
              case HyperEdgeType.controlFlow => updateTernaryEdge(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "controlFlowHyperEdge")
              case HyperEdgeType.dataFlow => updateTernaryEdge(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "dataFlowHyperEdge")
            }
          }
        }
      }
    }
    if(GlobalParameters.get.getLabelFromCounterExample==true){
      //create clause node and connect with guards
      val clauseNodeName = clauseNodePrefix + gnn_input.clauseCanonicalID.toString
      createNode(clauseNodeName,clauseNodeName,"clause",nodeShapeMap("clause"),Seq(clause))
      //add edges to the clause
      for (guardRootNode<-guardRootNodeList) { //from guards to clause
        addBinaryEdge(guardRootNode,clauseNodeName,"guardAST")
      }
      addBinaryEdge(clauseNodeName,headNodeName,label="clause") //from clause to head
      for (bodyNodeName<-bodyNodeNameList) //from body to clause
        addBinaryEdge(bodyNodeName,clauseNodeName,"clause")
    }
    clauseNumber += 1
  }
  //draw templates
  for (argInfo<-gnn_input.argumentInfoHornGraphList){
    argumentNodeSetInPredicates("_"+argInfo.index.toString)=argInfo.canonicalName //add _ to differentiate index with other constants
  }
  astEdgeType = "templateAST"
  for(p<-HornClauses.allPredicates(simpClauses)){
    val templateNameList=drawTemplates(p)
    for (templateNodeName<-templateNameList)
      addBinaryEdge(controlFlowNodeSetInOneClause(p.name),templateNodeName,"template")
  }

  writerGraph.write("}" + "\n")
  writerGraph.close()
  dataFlowInfoWriter.close()

  val (argumentIDList, argumentNameList, argumentOccurrenceList,argumentBoundList,argumentIndicesList,argumentBinaryOccurrenceList) = matchArguments()
  writeGNNInputToJSONFile(argumentIDList, argumentNameList, argumentOccurrenceList,argumentBoundList,argumentIndicesList,argumentBinaryOccurrenceList)


  def drawPredicateNode(controlFlowNodeName: String, predicateName: String, className: String): Unit = {
    //draw predicate node
    createNode(controlFlowNodeName, predicateName, className, nodeShapeMap(className))
    controlFlowNodeSetInOneClause(predicateName) = controlFlowNodeName
  }

  def drawDataFlow(arg: ITerm, dataFlowSet: Set[IExpression]): Unit = {
    val SE = IExpression.SymbolEquation(arg)
    for (df <- dataFlowSet) df match {
      case SE(coefficient, rhs) if (!coefficient.isZero) => {
        //draw data flow hyperedge node
        val dataFlowHyperedgeName = dataFlowHyperEdgeNodePrefix + gnn_input.dataFlowHyperEdgeCanonicalID.toString
        createHyperEdgeNode(dataFlowHyperedgeName, "guarded DFHE Clause " + clauseNumber.toString, "dataFlowHyperEdge", nodeShapeMap("dataFlowHyperEdge"))
        astEdgeType = "dataFlowAST"
        val dataFlowRoot = drawAST(rhs)
        //store data flow hyperedge connection
        hyperEdgeList :+= new hyperEdgeInfo(dataFlowHyperedgeName, dataFlowRoot, constantNodeSetInOneClause(arg.toString), HyperEdgeType.dataFlow)
      }
      case _ => {}
    }
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

  def getDataFlowAndGuard(clause: Clause, normalizedClause: Clause, dataFlowInfoWriter: PrintWriter): (Set[IExpression], Set[IFormula],Clause) = {
    /*
    Replace arguments in argumentInHead.intersect(argumentInBody) to arg' and add arg=arg' to constrains

   (1) x = f(\bar y) s.t.

   <1> x is one of the arguments of the clause head
   <2> \bar y are arguments of the literals in the clause body.
   <3> any variable assignment (assignment of values to the variables occurring in C) that satisfies the constraint of C also satisfies (1).
   */
    //replace intersect arguments in body and add arg=arg' to constrains
    val replacedClause=replaceIntersectArgumentInBody(normalizedClause)
    var dataflowList = Set[IExpression]()
    var dataflowListHeadArgSymbolEquation = Set[IExpression]()
    val bodySymbols = for (body <- replacedClause.body; arg <- body.args) yield new ConstantTerm(arg.toString)
    var bodySymbolsSet = bodySymbols.toSet
    for (x <- replacedClause.head.args) {
      val SE = IExpression.SymbolEquation(x)
      val constantTermX = new ConstantTerm(x.toString)
      for (f <- LineariseVisitor(replacedClause.constraint, IBinJunctor.And)) f match {
        case SE(coefficient, rhs) => {
          if (!(dataflowList contains f) && !(bodySymbolsSet contains constantTermX) && !SymbolCollector.constants(rhs).isEmpty
            && !(for (s <- SymbolCollector.constants(rhs)) yield s.name).intersect(for (s <- bodySymbolsSet) yield s.name).isEmpty
            && (for (s <- SymbolCollector.constants(f)) yield s.name).contains(x.toString)) {
            // discovered data-flow from body to x!
            dataflowList += f //sp(IExpression.Eq(x,rhs))
            dataflowListHeadArgSymbolEquation += sp(IExpression.Eq(x, rhs))
            bodySymbolsSet += constantTermX
          }
        }
        case _ => { //guardList+=f}
        }
      }
    }
    val guardList = (for (f <- LineariseVisitor(replacedClause.constraint, IBinJunctor.And)) yield f).toSet.diff(for (df <- dataflowList) yield df.asInstanceOf[IFormula])
    dataFlowInfoWriter.write("--------------------\n")
    dataFlowInfoWriter.write("original clause:\n")
    dataFlowInfoWriter.write(clause.toPrologString + "\n")
    dataFlowInfoWriter.write("normalized and replaced clause:\n")
    dataFlowInfoWriter.write(replacedClause.toPrologString + "\n")
    dataFlowInfoWriter.write("dataflow:\n")
    for (df <- dataflowListHeadArgSymbolEquation)
      dataFlowInfoWriter.write(df.toString + "\n")
    dataFlowInfoWriter.write("guard:\n")
    for (g <- guardList)
      dataFlowInfoWriter.write(g.toString + "\n")
    (dataflowListHeadArgSymbolEquation, guardList,replacedClause)
  }

}
