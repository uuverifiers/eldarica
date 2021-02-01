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

import ap.SimpleAPI
import ap.basetypes.IdealInt

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

import scala.collection.mutable.ArrayBuffer
import lazabs.horn.concurrency.DrawHyperEdgeHornGraph.HyperEdgeType
import lazabs.horn.preprocessor.ConstraintSimplifier

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
  val withOutAndConnectionToHyperedge=false
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

  //val sp = new Simplifier()
  val dataFlowInfoWriter = new PrintWriter(new File(file + ".HornGraph"))
  var tempID = 0
  var clauseNumber = 0
  var hyperEdgeList = scala.collection.mutable.ArrayBuffer[hyperEdgeInfo]()
  //for (clause <- Seq(simpClauses.head)) {
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
    var bodyNodeNameList:Array[String]=Array()
    if (normalizedClause.body.isEmpty) {
      //draw predicate node
      val initialControlFlowNodeName = controlNodePrefix + gnn_input.CONTROLCanonicalID.toString
      drawPredicateNode(initialControlFlowNodeName, "Initial", "CONTROL")
      //draw control flow hyperedge node between body and head
      val controlFlowHyperedgeName = controlFlowHyperEdgeNodePrefix + gnn_input.controlFlowHyperEdgeCanonicalID.toString
      matchAndCreateHyperEdgeNode(controlFlowHyperedgeName,"guarded CFHE Clause " + clauseNumber.toString,"controlFlowHyperEdge")
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
          matchAndCreateHyperEdgeNode(controlFlowHyperedgeName,"guarded CFHE Clause " + clauseNumber.toString,"controlFlowHyperEdge")
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
          matchAndCreateHyperEdgeNode(controlFlowHyperedgeName,"guarded CFHE Clause " + clauseNumber.toString,"controlFlowHyperEdge")
          //store control flow hyperedge connection between body and head
          hyperEdgeList :+= new hyperEdgeInfo(controlFlowHyperedgeName, controlFlowNodeSetInOneClause(body.pred.name), controlFlowNodeSetInOneClause(normalizedClause.head.pred.name), HyperEdgeType.controlFlow)
        }
      }
    }
    //draw dataflow
    for (arg <- normalizedClause.head.args)
      drawDataFlow(arg, dataFlowSet)

    var guardRootNodeList:Array[String]=Array()
    if(withOutAndConnectionToHyperedge==true){
      if (guardSet.isEmpty) {
        val trueNodeName = "true_" + gnn_input.GNNNodeID.toString
        guardRootNodeList:+=trueNodeName
        createNode(trueNodeName, "true", "constant", nodeShapeMap("constant"))
        constantNodeSetCrossGraph("true")=trueNodeName
        constantNodeSetInOneClause("true") = trueNodeName
        drawHyperEdgeWithTrueGuard(trueNodeName)
      } else {
        astEdgeType = "guardAST"
        for (guard <- guardSet) {
          val guardRootNodeName = drawAST(guard)
          guardRootNodeList:+=guardRootNodeName
          for (hyperEdgeNode <- hyperEdgeList) {
            hyperEdgeNode.guardName += guardRootNodeName
            if (hyperEdgeNode.guardName.size <= 1) {
              GlobalParameters.get.hornGraphType match {
                case HornGraphType.concretizedHyperedgeGraph=> drawHyperEdge(hyperEdgeNode,guardRootNodeName,addConcretinizedTernaryEdge)
                case HornGraphType.hyperEdgeGraph| HornGraphType.equivalentHyperedgeGraph=> drawHyperEdge(hyperEdgeNode,guardRootNodeName,addTernaryEdge)
              }
            } else
              GlobalParameters.get.hornGraphType match {
                case HornGraphType.concretizedHyperedgeGraph=> drawHyperEdge(hyperEdgeNode,guardRootNodeName,updateConcretinizedTernaryEdge)
                case HornGraphType.hyperEdgeGraph| HornGraphType.equivalentHyperedgeGraph=> drawHyperEdge(hyperEdgeNode,guardRootNodeName,updateTernaryEdge)
              }
          }
        }
      }
    }else{
      if (guardSet.isEmpty) {
        val trueNodeName = "true_" + gnn_input.GNNNodeID.toString
        guardRootNodeList:+=trueNodeName
        createNode(trueNodeName, "true", "constant", nodeShapeMap("constant"))
        constantNodeSetCrossGraph("true")=trueNodeName
        constantNodeSetInOneClause("true") = trueNodeName
        drawHyperEdgeWithTrueGuard(trueNodeName)
      } else if(guardSet.size==1){
        astEdgeType = "guardAST"
        for (guard <- guardSet) {
          val guardRootNodeName = drawAST(guard)
          for (hyperEdgeNode <- hyperEdgeList) {
            hyperEdgeNode.guardName += guardRootNodeName
            GlobalParameters.get.hornGraphType match {
              case HornGraphType.concretizedHyperedgeGraph=> drawHyperEdge(hyperEdgeNode,guardRootNodeName,addConcretinizedTernaryEdge)
              case HornGraphType.hyperEdgeGraph| HornGraphType.equivalentHyperedgeGraph=> drawHyperEdge(hyperEdgeNode,guardRootNodeName,addTernaryEdge)
            }
          }
        }
      }else{
        astEdgeType = "guardAST"
        for (guard <- guardSet) {
          val guardRootNodeName = drawAST(guard)
          guardRootNodeList:+=guardRootNodeName
        }
        val andName = "&" + "_" + gnn_input.GNNNodeID
        createNode(andName, labelName="&", "operator", nodeShapeMap("operator"))
        for(frn<-guardRootNodeList)
          addBinaryEdge(frn,andName,"guardAST",edgeDirectionMap("guardAST"))
        for (hyperEdgeNode <- hyperEdgeList) {
          hyperEdgeNode.guardName += andName
          GlobalParameters.get.hornGraphType match {
            case HornGraphType.concretizedHyperedgeGraph=> drawHyperEdge(hyperEdgeNode,andName,addConcretinizedTernaryEdge)
            case HornGraphType.hyperEdgeGraph| HornGraphType.equivalentHyperedgeGraph=> drawHyperEdge(hyperEdgeNode,andName,addTernaryEdge)
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
  val templateNameList=drawTemplates()
  for ((head,templateNodeNameList)<-templateNameList;templateNodeName<-templateNodeNameList)
    addBinaryEdge(controlFlowNodeSetInOneClause(head),templateNodeName,"template")

  writerGraph.write("}" + "\n")
  writerGraph.close()
  dataFlowInfoWriter.close()

  val (argumentIDList, argumentNameList, argumentOccurrenceList,argumentBoundList,argumentIndicesList,argumentBinaryOccurrenceList) = matchArguments()
  writeGNNInputToJSONFile(argumentIDList, argumentNameList, argumentOccurrenceList,argumentBoundList,argumentIndicesList,argumentBinaryOccurrenceList)

  def matchAndCreateHyperEdgeNode(controlFlowHyperedgeName:String,labelName:String,className:String): Unit ={
    GlobalParameters.get.hornGraphType match {
      case DrawHornGraph.HornGraphType.hyperEdgeGraph => createHyperEdgeNode(controlFlowHyperedgeName, labelName, className, nodeShapeMap(className))
      case DrawHornGraph.HornGraphType.equivalentHyperedgeGraph =>
      case DrawHornGraph.HornGraphType.concretizedHyperedgeGraph=>createConcretinizedHyperEdgeNode(controlFlowHyperedgeName,labelName,className,nodeShapeMap(className))
    }
  }
  def drawHyperEdgeWithTrueGuard(middleNodeName:String): Unit ={
    GlobalParameters.get.hornGraphType match {
      case DrawHornGraph.HornGraphType.equivalentHyperedgeGraph =>{
        for (hyperEdgeNode <- hyperEdgeList) {
          hyperEdgeNode.hyperEdgeType match {
            case HyperEdgeType.controlFlow => {
              addBinaryEdge(hyperEdgeNode.fromName,middleNodeName,label = "controlFlowHyperEdge")
              addBinaryEdge(middleNodeName,hyperEdgeNode.toName,label = "controlFlowHyperEdge")
              addBinaryEdge(hyperEdgeNode.toName,hyperEdgeNode.fromName,label = "controlFlowHyperEdge")
            }
            case HyperEdgeType.dataFlow => {
              addBinaryEdge(hyperEdgeNode.fromName, middleNodeName,label="dataFlowHyperEdge")
              addBinaryEdge(middleNodeName,hyperEdgeNode.toName,label="dataFlowHyperEdge")
              addBinaryEdge(hyperEdgeNode.toName,hyperEdgeNode.fromName,label="dataFlowHyperEdge")
            }
          }
        }
      }
      case DrawHornGraph.HornGraphType.concretizedHyperedgeGraph=>{
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
  }

  def drawHyperEdge(hyperEdgeNode:hyperEdgeInfo,guardRootNodeName:String,f: (String,String,String,String,String) => Unit): Unit ={
    hyperEdgeNode.hyperEdgeType match {
      case HyperEdgeType.controlFlow => {
        GlobalParameters.get.hornGraphType match {
          case DrawHornGraph.HornGraphType.equivalentHyperedgeGraph => {
            addBinaryEdge(hyperEdgeNode.fromName, guardRootNodeName,label="controlFlowHyperEdge")
            addBinaryEdge(guardRootNodeName,hyperEdgeNode.toName,label="controlFlowHyperEdge")
            addBinaryEdge(hyperEdgeNode.toName,hyperEdgeNode.fromName,label="controlFlowHyperEdge")
          }
          //case DrawHornGraph.HornGraphType.concretizedHyperedgeGraph=> addConcretinizedTernaryEdge(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "controlFlowHyperEdge")
          case DrawHornGraph.HornGraphType.hyperEdgeGraph |DrawHornGraph.HornGraphType.concretizedHyperedgeGraph => f(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "controlFlowHyperEdge")
        }
      }
      case HyperEdgeType.dataFlow => {
        GlobalParameters.get.hornGraphType match {
          case DrawHornGraph.HornGraphType.equivalentHyperedgeGraph => {
            addBinaryEdge(hyperEdgeNode.fromName, guardRootNodeName,label="dataFlowHyperEdge")
            addBinaryEdge(guardRootNodeName,hyperEdgeNode.toName,label="dataFlowHyperEdge")
            addBinaryEdge(hyperEdgeNode.toName,hyperEdgeNode.fromName,label="dataFlowHyperEdge")
          }
          //case DrawHornGraph.HornGraphType.concretizedHyperedgeGraph=> addConcretinizedTernaryEdge(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "dataFlowHyperEdge")
          case DrawHornGraph.HornGraphType.hyperEdgeGraph | DrawHornGraph.HornGraphType.concretizedHyperedgeGraph=>  f(hyperEdgeNode.fromName, guardRootNodeName, hyperEdgeNode.toName, hyperEdgeNode.hyperEdgeNodeName, "dataFlowHyperEdge")
        }
      }
    }
  }

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
        matchAndCreateHyperEdgeNode(dataFlowHyperedgeName,"guarded DFHE Clause " + clauseNumber.toString,"dataFlowHyperEdge")
        astEdgeType = "dataFlowAST"
        val dataFlowRoot=
        if (coefficient.isOne)
          drawAST(rhs)
        else if(coefficient>IdealInt(1))
          drawAST(rhs*coefficient)
        else
          drawAST((coefficient*rhs).minusSimplify)
        //store data flow hyperedge connection
        hyperEdgeList :+= new hyperEdgeInfo(dataFlowHyperedgeName, dataFlowRoot, constantNodeSetInOneClause(arg.toString), HyperEdgeType.dataFlow)
      }
      case _ => {}
    }
  }


  def getDataFlowAndGuard(clause: Clause, normalizedClause: Clause, dataFlowInfoWriter: PrintWriter): (Set[IExpression], Set[IFormula],Clause) = {
    /*
    Replace arguments in argumentInHead.intersect(argumentInBody) to arg' and add arg=arg' to constrains

   (1) x = f(\bar y) s.t.

   <1> x is one of the arguments of the clause head
   <2> every element of y occurs as an argument of an uninterpreted predicate in the body
   <3> any variable assignment (assignment of values to the variables occurring in C) that satisfies the constraint of C also satisfies (1).
   */
    //replace intersect arguments in body and add arg=arg' to constrains
    val replacedClause=DrawHyperEdgeHornGraph.replaceIntersectArgumentInBody(normalizedClause)
    var dataflowList = Set[IExpression]()
    var dataflowEquationList=Set[IExpression]()
    var bodySymbolsSet = (for (body <- replacedClause.body; arg <- body.args) yield arg).toSet
    //var bodySymbolsSet = bodySymbols.toSet
    //println(Console.GREEN + replacedClause)
    for (x <- replacedClause.head.args) {
      //println(Console.RED + x)
      val SE = IExpression.SymbolEquation(x)
      for (f <- LineariseVisitor(replacedClause.constraint, IBinJunctor.And)) f match {
        case SE(coefficient, rhs) => { //<1>
          //println(Console.YELLOW + rhs)
          //println(Console.GREEN + bodySymbolsSet)
          if (!(dataflowList contains f) // f is not in dataflowList
            //&& !SymbolCollector.constants(rhs).map(_.toString).contains(x.toString) // x is not in y
            && SymbolCollector.constants(rhs).map(_.toString).subsetOf(bodySymbolsSet.map(_.toString)) // <2>
            //&& (for (s <- SymbolCollector.constants(f)) yield s.name).contains(x.toString)// because match SE will match f that does not have head' arguments
          ) {
            // discovered dataflow from body to x
            //println(Console.RED + f)
            dataflowList += f //sp(IExpression.Eq(x,rhs))
            //dataflowEquationList += sp(IExpression.Eq(x,coefficient*rhs))
            //bodySymbolsSet += x
          }
        }
        case _ => { //println(Console.BLUE + f)//guardList+=f}
        }
      }
    }
    val guardList = (for (f <- LineariseVisitor(replacedClause.constraint, IBinJunctor.And)) yield f).toSet.diff(for (df <- dataflowList) yield df.asInstanceOf[IFormula]).map(sp(_))

    //todo: delete some redundant predicates
//    val redundantFormulas = for(g<-guardList if SymbolCollector.constants(g).map(_.toString).toSet.diff(replacedClause.head.args.map(_.toString).toSet).intersect(bodySymbolsSet.map(_.toString)).isEmpty) yield {
//      g
//    }

    dataFlowInfoWriter.write("--------------------\n")
    dataFlowInfoWriter.write("original clause:\n")
    dataFlowInfoWriter.write(clause.toPrologString + "\n")
    dataFlowInfoWriter.write("normalized and replaced clause:\n")
    dataFlowInfoWriter.write(replacedClause.toPrologString + "\n")
    dataFlowInfoWriter.write("dataflow:\n")
    for (df <- dataflowList)
      dataFlowInfoWriter.write(df.toString + "\n")
    dataFlowInfoWriter.write("guard:\n")
    for (g <- guardList)
      dataFlowInfoWriter.write(g.toString + "\n")
//    dataFlowInfoWriter.write("redundant:\n")
//    for (r <- redundantFormulas)
//      dataFlowInfoWriter.write(r.toString + "\n")
    (dataflowList, guardList,replacedClause)
  }

}
