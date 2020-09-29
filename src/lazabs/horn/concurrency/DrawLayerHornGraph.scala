/**
 * Copyright (c) 2011-2020 Philipp Ruemmer, Chencheng Liang All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
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

import ap.parser.IExpression.{Conj, Const, Difference, Disj, Eq, EqLit, EqZ, Geq, GeqZ, LeafFormula, SignConst, SimpleTerm}
import ap.parser.{IAtom, IBinFormula, IBinJunctor, IBoolLit, IConstant, IEpsilon, IExpression, IFormulaITE, IFunApp, IIntFormula, IIntLit, INamedPart, INot, IPlus, IQuantified, ITermITE, ITimes, ITrigger, IVariable, LineariseVisitor}
import lazabs.GlobalParameters

import scala.collection.mutable.{ListBuffer, HashMap => MHashMap, Map => MuMap}
import lazabs.horn.concurrency.DrawHornGraph.{GNNInput, addQuotes, argumentInfoHronGraph}
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import play.api.libs.json.Json

import scala.collection.mutable.ListBuffer

class DrawLayerHornGraph(file: String, simpClauses: Clauses,hints:VerificationHints,argumentInfoList:ListBuffer[argumentInfo]) {
  val useDotLib=false
  val dot = new Digraph(comment = "Horn Graph")
  val gnn_input=new GNNInput()

  val writerGraph = new PrintWriter(new File(file + ".layerHornGraph.gv"))
  writerGraph.write("digraph dag {" + "\n")

  println("Write layer horn graph to file")
  var edgeNameMap: Map[String, String] = Map()
  edgeNameMap += ("predicateArgument" -> "PA")
  edgeNameMap += ("predicateInstance" -> "PI")
  edgeNameMap += ("argumentInstance" -> "AI")
  edgeNameMap += ("controlHead" -> "CH")
  edgeNameMap += ("controlBody" -> "CB")
  edgeNameMap += ("controlArgument" -> "ARG")
  edgeNameMap += ("guard" -> "guard")
  edgeNameMap += ("data" -> "data")
  edgeNameMap += ("subTerm" -> "st")

  //turn on/off edge's label
  var edgeNameSwitch = true
  if (edgeNameSwitch == false) {
    for (key <- edgeNameMap.keys)
      edgeNameMap += (key -> "")
  }

  var shapeMap: Map[String, String] = Map()
  shapeMap += ("constant" -> "circle")
  shapeMap += ("operator" -> "square")
  shapeMap += ("predicateArgument" -> "ellipse")
  shapeMap += ("clause" -> "box")
  shapeMap += ("clauseHead" -> "box")
  shapeMap += ("clauseBody" -> "box")
  shapeMap += ("clauseArgument" -> "ellipse")
  shapeMap += ("symbolicConstant" -> "circle")
  //node cotegory: Operator and Constant don't need canonical name. FALSE is unique category
  //  var predicateNumber,predicateArgumentNumber=1
  //  var clauseNumber,clauseHeadNumber,clauseBodyNumber,clauseArgumentNumber=1;
  //  var symbolicConstantNumber=1
  val predicateNamePrefix="predicate_"
  val predicateArgumentPrefix="predicateArgument_"
  val clausePrefix="clause_"
  val clauseHeadPrefix="clauseHead_"
  val clauseBodyPrefix="clauseBody_"
  val clauseArgumentPrefix="clauseArgument_"
  val symbolicConstantPrefix="symbolicConstant_"

  var predicateNameMap = Map[String,predicateInfo]() //original name -> canonical name
  class predicateInfo(predicateName:String){
    val predicateCanonicalName=predicateName
    var argumentCanonicalNameList= new ListBuffer[Pair[String,Int]]() //(canonicalName, ID)
  }

  for (clause <- simpClauses) {
    //predicate layer: create predicate and arguments and edges between them
    createPredicateLayerNodesAndEdges(clause.head)
    for (bodyPredicate<-clause.body){
      //predicate layer: create predicate and arguments and edges between them
      createPredicateLayerNodesAndEdges(bodyPredicate)
    }
  }

  for (clause <- simpClauses) {
    //clause layer: create clause node
    val clauseNodeName= clausePrefix+gnn_input.clauseCanonicalID.toString
    createNode(clauseNodeName,
      "C"+gnn_input.clauseCanonicalID.toString,"clause","box",gnn_input.GNNNodeID)
    //draw constraints and connect to clause node
    for (conjunct <- LineariseVisitor(clause.constraint, IBinJunctor.And)){
      drawAST(conjunct,clauseNodeName)
    }


    //clause layer: create clause head node
    val clauseHeadNodeName = clauseHeadPrefix+gnn_input.clauseHeadCanonicalID.toString
    createNode(clauseHeadNodeName,
      "HEAD","clauseHead","box",gnn_input.GNNNodeID)
    //clause layer: create edge between head and clause node
    addEdge(clauseNodeName,clauseHeadNodeName,"controlHead")
    //predicateLayer->clauseLayer: connect predicate to clause head
    addEdge(predicateNameMap(clause.head.pred.name).predicateCanonicalName,clauseHeadNodeName,"predicateInstance")
    var tempIDForArgument=0
    for ((headArgument,predicateArgument)<-clause.head.args zip predicateNameMap(clause.head.pred.name).argumentCanonicalNameList){
      //clause layer: create clause head argument node
      val clauseArgumentNodeName = clauseArgumentPrefix+gnn_input.clauseArgCanonicalID.toString
      createNode(clauseArgumentNodeName,
        "ARG"+tempIDForArgument.toString,"clauseArg","ellipse",gnn_input.GNNNodeID)
      //clause layer: create edge between head and argument
      addEdge(clauseHeadNodeName,clauseArgumentNodeName,"controlArgument")
      //predicateLayer->clauseLayer: connect predicate argument to clause argument
      addEdge(predicateArgument._1,clauseArgumentNodeName,"argumentInstance")
      drawAST(headArgument,clauseArgumentNodeName)
      tempIDForArgument+=1
    }


    //clause layer: create clause arguments node in body
    var tempIDForPredicate=0
    for (bodyPredicate<-clause.body){
      //clause layer: create clause body node
      val clauseBodyNodeName=clauseBodyPrefix+gnn_input.clauseBodyCanonicalID.toString
      createNode(clauseBodyNodeName,
        "BODY"+tempIDForPredicate.toString,"clauseBody","box",gnn_input.GNNNodeID)
      tempIDForPredicate+=1
      //clause layer: create edge between body and clause node
      addEdge(clauseNodeName,clauseBodyNodeName,"controlBody")
      //predicateLayer->clauseLayer: connect predicate to clause body
      addEdge(predicateNameMap(bodyPredicate.pred.name).predicateCanonicalName,clauseBodyNodeName,"predicateInstance")

      tempIDForArgument=0
      for ((bodyArgument,predicateArgument)<-bodyPredicate.args zip predicateNameMap(bodyPredicate.pred.name).argumentCanonicalNameList){
        //clause layer: create clause body argument node
        val clauseArgumentNodeName=clauseArgumentPrefix+gnn_input.clauseArgCanonicalID.toString
        createNode(clauseArgumentNodeName,
          "ARG"+tempIDForArgument.toString,"clauseArg","ellipse",gnn_input.GNNNodeID)
        //clause layer: create edge between body and argument
        addEdge(clauseBodyNodeName,clauseArgumentNodeName,"controlArgument")
        //predicateLayer->clauseLayer: connect predicate argument to clause argument
        addEdge(predicateArgument._1,clauseArgumentNodeName,"argumentInstance")
        tempIDForArgument+=1
        drawAST(bodyArgument,clauseArgumentNodeName)
      }
    }

  }

  //match by argument name
  for(argHornGraph<-gnn_input.argumentInfoHornGraphList;arg<-argumentInfoList) {
    if(arg.headName==argHornGraph.head && arg.index == argHornGraph.index) {
      argHornGraph.score=arg.score
      argHornGraph.ID=arg.ID
    }
  }
  val argumentIDList = for (argHornGraph<-gnn_input.argumentInfoHornGraphList) yield argHornGraph.ID
  val argumentNameList = for (argHornGraph<-gnn_input.argumentInfoHornGraphList) yield argHornGraph.head+":"+argHornGraph.name
  val argumentOccurrenceList = for (argHornGraph<-gnn_input.argumentInfoHornGraphList) yield argHornGraph.score

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


  //direct write to JSON file
  println("Write GNNInput to file")
  var lastFiledFlag=false
  val writer = new PrintWriter(new File(file + ".layerHornGraph.JSON"))
  writer.write("{")
  writeGNNInputToJSONFile("nodeIds",IntArray(gnn_input.nodeIds),writer)
  writeGNNInputToJSONFile("nodeSymbolList",StringArray(gnn_input.nodeSymbols),writer)
  writeGNNInputToJSONFile("argumentIndices",IntArray(gnn_input.argumentIndices),writer)
  writeGNNInputToJSONFile("binaryAdjacentList",PairArray(gnn_input.binaryAdjacency.binaryEdge),writer)
  writeGNNInputToJSONFile("ternaryAdjacencyList",TripleArray(gnn_input.ternaryAdjacency.ternaryEdge),writer)
  writeGNNInputToJSONFile("predicateArgumentEdges",PairArray(gnn_input.predicateArgumentEdges.binaryEdge),writer)
  writeGNNInputToJSONFile("predicateInstanceEdges",PairArray(gnn_input.predicateInstanceEdges.binaryEdge),writer)
  writeGNNInputToJSONFile("argumentInstanceEdges",PairArray(gnn_input.argumentInstanceEdges.binaryEdge),writer)
  writeGNNInputToJSONFile("controlHeadEdges",PairArray(gnn_input.controlHeadEdges.binaryEdge),writer)
  writeGNNInputToJSONFile("controlBodyEdges",PairArray(gnn_input.controlBodyEdges.binaryEdge),writer)
  writeGNNInputToJSONFile("controlArgumentEdges",PairArray(gnn_input.controlArgumentEdges.binaryEdge),writer)
  writeGNNInputToJSONFile("guardEdges",PairArray(gnn_input.guardEdges.binaryEdge),writer)
  writeGNNInputToJSONFile("dataEdges",PairArray(gnn_input.dataEdges.binaryEdge),writer)
  writeGNNInputToJSONFile("unknownEdges",PairArray(gnn_input.unknownEdges.binaryEdge),writer)
  writeGNNInputToJSONFile("argumentIDList",IntArray(argumentIDList.toArray),writer)
  writeGNNInputToJSONFile("argumentNameList",StringArray(argumentNameList.toArray),writer)
  lastFiledFlag=true
  writeGNNInputToJSONFile("argumentOccurrence",IntArray(argumentOccurrenceList.toArray),writer)
  writer.write("}")
  writer.close()
  def writeGNNInputToJSONFile(fieldName:String,fiedlContent:Arrays,writer:PrintWriter): Unit ={
    fiedlContent match {
      case StringArray(x)=>{writeOneField(fieldName,x,writer)}
      case IntArray(x)=>{writeOneField(fieldName,x,writer)}
      case PairArray(x)=>{writeOneField(fieldName,x,writer)}
      case TripleArray(x)=>writeOneField(fieldName,x,writer)
    }
    if (lastFiledFlag==false)
      writer.write(",\n")
    else
      writer.write("\n")
  }
  sealed abstract class Arrays
  case class StringArray(x:Array[String]) extends Arrays
  case class IntArray(x:Array[Int]) extends Arrays
  case class PairArray(x:Array[Pair[Int,Int]]) extends Arrays
  case class TripleArray(x:Array[Triple[Int,Int,Int]]) extends Arrays

  def writeOneField(fieldName:String,fiedlContent:Array[Pair[Int,Int]],writer:PrintWriter): Unit ={
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize=fiedlContent.size-1
    for ((p,i)<-fiedlContent.zipWithIndex){
      writer.write("[")
      writer.write(p._1.toString)
      writer.write(",")
      writer.write(p._2.toString)
      writer.write("]")
      if (i<filedSize)
        writer.write(",")
    }
    writer.write("]")
  }
  def writeOneField(fieldName:String,fiedlContent:Array[Triple[Int,Int,Int]],writer:PrintWriter): Unit ={
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize=fiedlContent.size-1
    for ((p,i)<-fiedlContent.zipWithIndex){
      writer.write("[")
      writer.write(p._1.toString)
      writer.write(",")
      writer.write(p._2.toString)
      writer.write(",")
      writer.write(p._3.toString)
      writer.write("]")
      if (i<filedSize)
        writer.write(",")
    }
    writer.write("]")
  }

  def writeOneField(fieldName:String,fiedlContent:Array[Int],writer:PrintWriter): Unit ={
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize=fiedlContent.size-1
    for ((p,i)<-fiedlContent.zipWithIndex){
      writer.write(p.toString)
      if (i<filedSize)
        writer.write(",")
    }
    writer.write("]")
  }
  def writeOneField(fieldName:String,fiedlContent:Array[String],writer:PrintWriter): Unit ={
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize=fiedlContent.size-1
    for ((p,i)<-fiedlContent.zipWithIndex){
      writer.write(addQuotes(p.toString))
      if (i<filedSize)
        writer.write(",")
    }
    writer.write("]")
  }


  //write dot file
  if (useDotLib==true){
    val filePath=file.substring(0,file.lastIndexOf("/")+1)
    val fileName=file.substring(file.lastIndexOf("/")+1,file.size)
    dot.save(fileName = fileName+".layerHornGraph.gv", directory = filePath)
  }


  def createNode(canonicalName:String,labelName:String,className:String,shape:String,GNNNodeID:Int): Unit ={
    if (useDotLib==true)
      dot.node(addQuotes(canonicalName), label = addQuotes(labelName),
        attrs = MuMap("nodeName"->addQuotes(canonicalName),
          "shape"->addQuotes(shape),"class"->className,"GNNNodeID"->GNNNodeID.toString))

    writerGraph.write(addQuotes(canonicalName) +
      " [label="+addQuotes(labelName)+" nodeName="+addQuotes(canonicalName)+" class="+className +" shape="+ addQuotes(shape) + "];" + "\n")
    if (className=="predicateArgument"){
      gnn_input.incrementArgumentIndicesAndNodeIds(canonicalName,className,labelName)
    }else{
      gnn_input.incrementNodeIds(canonicalName,className,labelName)
    }
  }
  def addEdge(from:String,to:String,label:String): Unit ={
    if (useDotLib==true)
      dot.edge(addQuotes(from),addQuotes(to),attrs = MuMap("label"->addQuotes(edgeNameMap(label))))
    writerGraph.write(addQuotes(from)+ " -> " + addQuotes(to) +
      " [label=" + addQuotes(edgeNameMap(label)) + "]" + "\n")
    gnn_input.incrementBinaryEdge(from, to,label)
  }

  def createPredicateLayerNodesAndEdges(pred:IAtom): Unit ={
    //predicate layer: create predicate and argument node
    if (!predicateNameMap.contains(pred.pred.name)){
      val predicateNodeCanonicalName=predicateNamePrefix+gnn_input.predicateNameCanonicalID.toString
      predicateNameMap+=(pred.pred.name->new predicateInfo(predicateNodeCanonicalName))
      createNode(predicateNodeCanonicalName,
        pred.pred.name,"predicateName","box",gnn_input.GNNNodeID)
      var tempID=0
      for (headArg<-pred.args){
        val argumentNodeCanonicalName=predicateArgumentPrefix+gnn_input.predicateArgumentCanonicalID.toString
        //create argument node
        createNode(argumentNodeCanonicalName,
          "Arg"+tempID.toString,"predicateArgument","ellipse",gnn_input.GNNNodeID)
        //create edge from argument to predicate
        addEdge(predicateNodeCanonicalName,argumentNodeCanonicalName,"predicateArgument")
        predicateNameMap(pred.pred.name).argumentCanonicalNameList+=Pair(argumentNodeCanonicalName,tempID)
        gnn_input.argumentInfoHornGraphList+=new argumentInfoHronGraph(pred.pred.name,tempID)
        tempID+=1
      }
    }
  }

  def addEdgeInSubTerm(from:String,to:String): Unit ={
    val toNodeClass=to.substring(0,to.indexOf("_"))
    toNodeClass match {
      case "clause" => addEdge(from,to,"guard")
      case "clauseArgument" => addEdge(from,to,"data")
      case _ => addEdge(from,to,"subTerm")
    }
  }

  def drawASTBinaryRelation(op:String,previousNodeName:String,e1: IExpression,e2: IExpression): Unit ={
    val condName=op+"_"+gnn_input.GNNNodeID
    createNode(condName,op,"operator",shapeMap("operator"),gnn_input.GNNNodeID)
    if(previousNodeName!="") addEdgeInSubTerm(condName,previousNodeName)
    drawAST(e1,condName)
    drawAST(e2,condName)
  }
  def drawASTUnaryRelation(op:String,previousNodeName:String,e: IExpression): Unit ={
    val opName=op+"_"+gnn_input.GNNNodeID
    createNode(opName,op,"operator",shapeMap("operator"),gnn_input.GNNNodeID)
    if(previousNodeName!="") addEdgeInSubTerm(opName,previousNodeName)
    drawAST(e,opName)
  }
  def drawASTEndNode(constantStr:String,previousNodeName:String,className:String): Unit ={
    val constantName=constantStr+"_"+gnn_input.GNNNodeID
    createNode(constantName,constantStr,className,shapeMap(className),gnn_input.GNNNodeID)
    //if(previousNodeName!="")
    addEdgeInSubTerm(constantName,previousNodeName)
  }
  def drawAST(e: IExpression,previousNodeName:String=""): Unit ={
    e match {
      case EqZ(t)=>{
        //println("EqZ")
        //create equal node
        val equalName="="+"_"+gnn_input.GNNNodeID
        createNode(equalName,"=","operator",shapeMap("operator"),gnn_input.GNNNodeID)
        if(previousNodeName!="") addEdgeInSubTerm(equalName,previousNodeName)
        //create zero node
        drawASTEndNode("0",equalName,"constant")

        drawAST(t,equalName)
      }
      case Eq(t1, t2) => drawASTBinaryRelation("=",previousNodeName,t1,t2)
      case EqLit(term, lit) => {
        //create equal node
        val equalName="="+"_"+gnn_input.GNNNodeID
        createNode(equalName,"=","operator",shapeMap("operator"),gnn_input.GNNNodeID)
        if(previousNodeName!="") addEdgeInSubTerm(equalName,previousNodeName)
        //create lit node
        drawASTEndNode(lit.toString(),equalName,"constant")
        drawAST(term,equalName)
      }
      case GeqZ(t)=>{
        //create >= node
        val equalName=">="+"_"+gnn_input.GNNNodeID
        createNode(equalName,"=","operator",shapeMap("operator"),gnn_input.GNNNodeID)
        if(previousNodeName!="") addEdgeInSubTerm(equalName,previousNodeName)
        //create zero node
        drawASTEndNode("0",equalName,"constant")
        drawAST(t,equalName)
      }
      case Geq(t1, t2) => drawASTBinaryRelation(">=",previousNodeName,t1,t2)
      case Conj(a,b)=> drawASTBinaryRelation("&",previousNodeName,a,b)
      case Disj(a,b)=> drawASTBinaryRelation("|",previousNodeName,a,b)
      case Const(t)=> drawASTEndNode(t.toString(),previousNodeName,"constant")
      //case SignConst(t)=>{println("SignConst")}
      //case SimpleTerm(t)=>{println("SimpleTerm")}
//      case LeafFormula(t)=>{
//        //println("LeafFormula")
//        drawAST(t,previousNodeName)
//      }
      case Difference(t1, t2)=> drawASTBinaryRelation("-",previousNodeName,t1,t2)
      case IAtom(pred, args) => {}
      case IBinFormula(j, f1, f2) => drawASTBinaryRelation(j.toString,previousNodeName,f1,f2)
      case IBoolLit(v) => drawASTEndNode(v.toString(),previousNodeName,"constant")
      case IFormulaITE(cond, left, right) => {
          drawAST(cond,previousNodeName)
          drawAST(right,previousNodeName)
          drawAST(left,previousNodeName)
      }
      case IIntFormula(rel, term) => drawASTUnaryRelation(rel.toString,previousNodeName,term)
      case INamedPart(pname, subformula) => drawASTUnaryRelation(pname.toString,previousNodeName,subformula)
      case INot(subformula) => drawASTUnaryRelation("!",previousNodeName,subformula)
      case IQuantified(quan, subformula) => drawASTUnaryRelation(quan.toString,previousNodeName,subformula)
      case ITrigger(patterns, subformula) => {}
      case IConstant(c) => drawASTEndNode(c.toString(),previousNodeName,"symbolicConstant")
      case IEpsilon(cond) => drawASTUnaryRelation("eps",previousNodeName,cond)
      case IFunApp(fun, args) => {}
      case IIntLit(v) => drawASTEndNode(v.toString(),previousNodeName,"constant")
      case IPlus(t1, t2) => drawASTBinaryRelation("+",previousNodeName,t1,t2)
      case ITermITE(cond, left, right) => {
        drawAST(cond,previousNodeName)
        drawAST(right,previousNodeName)
        drawAST(left,previousNodeName)
      }
      case ITimes(coeff, subterm) => {
        val timesName="*"+"_"+gnn_input.GNNNodeID
        createNode(timesName,"*","operator",shapeMap("operator"),gnn_input.GNNNodeID)
        if(previousNodeName!="") addEdgeInSubTerm(timesName,previousNodeName)
        drawASTEndNode(coeff.toString(),timesName,"constant")
        drawAST(subterm,timesName)
      }
      case IVariable(index) => drawASTEndNode(index.toString(),previousNodeName,"constant")
      case _ => drawASTEndNode("unknown",previousNodeName,"constant")
    }
  }

}
