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
import ap.parser.IAtom
import lazabs.GlobalParameters
import scala.collection.mutable.{ListBuffer, HashMap => MHashMap, Map => MuMap}
import lazabs.horn.concurrency.DrawHornGraph.{GNNInput, addQuotes}
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import play.api.libs.json.Json

import scala.collection.mutable.ListBuffer

class DrawLayerHornGraph(file: String, simpClauses: Clauses,hints:VerificationHints,argumentInfoList:ListBuffer[argumentInfo]) {
  val dot = new Digraph(comment = "Horn Graph")
  val gnn_input=new GNNInput()

  println("Write horn to file")
  var edgeNameMap: Map[String, String] = Map()
  edgeNameMap += ("predicateArgument" -> "PA")
  edgeNameMap += ("predicateInstance" -> "PI")
  edgeNameMap += ("argumentInstance" -> "AI")
  edgeNameMap += ("controlHead" -> "CH")
  edgeNameMap += ("controlBody" -> "CB")
  edgeNameMap += ("argument" -> "ARG")
  edgeNameMap += ("guard" -> "guard")
  edgeNameMap += ("data" -> "data")
  edgeNameMap += ("subTermEdge" -> "ste")

  //turn on/off edge's label
  var edgeNameSwitch = true
  if (edgeNameSwitch == false) {
    for (key <- edgeNameMap.keys)
      edgeNameMap += (key -> "")
  }

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

  var predicateNameSet= Set[String]()

  println("-------------debug-----------")
  for (clause <- simpClauses) {

    println(clause.toPrologString.toString)
    //create clause node
    createNode(clausePrefix+gnn_input.clauseCanonicalID.toString,
      "C"+gnn_input.clauseCanonicalID.toString,"clause","box",gnn_input.GNNNodeID)

    //create head node
    createNode(clauseHeadPrefix+gnn_input.clauseHeadCanonicalID.toString,
      "HEAD","clauseHead","box",gnn_input.GNNNodeID)

    //create body node
    createNode(clauseBodyPrefix+gnn_input.clauseBodyCanonicalID.toString,
      "BODY"+gnn_input.clauseBodyCanonicalID.toString,"clauseBody","box",gnn_input.GNNNodeID)

    //create FALSE node
    createNode("FALSE",
      "FALSE","FALSE","box",gnn_input.GNNNodeID)

    //create clause arguments node in head
    var tempID=0
    for (headArg<-clause.head.args){
      createNode(clauseArgumentPrefix+gnn_input.clauseArgCanonicalID.toString,
        "ARG"+tempID.toString,"clauseArg","ellipse",gnn_input.GNNNodeID)
      tempID+=1
    }
    createPredicateLayerNodesAndEdges(clause.head)


    //create clause arguments node in body
    for (bodyPredicate<-clause.body){
      createPredicateLayerNodesAndEdges(bodyPredicate)
      tempID=0
      for (bodyArg<-bodyPredicate.args){
        createNode(clauseArgumentPrefix+gnn_input.clauseArgCanonicalID.toString,
          "ARG"+tempID.toString,"clauseArg","ellipse",gnn_input.GNNNodeID)
        tempID+=1
      }
      predicateNameSet+=bodyPredicate.pred.name
    }


  }


  //write dot file
  val filePath=file.substring(0,file.lastIndexOf("/")+1)
  dot.save(fileName = file+".layerHornGraph.gv", directory = filePath)
  //write JSON file
  val oneGraphGNNInput=Json.obj("nodeIds" -> gnn_input.nodeIds,"nodeSymbolList"->gnn_input.nodeSymbols,
    "argumentIndices"->gnn_input.argumentIndices)
  println("Write GNNInput to file")
  val writer = new PrintWriter(new File(file + ".layerHornGraph.JSON")) //python path
  writer.write(oneGraphGNNInput.toString())
  writer.close()



  def createNode(canonicalName:String,labelName:String,className:String,shape:String,GNNNodeID:Int): Unit ={
    dot.node(addQuotes(canonicalName), label = addQuotes(labelName),
      attrs = MuMap("nodeName"->addQuotes(canonicalName),
        "shape"->addQuotes(shape),"class"->className,"GNNNodeID"->GNNNodeID.toString))
    if (className=="predicateArgument"){
      gnn_input.incrementArgumentIndicesAndNodeIds(canonicalName,className,labelName)
    }else{
      gnn_input.incrementNodeIds(canonicalName,className,labelName)
    }

  }

  def createPredicateLayerNodesAndEdges(pred:IAtom): Unit ={
    //predicate layer: create predicate and argument node
    if (!predicateNameSet.contains(pred.pred.name)){
      predicateNameSet+=pred.pred.name
      val predicateNodeCanonicalName=predicateNamePrefix+gnn_input.predicateNameCanonicalID.toString
      createNode(predicateNamePrefix+gnn_input.predicateNameCanonicalID.toString,
        pred.pred.name,"predicateName","box",gnn_input.GNNNodeID)
      var tempID=0
      for (headArg<-pred.args){
        val argumentNodeCanonicalName=clauseArgumentPrefix+gnn_input.predicateArgumentCanonicalID.toString
        //create argument node
        createNode(argumentNodeCanonicalName,
          "Arg"+tempID.toString,"predicateArgument","ellipse",gnn_input.GNNNodeID)
        tempID+=1
        //create edge from argument to predicate
        dot.edge(addQuotes(predicateNodeCanonicalName),addQuotes(argumentNodeCanonicalName),attrs = MuMap("label"->addQuotes(edgeNameMap("predicateArgument"))))
      }
    }
  }


}


class ClauseInfo(){

}
