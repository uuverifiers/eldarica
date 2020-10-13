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
import ap.parser.IExpression.{ConstantTerm, Eq}
import ap.parser.{IBinJunctor, IConstant, IExpression, IFormula, ITerm, LineariseVisitor, Simplifier, SymbolCollector}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import scala.collection.mutable.ListBuffer

class DrawHyperEdgeHornGraph(file: String, simpClauses: Clauses, hints: VerificationHints, argumentInfoList: ListBuffer[argumentInfo]) extends DrawHornGraph (file: String, simpClauses: Clauses,hints:VerificationHints,argumentInfoList:ListBuffer[argumentInfo]) {

  println("Write hyperedge horn graph to file")
  var edgeNameMap: Map[String, String] = Map()
  edgeNameMap += ("controlFlowHyperEdge" -> "CFHE")
  edgeNameMap += ("dataFlowHyperEdge" -> "DFHE")
  edgeNameMap += ("dataFlowAST" -> "data")
  edgeNameMap += ("guardAST" -> "guard")
  edgeNameMap += ("argument" -> "arg")
  //turn on/off edge's label
  var edgeNameSwitch = true
  if (edgeNameSwitch == false) {
    for (key <- edgeNameMap.keys)
      edgeNameMap += (key -> "")
  }
  //node cotegory: Operator and Constant don't need canonical name. FALSE is unique category
  val controlNodePrefix="CONTROLN_"
  val symbolicConstantNodePrefix="SYMBOLIC_CONSTANT_"
  val argumentNodePrefix="ARGUMENT_"
  val hyperEdgeNodePrefix="hyperedge_"
  //node shape map
  var nodeShapeMap: Map[String, String] = Map()
  nodeShapeMap += ("CONTROL" -> "box")
  nodeShapeMap += ("OPERATOR" -> "square")
  nodeShapeMap += ("SYMBOLIC_CONSTANT" -> "circle")
  nodeShapeMap += ("CONSTANT" -> "circle")
  nodeShapeMap += ("ARGUMENT" -> "ellipse")
  nodeShapeMap += ("FALSE" -> "box")


  val sp = new Simplifier()
  val dataFlowInfoWriter = new PrintWriter(new File(file + ".HornGraph"))
  var tempID=0
  for (clause <- simpClauses) {
    val normalizedClause = clause.normalize()
    val (dataFlowSet,guardSet)=getDataFlowAndGuard(clause,normalizedClause,dataFlowInfoWriter)
    //todo: draw control flow
    //draw body predicate node and argument node
    if(normalizedClause.body.isEmpty){
      val initialControlFlowNodeName= controlNodePrefix+gnn_input.CONTROLCanonicalID.toString
      //draw predicate node
      createNode(initialControlFlowNodeName,"Initial","CONTROL",nodeShapeMap("CONTROL"))
    }else{
      for(body<-clause.body){
        //draw predicate node
        val controlFlowNodeName= controlNodePrefix+gnn_input.CONTROLCanonicalID.toString
        createNode(controlFlowNodeName,body.pred.name,"CONTROL",nodeShapeMap("CONTROL"))
        //todo:draw argument node
        tempID=0
        for(arg<-body.args){
          gnn_input.argumentInfoHornGraphList+=new argumentInfoHronGraph(body.pred.name,tempID)
          tempID+=1
        }

      }
    }
    //draw head predicate node and argument node
    if (normalizedClause.head.pred.name=="FALSE"){
      //draw predicate node
      createNode("FALSE","FALSE","FALSE",nodeShapeMap("FALSE"))
    }else{
      //draw predicate node
      val controlFlowNodeName= controlNodePrefix+gnn_input.CONTROLCanonicalID.toString
      createNode(controlFlowNodeName,normalizedClause.head.pred.name,"CONTROL",nodeShapeMap("CONTROL"))
      //todo: draw argument node
      tempID=0
      for(arg<-normalizedClause.head.args){
        gnn_input.argumentInfoHornGraphList+=new argumentInfoHronGraph(normalizedClause.head.pred.name,tempID)
        tempID+=1
      }
    }
    //todo: draw hyperedge between body and head
    val hyperedgeName=hyperEdgeNodePrefix+gnn_input.hyperEdgeCanonicalID.toString

    //todo: draw guard and data flow

  }
  writerGraph.write("}" + "\n")
  writerGraph.close()
  dataFlowInfoWriter.close()

  val (argumentIDList,argumentNameList,argumentOccurrenceList) = matchArguments()
  writeGNNInputToJSONFile(argumentIDList,argumentNameList,argumentOccurrenceList)







  def getDataFlowAndGuard(clause:Clause,normalizedClause:Clause,dataFlowInfoWriter:PrintWriter): (Set[IExpression],Set[IFormula]) ={
     /*
    (1) x = f(\bar y) s.t.

    <1> x is one of the arguments of the clause head
    <2> \bar y are arguments of the literals in the clause body. what if \bar y are just some constants?
    <3> any variable assignment (assignment of values to the variables occurring in C) that satisfies the constraint of C also satisfies (1).
    */
    var dataflowList = Set[IExpression]()
    var dataflowListHeadArgSymbolEquation=Set[IExpression]()
    val bodySymbols = for (body <- normalizedClause.body; arg <- body.args) yield new ConstantTerm(arg.toString)
    var bodySymbolsSet = bodySymbols.toSet
    for (x <- normalizedClause.head.args) {
      val SE = IExpression.SymbolEquation(x)
      val constantTermX = new ConstantTerm(x.toString)
      for (f <- LineariseVisitor(normalizedClause.constraint, IBinJunctor.And)) f match {
        case SE(coefficient, rhs) => {
          if (!(dataflowList contains f) && !(bodySymbolsSet contains constantTermX) && !SymbolCollector.constants(rhs).isEmpty
            && (for (s <- SymbolCollector.constants(rhs)) yield s.name).subsetOf(for (s <- bodySymbolsSet) yield s.name)
            && (for (s <- SymbolCollector.constants(f)) yield s.name).contains(x.toString)) {
            // discovered data-flow from body to x!
            dataflowList += f//sp(IExpression.Eq(x,rhs))
            dataflowListHeadArgSymbolEquation += sp(IExpression.Eq(x,rhs))
            bodySymbolsSet += constantTermX
          }
        }
        case _ => { //guardList+=f}
        }
      }
    }
    val guardList = (for (f <- LineariseVisitor(normalizedClause.constraint, IBinJunctor.And)) yield f).toSet.diff(for (df <- dataflowList) yield df.asInstanceOf[IFormula])
    dataFlowInfoWriter.write("--------------------\n")
    dataFlowInfoWriter.write(clause.toPrologString+"\n")
    dataFlowInfoWriter.write(normalizedClause.toPrologString+"\n")
    dataFlowInfoWriter.write("dataflow:\n")
    for (df<-dataflowListHeadArgSymbolEquation)
      dataFlowInfoWriter.write(df.toString+"\n")
    dataFlowInfoWriter.write("guard:\n")
    for (g<- guardList)
      dataFlowInfoWriter.write(g.toString+"\n")
    (dataflowListHeadArgSymbolEquation,guardList)
  }

}
