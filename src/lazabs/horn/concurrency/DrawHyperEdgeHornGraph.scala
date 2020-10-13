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
import ap.parser.IExpression.{ConstantTerm, Eq}
import ap.parser.{IBinJunctor, IConstant, IExpression, IFormula, ITerm, LineariseVisitor, Simplifier, SymbolCollector}
import lazabs.ast.ASTree
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import scala.collection.GenSet
import scala.collection.mutable.ListBuffer

class DrawHyperEdgeHornGraph(file: String, simpClauses: Clauses, hints: VerificationHints, argumentInfoList: ListBuffer[argumentInfo]) {
  /*
  main6(P5, T6, T7, T8, T9) :- main6(P5, T6 + -1, T7 + -1, P4, P0),
  [P3 != 0 & P5 != 0 & T9 = P0 + 1 + T6 + -1 & T8 = T7 + -1 + 1 + P4 + 1.]

  (1) x = f(\bar y) s.t.

  <1> x is one of the arguments of the clause head
  <2> \bar y are arguments of the literals in the clause body. what if \bar y are just some constants?
  <3> any variable assignment (assignment of values to the variables occurring in C) that satisfies the constraint of C also satisfies (1).
  */
  //val sp = new Simplifier()
  for (clause <- simpClauses) {
    val normalizedClause = clause.normalize()
    var dataflowList = Set[IExpression]()
    //var guardList=Set[IExpression]()
    val bodySymbols = for (body <- normalizedClause.body; arg <- body.args) yield new ConstantTerm(arg.toString)
    var bodySymbolsSet = bodySymbols.toSet
    println(normalizedClause.constraint.toString)
    for (x <- normalizedClause.head.args) {
      val SE = IExpression.SymbolEquation(x)
      val constantTermX = new ConstantTerm(x.toString)
      for (f <- LineariseVisitor(normalizedClause.constraint, IBinJunctor.And)) f match {
        case SE(coefficient, rhs) => {
          if (!(dataflowList contains f) && !(bodySymbolsSet contains constantTermX) && !SymbolCollector.constants(rhs).isEmpty && (for (s <- SymbolCollector.constants(rhs)) yield s.name).subsetOf(for (s <- bodySymbolsSet) yield s.name)) {
            // discovered data-flow from body to x!
            dataflowList += f //IExpression.Eq(x,rhs)
            bodySymbolsSet += constantTermX
          }
        }
        case _ =>{//guardList+=f}
      }
    }
    val guardList = (for (f <- LineariseVisitor(normalizedClause.constraint, IBinJunctor.And)) yield f).toSet.diff(for (df <- dataflowList) yield df.asInstanceOf[IFormula])
    println("normalizedClause")
    println(normalizedClause.head, normalizedClause.body, normalizedClause.constraint)
    println("dataflowList", dataflowList)
    println("guardList", guardList)


  }
  //  for (clause<-simpClauses){
  //    //normalise some of the arguments in body.
  //    for (body <- clause.body){
  //      for (argument<-body.args){
  //        if (it is compisite){
  //          clause.normalize()
  //          //clause.normalize()
  //          create a new variable: val freshVariable= IConstant(new ConstantTerm("freshVariable_" + freshVariableNameCounter.toString))
  //          freshVariableNameCounter+=1
  //          constrainList:+= sp(IExpression.Eq(freshVariable,argument))
  //        }
  //      }
  //     }
  //    //add other constrains to constrainList
  //    for (conjunct <- LineariseVisitor(clause.constraint, IBinJunctor.And)){
  //      constrainList:+=conjunct
  //    }
  //    /*
  //    main6(P5, T6, T7, T8, T9) :- main6(Z, X, Y, P4, P0),
  //    [P5 = Z, X = T6 + -1, Y = T7 + -1, P3 != 0 & P5 != 0 & T9 = P0 + 1 + T6 + -1 & T8 = T7 + -1 + 1 + P4 + 1.]
  //    */
  //    //parse constrainList to determine simple dataflow and guards
  //    var dataflowList=List[IExpression]()
  //    var guardList=List[IExpression]()
  //    var possibleDataflowList=List[IExpression]()
  //    for (constrain<-constrainList){
  //      constrain match {
  //        case Eq(t1,t2)=>{//P5 = Z, X = T6 - 1, Y = T7 - 1, T9 = P0 + T6, T8 = T7 + P4 + 1
  //          if(constrain doesn't contain elements in clause.head.args) {//don't satisfy <1>, so put it to guard
  //            guardList:+=constrain
  //            //if arguments in head can be computed by arguments in body
  //            IExpression.SymbolEquation(x,)
  //          }else if (constrain contains one element in clause.head.args and constrain contains elements in body.args){//satisfy <1> and <2>, need to check <3>
  //            dataflowList:+=constrain
  //          }else if(constrain contains more than one elements in clause.head.args){//satisfy <1>
  //            possibleDataflowList:+=constrain
  //          }
  //        }
  //        case _ =>{guardList:+=constrain}
  //      }
  //    }
  //    //treat assignments with more than one elements in clause.head.args
  //    for (pdf<-possibleDataflowList){
  //      val newPdf =  pdf replace elements in clause.head.args by go through dataflowList
  //      if (newPdf don't contains elements in clause.head.args){
  //        guardList:+=newPdf
  //      }else if (newPdf contains one element in clause.head.args){
  //        dataflowList:+=newPdf
  //      }else if(newPdf contains more than one elements in clause.head.args){
  //        //should we treat it as a normal dataflow like dataflowList:+=newPdf?
  //      }
  //
  //    }
  //    //draw dataflow and guards...
  //  }

}
