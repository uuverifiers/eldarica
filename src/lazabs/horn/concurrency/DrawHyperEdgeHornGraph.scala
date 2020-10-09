package lazabs.horn.concurrency
import ap.parser.IExpression.{ConstantTerm, Eq}
import ap.parser.{IBinJunctor, IConstant, IExpression, IFormula, LineariseVisitor, Simplifier}
import lazabs.ast.ASTree
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import scala.collection.mutable.ListBuffer

class DrawHyperEdgeHornGraph(file: String, simpClauses: Clauses,hints:VerificationHints,argumentInfoList:ListBuffer[argumentInfo]) {
  //(1) x = f(\bar y)
  //<1> x is one of the arguments of the clause head
  //<2> \bar y are arguments of the literals in the clause body
  //<3> any variable assignment (assignment of values to the variables occurring in C) that satisfies the constraint of C also satisfies (1).
//
//  val sp=new Simplifier()
//  var freshVariableNameCounter=0
//  var constrainList=List[IExpression]()
//  for (clause<-simpClauses){
//    //normalise some of the arguments in body.
//    for (body <- clause.body){
//      for (argument<-body.args){
//        if (argument contains one or more elements in clause.head.args){
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
//    //parse constrainList to determine simple dataflow and guards
//    var dataflowList=List[IExpression]()
//    var guardList=List[IExpression]()
//    var possibleDataflowList=List[IExpression]()
//    for (constrain<-constrainList){
//      constrain match {
//        case Eq(t1,t2)=>{
//          if(constrain doesn't contain elements in clause.head.args) {//don't satisfy <1>, so put it to guard
//            guardList:+=constrain
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
//


}
