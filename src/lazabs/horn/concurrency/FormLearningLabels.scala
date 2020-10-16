package lazabs.horn.concurrency
import java.io.{File, PrintWriter}

import ap.terfor.preds.Predicate
import ap.parser.IAtom
import lazabs.GlobalParameters
import lazabs.horn.concurrency.DrawHornGraph.addQuotes
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}

class FormLearningLabels (simpClauses: Clauses){
  //hints: VerificationHints
  class predicateNodeInfo(nodeName:String){
    val name=nodeName
    var predecessorNameList:List[String]=List()
    var successorNameList:List[String]=List()
    def prettyPrint(): Unit ={
      println(name)
      print("predecessors:")
      for (p<-predecessorNameList) print(p+",")
      println
      print("successors:")
      for (s<-successorNameList) print(s+",")
      println
    }
  }

  def getPredicateOccurenceInCircles(): Map[String,Int] ={
    var predicateNameSet:Set[String]=Set()
    var predicateNodeList:List[predicateNodeInfo]=List()
      for (clause<-simpClauses;p<-clause.predicates){
      if (!predicateNameSet.contains(p.name))
        predicateNodeList:+=new predicateNodeInfo(p.name)
        predicateNameSet+=p.name
    }
    //build and visualize graph
    val writerPredicateGraph = new PrintWriter(new File(GlobalParameters.get.fileName + "." + "circles" + ".gv"))
    writerPredicateGraph.write("digraph dag {" + "\n")
    for(clause<-simpClauses) {
      //create head node
      val headName=clause.head.pred.name
      writerPredicateGraph.write(addQuotes(headName) +
        " [label=" + addQuotes(headName)  + " shape=" + "box" + "];" + "\n")
      for (body<-clause.body){
        //create body node
        val bodyName=body.pred.name
        writerPredicateGraph.write(addQuotes(bodyName) +
          " [label=" + addQuotes(bodyName)  + " shape=" + "box" + "];" + "\n")
        //add edge
        writerPredicateGraph.write(addQuotes(bodyName) + " -> " + addQuotes(headName) + "\n")
        for(pn<-predicateNodeList) if(pn.name==headName) pn.predecessorNameList:+=bodyName else if (pn.name==bodyName) pn.successorNameList:+=headName

      }
    }
    writerPredicateGraph.write("}" + "\n")
    writerPredicateGraph.close()

    //todo:identify circles
    val circles:Set[List[String]]=Set()
    //for (ps<-predicateNodeList) ps.prettyPrint()


    //form predicate head occurrence in circles
    var predicateOccurrenceMap:Map[String,Int]=(for(clause<-simpClauses;p<-clause.predicates if (p.name!="FALSE") ) yield (p.name->0)).toMap
    for (c<-circles;p<-c) if (predicateOccurrenceMap.keySet.contains(p)){
      predicateOccurrenceMap=predicateOccurrenceMap.updated(p,predicateOccurrenceMap(p)+1)
      //new Predicate("Initial",0)
    }
    predicateOccurrenceMap
  }

  def getPredicateOccurenceInClauses(): Map[Predicate,Int] ={
    //form predicate head occurrence in clauses
    var predicateOccurrenceMap:Map[Predicate,Int]=(for(clause<-simpClauses;p<-clause.predicates if (p.name!="FALSE") ) yield (p->0)).toMap
    for(clause<-simpClauses){
      for (p<-clause.predicates) if (predicateOccurrenceMap.keySet.contains(p)){
        predicateOccurrenceMap=predicateOccurrenceMap.updated(p,predicateOccurrenceMap(p)+1)
        //new Predicate("Initial",0)
      }
    }
    predicateOccurrenceMap
  }
}
