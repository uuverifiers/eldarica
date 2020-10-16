package lazabs.horn.concurrency
import ap.terfor.preds.Predicate
import ap.parser.IAtom
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}

class FormLearningLabels (simpClauses: Clauses){
  //hints: VerificationHints


  def getPredicateOccurenceInCircles(): Unit ={

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
