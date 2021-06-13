package lazabs.horn.concurrency
import lazabs.GlobalParameters
import lazabs.horn.abstractions.{AbsReader, VerificationHints}
import lazabs.horn.concurrency.DrawHornGraph.HornGraphType

import scala.collection.mutable.ArrayBuffer

object GraphTranslator{
  def drawAllHornGraph(clauseCollection: ClauseInfo, hintsCollection: VerificationHintsInfo, argumentInfo: ArrayBuffer[argumentInfo],file:String=GlobalParameters.get.fileName): Unit ={
    if(GlobalParameters.get.getAllHornGraph==true){
      for(graphType<-HornGraphType.values){
        GlobalParameters.get.hornGraphType=graphType
        drawOneHornGraph(clauseCollection,hintsCollection,argumentInfo,file=file)
      }
      drawOneHornGraph(clauseCollection,hintsCollection,argumentInfo,file=file)
    }else{
      drawOneHornGraph(clauseCollection,hintsCollection,argumentInfo,file=file)
    }
  }

  def drawOneHornGraph(clauseCollection: ClauseInfo, hintsCollection: VerificationHintsInfo, argumentInfo: ArrayBuffer[argumentInfo],file:String=GlobalParameters.get.fileName): Unit ={
    val startTime=System.currentTimeMillis
    GlobalParameters.get.hornGraphType match {
      case HornGraphType.hyperEdgeGraph |HornGraphType.equivalentHyperedgeGraph | HornGraphType.concretizedHyperedgeGraph =>new DrawHyperEdgeHornGraph(file, clauseCollection, hintsCollection,argumentInfo)
      case _=>new DrawLayerHornGraph(file, clauseCollection, hintsCollection,argumentInfo)
    }
    println(Console.GREEN+"Time consumption for drawing "+GlobalParameters.get.hornGraphType.toString+": "+ (System.currentTimeMillis-startTime)/1000 +"s")
  }

  def separateGraphByPredicates(unlabeledPredicates:VerificationHints,labeledPredicates:VerificationHints,clauseCollection:ClauseInfo,argumentInfo: ArrayBuffer[argumentInfo]): Unit ={
    val totalPredicateNumber=unlabeledPredicates.totalPredicateNumber
    println("total unlabeled number",totalPredicateNumber)
    val predicateNumberRatio= for ((k,v)<-unlabeledPredicates.toInitialPredicates) yield k->v.size/totalPredicateNumber.toFloat
    //println("predicateNumberRatio",predicateNumberRatio)
    val batch_size=
    if (clauseCollection.simplifiedClause.size>1000)
      10
    else if (clauseCollection.simplifiedClause.size>500)
      50
    else if (clauseCollection.simplifiedClause.size>100)
      100
    else 200
    //val batch_size=4
    println("batch_size",batch_size)
    val trunk=(totalPredicateNumber/batch_size.toFloat).ceil.toInt
//    val trunk=3
//    val batch_size=(totalPredicateNumber/trunk.toFloat).ceil.toInt
    val trunkList:Seq[Tuple2[VerificationHints,VerificationHints]]=
      for (t<- (0 until trunk))yield{
        val unlabeled= for ((k,v)<- unlabeledPredicates.toInitialPredicates) yield {
          val batch_size_per_head=(predicateNumberRatio(k)*batch_size).ceil.toInt
          val sliceEnd= if (batch_size_per_head*(t+1)>=v.size) v.size else batch_size_per_head*(t+1)
          k->v.slice(batch_size_per_head*t,sliceEnd)
        }
        val labeled = for ((k,v)<-unlabeled) yield {
          val labelList=for (l<-labeledPredicates.toInitialPredicates(k);if v.contains(l)) yield l
          k->labelList
        }
        (HintsSelection.transformPredicateMapToVerificationHints(unlabeled),HintsSelection.transformPredicateMapToVerificationHints(labeled))
      }
    for (t<-trunkList) yield {
      println("------------")
      println("unlabeled",t._1.totalPredicateNumber)
      //t._1.pretyPrintHints()
      println("labeled",t._2.totalPredicateNumber)
      //t._2.pretyPrintHints()
    }
    for ((t,i)<-trunkList.zipWithIndex){
      val fileName=GlobalParameters.get.fileName+"-"+i.toString
      val hintsCollection=new VerificationHintsInfo(t._1,t._2,VerificationHints(Map()))//labeledPredicates
      drawAllHornGraph(clauseCollection,hintsCollection,argumentInfo,fileName)
      HintsSelection.writePredicatesToFiles(t._1,t._2,fileName)
    }
  }

}








