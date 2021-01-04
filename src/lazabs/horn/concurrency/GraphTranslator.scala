package lazabs.horn.concurrency
import lazabs.GlobalParameters
import lazabs.horn.concurrency.DrawHornGraph.HornGraphType

import scala.collection.mutable.{ArrayBuffer}

object GraphTranslator{
  def drawAllHornGraph(clauseCollection: ClauseInfo, hintsCollection: VerificationHintsInfo, argumentInfo: ArrayBuffer[argumentInfo]): Unit ={
    for(graphType<-HornGraphType.values){
      val startTime=System.currentTimeMillis
      GlobalParameters.get.hornGraphType=graphType
      GlobalParameters.get.hornGraphType match {
        case HornGraphType.hyperEdgeGraph |HornGraphType.equivalentHyperedgeGraph | HornGraphType.concretizedHyperedgeGraph =>new DrawHyperEdgeHornGraph(GlobalParameters.get.fileName, clauseCollection, hintsCollection,argumentInfo)
        case _=>new DrawLayerHornGraph(GlobalParameters.get.fileName, clauseCollection, hintsCollection,argumentInfo)
      }
      println(Console.GREEN+"Time consumption for drawing graph: "+ (System.currentTimeMillis-startTime)/1000 +"s")
    }
  }
}








