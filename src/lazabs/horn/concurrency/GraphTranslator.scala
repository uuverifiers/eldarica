package lazabs.horn.concurrency
import lazabs.GlobalParameters
import lazabs.horn.concurrency.DrawHornGraph.HornGraphType

import scala.collection.mutable.{ArrayBuffer}

object GraphTranslator{
  def drawAllHornGraph(clauseCollection: ClauseInfo, hintsCollection: VerificationHintsInfo, argumentInfo: ArrayBuffer[argumentInfo]): Unit ={
    if(GlobalParameters.get.getHornGraph==true){
      drawOneHornGraph(clauseCollection,hintsCollection,argumentInfo)
    }else{
      for(graphType<-HornGraphType.values){
        GlobalParameters.get.hornGraphType=graphType
        drawOneHornGraph(clauseCollection,hintsCollection,argumentInfo)
      }
    }
  }

  def drawOneHornGraph(clauseCollection: ClauseInfo, hintsCollection: VerificationHintsInfo, argumentInfo: ArrayBuffer[argumentInfo]): Unit ={
    val startTime=System.currentTimeMillis
    GlobalParameters.get.hornGraphType match {
      case HornGraphType.hyperEdgeGraph |HornGraphType.equivalentHyperedgeGraph | HornGraphType.concretizedHyperedgeGraph =>new DrawHyperEdgeHornGraph(GlobalParameters.get.fileName, clauseCollection, hintsCollection,argumentInfo)
      case _=>new DrawLayerHornGraph(GlobalParameters.get.fileName, clauseCollection, hintsCollection,argumentInfo)
    }
    println(Console.GREEN+"Time consumption for drawing "+GlobalParameters.get.hornGraphType.toString+": "+ (System.currentTimeMillis-startTime)/1000 +"s")
  }
}








