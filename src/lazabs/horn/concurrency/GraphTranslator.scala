package lazabs.horn.concurrency
import lazabs.GlobalParameters
import lazabs.horn.concurrency.DrawHornGraph.HornGraphType

import scala.collection.mutable.{ArrayBuffer}

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
}








