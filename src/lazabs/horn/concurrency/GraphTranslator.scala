package lazabs.horn.concurrency
import lazabs.GlobalParameters
import lazabs.horn.concurrency.DrawHornGraph.HornGraphType
import scala.collection.mutable.ListBuffer

object GraphTranslator{
  def drawAllHornGraph(clauseCollection: ClauseInfo, hintsCollection: VerificationHintsInfo, argumentInfo: ListBuffer[argumentInfo]): Unit ={
    for(graphType<-HornGraphType.values){
      GlobalParameters.get.hornGraphType=graphType
      GlobalParameters.get.hornGraphType match {
        case HornGraphType.hyperEdgeGraph |HornGraphType.equivalentHyperedgeGraph =>new DrawHyperEdgeHornGraph(GlobalParameters.get.fileName, clauseCollection, hintsCollection,argumentInfo)
        case _=>new DrawLayerHornGraph(GlobalParameters.get.fileName, clauseCollection, hintsCollection,argumentInfo)
      }
    }
  }
}








