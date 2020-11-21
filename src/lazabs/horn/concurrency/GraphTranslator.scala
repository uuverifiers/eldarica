package lazabs.horn.concurrency
import java.io.{File, FileWriter, PrintWriter}

import ap.parser._
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints._
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.concurrency.DrawHornGraph.HornGraphType
import lazabs.horn.preprocessor.HornPreprocessor.VerificationHints

import scala.collection.mutable.ListBuffer

object GraphTranslator{
  def drawAllHornGraph(clauseCollection: ClauseInfo, hintsCollection: VerificationHintsInfo, argumentInfo: ListBuffer[argumentInfo]): Unit ={
    for(graphType<-HornGraphType.values){
      GlobalParameters.get.hornGraphType=graphType
      GlobalParameters.get.hornGraphType match {
        case HornGraphType.hyperEdgeGraph =>new DrawHyperEdgeHornGraph(GlobalParameters.get.fileName, clauseCollection, hintsCollection,argumentInfo)
        case _=>new DrawLayerHornGraph(GlobalParameters.get.fileName, clauseCollection, hintsCollection,argumentInfo)
      }
    }
  }
}








