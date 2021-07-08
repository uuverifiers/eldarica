package lazabs.horn.concurrency

import ap.parser.IFormula
import ap.parser.IExpression.Predicate
import lazabs.GlobalParameters
import lazabs.horn.abstractions.{AbsReader, VerificationHints}
import lazabs.horn.concurrency.DrawHornGraph.HornGraphType
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

import scala.collection.mutable.ArrayBuffer

object GraphTranslator {
  def drawAllHornGraph(clauseCollection: ClauseInfo, hintsCollection: VerificationHintsInfo, argumentInfo: ArrayBuffer[argumentInfo], file: String = GlobalParameters.get.fileName): Unit = {
    if (GlobalParameters.get.getAllHornGraph == true) {
      for (graphType <- HornGraphType.values) {
        GlobalParameters.get.hornGraphType = graphType
        drawOneHornGraph(clauseCollection, hintsCollection, argumentInfo, file = file)
      }
      drawOneHornGraph(clauseCollection, hintsCollection, argumentInfo, file = file)
    } else {
      drawOneHornGraph(clauseCollection, hintsCollection, argumentInfo, file = file)
    }
  }

  def drawOneHornGraph(clauseCollection: ClauseInfo, hintsCollection: VerificationHintsInfo, argumentInfo: ArrayBuffer[argumentInfo], file: String = GlobalParameters.get.fileName): Unit = {
    val startTime = System.currentTimeMillis
    GlobalParameters.get.hornGraphType match {
      case HornGraphType.hyperEdgeGraph | HornGraphType.equivalentHyperedgeGraph | HornGraphType.concretizedHyperedgeGraph => new DrawHyperEdgeHornGraph(file, clauseCollection, hintsCollection, argumentInfo)
      case _ => new DrawLayerHornGraph(file, clauseCollection, hintsCollection, argumentInfo)
    }
    println(Console.GREEN + "Time consumption for drawing " + GlobalParameters.get.hornGraphType.toString + ": " + (System.currentTimeMillis - startTime) / 1000 + "s")
  }

  def getBatchSize(simplifiedClause: Clauses, totalPredicateNumber: Int): Int = {
    //todo: do some experiments to determine a good strategy
    //    if (simplifiedClause.size>1000)
    //      10
    //    else if (simplifiedClause.size>500)
    //      50
    //    else if (simplifiedClause.size>100)
    //      100
    //    else 200
    //    if (totalPredicateNumber>=10000)
    200
  }

  def separateGraphByPredicates(unlabeledPredicates: VerificationHints, labeledPredicates: VerificationHints, clauseCollection: ClauseInfo, argumentInfo: ArrayBuffer[argumentInfo]): Unit = {
    val totalPredicateNumber = unlabeledPredicates.totalPredicateNumber
    println("total unlabeled number", totalPredicateNumber)
    val batch_size = getBatchSize(clauseCollection.simplifiedClause, totalPredicateNumber)
    //val batch_size=4
    println("batch_size", batch_size)
    val trunk = (totalPredicateNumber / batch_size.toFloat).ceil.toInt
    val trunkList =
    if (GlobalParameters.get.generateTemplates == true) {
      val predicateNumberRatio = for ((k, v) <- unlabeledPredicates.predicateHints) yield k -> v.size / totalPredicateNumber.toFloat
      for (t <- 0 until trunk) yield {
        val unlabeled = VerificationHints(for ((k, v) <- unlabeledPredicates.predicateHints) yield {
          val batch_size_per_head = (predicateNumberRatio(k) * batch_size).ceil.toInt
          val sliceEnd = if (batch_size_per_head * (t + 1) >= v.size) v.size else batch_size_per_head * (t + 1)
          k -> v.slice(batch_size_per_head * t, sliceEnd)
        })
        val labeled=
          if (!labeledPredicates.isEmpty) {
            VerificationHints(for ((k, v) <- unlabeled.predicateHints) yield {
              //todo:change to logic compare
              val labelList = for (l <- labeledPredicates.predicateHints(k); if v.contains(l)) yield l
              k -> labelList
            })
          } else {
            VerificationHints(Map())
          }
        (unlabeled, labeled)
      }
    } else {
      val predicateNumberRatio = for ((k, v) <- unlabeledPredicates.toInitialPredicates) yield k -> v.size / totalPredicateNumber.toFloat
      for (t <- 0 until trunk) yield {
        val unlabeled = for ((k, v) <- unlabeledPredicates.toInitialPredicates) yield {
          val batch_size_per_head = (predicateNumberRatio(k) * batch_size).ceil.toInt
          val sliceEnd = if (batch_size_per_head * (t + 1) >= v.size) v.size else batch_size_per_head * (t + 1)
          k -> v.slice(batch_size_per_head * t, sliceEnd)
        }
        val labeled: Map[Predicate, Seq[IFormula]] =
          if (!labeledPredicates.isEmpty) {
            for ((k, v) <- unlabeled) yield {
              val labelList = for (l <- labeledPredicates.toInitialPredicates(k); if HintsSelection.containsPred(l, v)) yield l
              k -> labelList
            }
          } else {
            Map()
          }
        (HintsSelection.transformPredicateMapToVerificationHints(unlabeled), HintsSelection.transformPredicateMapToVerificationHints(labeled))
      }
    }

    for ((t, i) <- trunkList.zipWithIndex) {
      val fileName = GlobalParameters.get.fileName + "-" + i.toString
      val hintsCollection = new VerificationHintsInfo(t._1, t._2, VerificationHints(Map())) //labeledPredicates
      if (t._1.totalPredicateNumber!=0) {
        println("------------")
        println("unlabeled", t._1.totalPredicateNumber)
        println("labeled", t._2.totalPredicateNumber)
        drawAllHornGraph(clauseCollection, hintsCollection, argumentInfo, fileName)
        HintsSelection.writePredicatesToFiles(t._1, t._2, fileName)
      }

    }
  }

}








