package lazabs.horn.graphs

import ap.parser.IAtom
import ap.parser.IExpression.Predicate
import ap.terfor.conjunctions.Conjunction
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{CounterexampleMiner, HornClauses, HornTranslator, NormClause}
import lazabs.horn.graphs.Utils.{getPredAbs, readJSONFile, readJsonFieldDouble, readJsonFieldInt, readSMTFormatFromFile, writeOneLineJson, writeSMTFormatToFile}
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import lazabs.horn.global.HornClause
import lazabs.horn.graphs.GraphUtils.graphFileNameMap
import lazabs.horn.preprocessor.{HornPreprocessor, ReachabilityChecker}

import java.io.{File, PrintWriter}

object counterExampleUtils {
  object CounterExampleMiningOption extends Enumeration {
    val union, common = Value
  }

  def mineClausesInCounterExamples(clauses: Clauses, predicateGenerator: Dag[AndOrNode[NormClause, Unit]] =>
    Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom, NormClause)]]): Unit = {
    //write simplified clauses to file
    writeSMTFormatToFile(clauses, "simplified")

    val CEMiner = new CounterexampleMiner(clauses, predicateGenerator)
    val minedCEs = if (GlobalParameters.get.ceMiningOption == CounterExampleMiningOption.union)
      CEMiner.unionMinimalCounterexampleIndexs
    else
      CEMiner.commonCounterexampleIndexs
    val clausesInCE = for ((c, i) <- clauses.zipWithIndex; if minedCEs.contains(i)) yield c


    val ceLabels = for ((c, i) <- clauses.zipWithIndex) yield {
      if (minedCEs.contains(i)) 1 else 0
    }

    val jsonFileName = GlobalParameters.get.fileName + ".counterExampleIndex.JSON"
    val writer = new PrintWriter(new File(jsonFileName))
    writer.write("{\n")
    writeOneLineJson(head = "clauseNumber", Seq(clauses.length).toString(), writer, changeLine = false)
    writeOneLineJson(head = "counterExampleNumber", Seq(minedCEs.length).toString(), writer, changeLine = false)
    writeOneLineJson(head = "clauseIndices", (0 to clauses.length - 1).toString(), writer)
    writeOneLineJson(head = "counterExampleIndices", minedCEs.toString(), writer)
    writeOneLineJson(head = "counterExampleLabels", ceLabels.toString(), writer)
    writeOneLineJson("endField", "[0]", writer, changeLine = false, lastEntry = true)
    writer.write("}")
    writer.close()

    printMinedClausesInCounterExamples(clauses, clausesInCE)

  }

  def printMinedClausesInCounterExamples(originalClauses: Clauses, minedClauses: Clauses): Unit = {
    println("-" * 10 + " original clauses " + originalClauses.length + "-" * 10)
    if (GlobalParameters.get.log) {
      originalClauses.map(_.toPrologString).foreach(println(_))
    }

    println("-" * 10 + " clauses in counter-examples " + minedClauses.length + "-" * 10)
    if (GlobalParameters.get.log) {
      minedClauses.map(_.toPrologString).foreach(println(_))
    }
  }


  def getPrunedClauses(clauses: Clauses): Clauses = {
    println(Console.BLUE + "-" * 10 + " getPrunedClauses " + "-" * 10)
    if (GlobalParameters.get.hornGraphLabelType == HornGraphLabelType.unsatCore) {
      //val clausesInCounterExample = getRandomCounterExampleClauses(clauses)
      val clausesInCounterExample = getPredictedCounterExampleClauses(clauses)
      val checkedClauses = sanityCheckForUnsatCore(clausesInCounterExample, clauses)
      printPrunedReults(clauses, clausesInCounterExample, checkedClauses)
      checkedClauses
    } else {
      clauses
    }
  }

  def sanityCheckForUnsatCore(clausesInCE: Clauses, originalClauses: Clauses): Clauses = {
    //sanity check, keep at least one entrance and exit in a path
    //    val falsePredicates = for (c<-originalClauses; if c.head.pred==HornClauses.FALSE) yield c.head.pred
    //    val falsePredicatesInCEs = for (c<-clausesInCE; if c.head.pred==HornClauses.FALSE) yield c.head.pred
    val (checkedClauses, _, _) = ReachabilityChecker.process(clausesInCE, VerificationHints(Map()))
    //if this empty, then no path
    if (checkedClauses.length == 0)
      checkedClauses
    else
      clausesInCE
  }


  def getPredictedCounterExampleClauses(clauses: Clauses): Clauses = {
    val graphFileName = GlobalParameters.get.fileName + "." + graphFileNameMap(GlobalParameters.get.hornGraphType) + ".JSON"
    val predictedLabels = readJsonFieldInt(graphFileName, readLabelName = "predictedLabel")
    val predictedLogits = readJsonFieldDouble(graphFileName, readLabelName = "predictedLabelLogit")
    val predictedLabelsFromThresholdLogits = for (l <- predictedLogits) yield if (l > GlobalParameters.get.unsatCoreThreshold) 1 else 0
    if (GlobalParameters.get.log) {
      println(Console.RED + "predictedLabels", predictedLabels.length, predictedLabels.mkString)
      println(Console.RED + "predictedLabelsFromThresholdLogits", predictedLabelsFromThresholdLogits.length, "threshold", GlobalParameters.get.unsatCoreThreshold, predictedLabelsFromThresholdLogits.mkString)
    }

    val clausesInCE = GlobalParameters.get.hornGraphType match {
      case HornGraphType.CDHG => {
        val labelMask = readJsonFieldInt(graphFileName, readLabelName = "labelMask")
        val originalClausesIndex = labelMask.distinct
        val separatedPredictedLabels = for (i <- originalClausesIndex) yield {
          for (ii <- (0 until labelMask.count(_ == i))) yield predictedLabelsFromThresholdLogits(i + ii)
        }
        val labelForOriginalClauses = for (sl <- separatedPredictedLabels) yield {
          sl.max
        }
        if (GlobalParameters.get.log) {
          println(Console.RED + "labelMask", labelMask.length, labelMask.mkString)
          val separatedLabelMask = for (i <- originalClausesIndex) yield {
            for (ii <- (0 until labelMask.count(_ == i))) yield labelMask(i + ii)
          }
          println(Console.RED + "separatedLabelMask", separatedLabelMask.length, separatedLabelMask.mkString)
          println(Console.RED + "clauses", clauses.length)
          println(Console.RED + "separatedPredictedLabels", separatedPredictedLabels.length, separatedPredictedLabels.mkString)
          println(Console.RED + "labelForOriginalClauses", labelForOriginalClauses.length, labelForOriginalClauses.mkString)
        }
        for ((c, l) <- clauses.zip(labelForOriginalClauses); if l == 1) yield c
      }
      case HornGraphType.CG => {
        for ((c, l) <- clauses.zip(predictedLabelsFromThresholdLogits); if l == 1) yield c
      }
    }

    clausesInCE
  }

  def getRandomCounterExampleClauses(clauses: Clauses): Clauses = {
    val rand = new scala.util.Random
    if (GlobalParameters.get.fixRandomSeed)
      rand.setSeed(42)
    for (c <- clauses; if rand.nextInt(10) < 5) yield c
  }

  def printPrunedReults(clauses: Clauses, clausesInCounterExample: Clauses, sanityCheckedClauses: Clauses): Unit = {
    if (GlobalParameters.get.log) {
      writeSMTFormatToFile(clausesInCounterExample, "pruned")

      println("-" * 10 + " original clauses " + clauses.length + "-" * 10)
      clauses.map(_.toPrologString).foreach(println(_))
      println("-" * 10 + " clauses in counter-examples " + clausesInCounterExample.length + "-" * 10)
      clausesInCounterExample.map(_.toPrologString).foreach(println(_))
      println("-" * 10 + " sanity checked clauses " + sanityCheckedClauses.length + "-" * 10)
      sanityCheckedClauses.map(_.toPrologString).foreach(println(_))

    }
  }


}
