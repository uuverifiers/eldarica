package lazabs.horn.graphs

import ap.parser.IAtom
import ap.parser.IExpression.Predicate
import ap.terfor.conjunctions.Conjunction
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{AbstractState, CounterexampleMiner, HornClauses, HornTranslator, NormClause, RelationSymbol, StateQueue}
import lazabs.horn.graphs.Utils.{getFloatSeqRank, getPredAbs, printListMap, readJSONFile, readJsonFieldDouble, readJsonFieldInt, readSMTFormatFromFile, roundByDigit, writeOneLineJson, writeSMTFormatToFile}
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import lazabs.horn.global.HornClause
import lazabs.horn.graphs.GraphUtils.{graphFileNameMap, printCurrentNodeMap}
import lazabs.horn.preprocessor.{HornPreprocessor, ReachabilityChecker}

import scala.collection.mutable.PriorityQueue
import java.io.{File, PrintWriter}

object counterExampleUtils {
  object CounterExampleMiningOption extends Enumeration {
    val union, common = Value
  }

  def mineClausesInCounterExamples(clauses: Clauses, predicateGenerator: Dag[AndOrNode[NormClause, Unit]] =>
    Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom, NormClause)]]): Unit = {

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


  def getRankedClausesByMUS(clauses: Clauses): Seq[(HornClauses.Clause, Int)] = {
    try {
      val graphFileName = GlobalParameters.get.fileName + "." + graphFileNameMap(GlobalParameters.get.hornGraphType) + ".JSON"
      val predictedLogits = readJsonFieldDouble(graphFileName, readLabelName = "predictedLabelLogit")
      //The higher value the lower rank
      val sortedClauses = clauses.zip(predictedLogits).sortBy(_._2).reverse //todo check this
      val rankedClauses = for ((t, i) <- sortedClauses.zipWithIndex) yield (t._1, i)
      //normalize rank to 0 to 100, rank may repeated
      val normalizedRankedClause = rankedClauses.map(x => (x._1, (x._2.toDouble / rankedClauses.length * 100).toInt))

      if (GlobalParameters.get.log) {
        println(Console.BLUE + "rank, logit value, clause")
        for ((t, i) <- sortedClauses.zipWithIndex) println(Console.BLUE + i, t._2, t._1)
      }

      normalizedRankedClause


    } catch {
      case _ => {
        val zeros = Seq.fill(clauses.length)(0)
        clauses.zip(zeros)
      }
    }
  }

  def getPrunedClauses(clauses: Clauses): Clauses = {
    println(Console.BLUE + "-" * 10 + " getPrunedClauses " + "-" * 10)
    if (GlobalParameters.get.hornGraphLabelType == HornGraphLabelType.unsatCore) {
      try {
        //val clausesInCounterExample = getRandomCounterExampleClauses(clauses)
        val clausesInCounterExample = getPredictedCounterExampleClauses(clauses)
        val checkedClauses = sanityCheckForUnsatCore(clausesInCounterExample, clauses)
        printPrunedReults(clauses, clausesInCounterExample, checkedClauses)
        checkedClauses
      } catch {
        case _ => {
          println(Console.RED + "pruning except")
          clauses
        }
      }
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
    // pruned by rank
    //higher logit value higher rank
    val sortedClausesByLogitValue = clauses.zip(predictedLogits).sortBy(_._2)
    val rankedClausesMap = (for ((t, i) <- sortedClausesByLogitValue.zipWithIndex) yield (t._1, i)).toMap
    println("clauses",clauses.length)
    println("predictedLogits",predictedLogits.length)
    val predictedLogitsRank = for (c <- clauses) yield rankedClausesMap(c)
    //val predictedLogitsRank = getFloatSeqRank(predictedLogits.toSeq)
    val rankThreshold = GlobalParameters.get.unsatCoreThreshold * predictedLogitsRank.length
    val predictedLabelsFromThresholdLogits = for (r <- predictedLogitsRank) yield if (r >= rankThreshold) 1 else 0
    //pruned by normalization
    //    val normalizedPredictedLogits= predictedLogits.map(x => (x - predictedLogits.min) / (predictedLogits.max - predictedLogits.min))
    //    val predictedLabelsFromThresholdLogits = for (l <- normalizedPredictedLogits) yield if (l > GlobalParameters.get.unsatCoreThreshold) 1 else 0

    if (GlobalParameters.get.log) {
      println(Console.BLUE + "predictedLabels", predictedLabels.length, predictedLabels.mkString)
      println(Console.BLUE + "predictedLabelsFromThresholdLogits", predictedLabelsFromThresholdLogits.length, "threshold", GlobalParameters.get.unsatCoreThreshold, predictedLabelsFromThresholdLogits.mkString)
    }

    val clausesInCE = GlobalParameters.get.hornGraphType match {
      case HornGraphType.CDHG => {
        //CDHG increased the clauses when normalization, so we need transform it back by label Mask
        val labelMask = readJsonFieldInt(graphFileName, readLabelName = "labelMask")
        val originalClausesIndex = labelMask.distinct
        println("debug 0")
        val separatedPredictedLabels = for (i <- originalClausesIndex) yield {
          for (ii <- (0 until labelMask.count(_ == i))) yield predictedLabelsFromThresholdLogits(i + ii)
        }
        println("separatedPredictedLabels",separatedPredictedLabels.mkString)
        println("debug 1")
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
      writeSMTFormatToFile(clausesInCounterExample, "pruned-" + roundByDigit(GlobalParameters.get.unsatCoreThreshold, 2))
      writeSMTFormatToFile(sanityCheckedClauses, "pruned-after-reachability-check-" + roundByDigit(GlobalParameters.get.unsatCoreThreshold, 2))
      println("-" * 10 + " original clauses " + clauses.length + "-" * 10)
      clauses.map(_.toPrologString).foreach(println(_))
      println("-" * 10 + " clauses in counter-examples " + clausesInCounterExample.length + "-" * 10)
      clausesInCounterExample.map(_.toPrologString).foreach(println(_))
      println("-" * 10 + " sanity checked clauses " + sanityCheckedClauses.length + "-" * 10)
      sanityCheckedClauses.map(_.toPrologString).foreach(println(_))

    }
  }


}


class MUSPriorityStateQueue(normClauseToRank: Map[NormClause, Int]) extends StateQueue {
  type TimeType = Int

  private var time = 0

  private def priority(s: Expansion) = {
    // the lower logit value the higher rank value
    // the lower the priority value is, the higher priority that the clause will be processed first
    val (_, nc, _, _) = s
    val rankScore = normClauseToRank(nc)


    val (states, NormClause(_, _, (RelationSymbol(headSym), _)), _,
    birthTime) = s


    //used only rank
    rankScore

    //todo: experiment with coefficients
    //combine rank score with other heuristics with coefficients
//    val coefficient = 10 //0.5, 10, 100
//    (headSym match {
//      case HornClauses.FALSE => -10000
//      case _ => 0
//    }) + (
//      for (AbstractState(_, preds) <- states.iterator)
//        yield preds.size).sum + //less predicates means less restricts, means more states
//      birthTime + //longer birthtime means higher priority
//      (coefficient * rankScore).toInt


    //combine rank score with other heuristics
    //    (headSym match {
    //      case HornClauses.FALSE => -10000
    //      case _ => 0
    //    }) + (
    //      for (AbstractState(_, preds) <- states.iterator)
    //        yield preds.size).sum + //less predicates means less restricts, means more states
    //      birthTime //longer birthtime means higher priority
    //    +rankScore

    //original version
    //    (headSym match {
    //      case HornClauses.FALSE => -10000
    //      case _ => 0
    //    }) + (
    //      for (AbstractState(_, preds) <- states.iterator)
    //        yield preds.size).sum +
    //      birthTime
  }

  private implicit val ord = new Ordering[Expansion] {
    def compare(s: Expansion, t: Expansion) =
      priority(t) - priority(s)
  }

  private val states = new PriorityQueue[Expansion]

  def isEmpty: Boolean =
    states.isEmpty

  def size: Int =
    states.size

  def enqueue(s: Seq[AbstractState],
              clause: NormClause, assumptions: Conjunction): Unit = {
    states += ((s, clause, assumptions, time))
  }

  def enqueue(exp: Expansion): Unit = {
    states += exp
  }

  def dequeue: Expansion =
    states.dequeue

  def removeGarbage(reachableStates: scala.collection.Set[AbstractState]) = {
    val remainingStates = (states.iterator filter {
      case (s, _, _, _) => s forall (reachableStates contains _)
    }).toArray
    states.dequeueAll
    states ++= remainingStates
  }

  override def incTime: Unit =
    time = time + 1
}
