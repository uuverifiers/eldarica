package lazabs.horn.graphs

import ap.parser.IAtom
import ap.parser.IExpression.Predicate
import ap.terfor.conjunctions.Conjunction
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{CounterexampleMiner, HornTranslator, NormClause}
import lazabs.horn.graphs.Utils.{getPredAbs, getfileNameWithSuffix, readJSONFile, readJsonFieldInt, writeOneLineJson, writeSMTFormatToFile}
import lazabs.horn.parser.HornReader.fromSMT
import lazabs.horn.preprocessor.HornPreprocessor.Clauses
import lazabs.horn.global.HornClause
import lazabs.horn.graphs.NodeAndEdgeType.graphNameMap

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

    writeSMTFormatToFile(clauses, "simplified")
    val ceLabels = for ((c, i) <- clauses.zipWithIndex) yield {
      if (minedCEs.contains(i)) 1 else 0
    }

    val jsonFileName = GlobalParameters.get.fileName + ".counterExampleIndex.JSON"
    val writer = new PrintWriter(new File(jsonFileName))
    writer.write("{\n")
    writeOneLineJson(head = "clauseNumber", Seq(clauses.length).toString(), writer,changeLine = false)
    writeOneLineJson(head = "counterExampleNumber", Seq(minedCEs.length).toString(), writer,changeLine = false)
    writeOneLineJson(head = "clauseIndices", (0 to clauses.length-1).toString(), writer)
    writeOneLineJson(head = "counterExampleIndices", minedCEs.toString(), writer)
    writeOneLineJson(head = "counterExampleLabels", ceLabels.toString(), writer)
    writeOneLineJson("endField", "[0]",writer,changeLine = false,lastEntry=true)
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


  def readClausesFromFile(suffix: String = ""): Clauses = {
    val fileName = getfileNameWithSuffix(suffix)
    fromSMT(fileName) map ((new HornTranslator).transform(_))
  }

  def getPrunedClauses(clauses: Clauses): Clauses = {
    println(Console.BLUE + "-" * 10 + " getPrunedClauses " + "-" * 10)
    if (GlobalParameters.get.pruneClauses == true) {
      val clausesInCounterExample = getRandomCounterExampleClauses(clauses)
      val prunedClauses = pruneClausesWithSanityCheck(clauses, clausesInCounterExample)
      printPrunedReults(clauses, prunedClauses, clausesInCounterExample)
      prunedClauses

    } else {
      clauses
    }
  }

  def pruneClausesWithSanityCheck(clauses: Clauses, clausesInCounterExample: Clauses): Clauses = {
    //todo: sanity check, keep at least one entrance and exit
    clauses.filterNot(x => clausesInCounterExample.contains(x))
  }

  def getRandomCounterExampleClauses(clauses: Clauses): Clauses = {
    val rand = new scala.util.Random
    if (GlobalParameters.get.fixRandomSeed)
      rand.setSeed(42)
    for (c <- clauses; if rand.nextInt(10) < 5) yield c
  }

  def printPrunedReults(clauses: Clauses, prunedClauses: Clauses, clausesInCounterExample: Clauses): Unit = {
    if (GlobalParameters.get.log) {
      writeSMTFormatToFile(prunedClauses, "pruned")

      println("-" * 10 + " original clauses " + clauses.length + "-" * 10)
      clauses.map(_.toPrologString).foreach(println(_))
      println("-" * 10 + " clauses in counter-examples " + clausesInCounterExample.length + "-" * 10)
      clausesInCounterExample.map(_.toPrologString).foreach(println(_))
      println("-" * 10 + " pruned clauses " + prunedClauses.length + "-" * 10)
      prunedClauses.map(_.toPrologString).foreach(println(_))

    }
  }


}
