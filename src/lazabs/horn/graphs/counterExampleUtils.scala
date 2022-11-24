package lazabs.horn.graphs

import ap.parser.IAtom
import ap.parser.IExpression.Predicate
import ap.terfor.conjunctions.Conjunction
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{CounterexampleMiner, NormClause}
import lazabs.horn.graphs.Utils.{getPredAbs, writeSMTFormatToFile}
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

object counterExampleUtils {
  object CounterExampleMiningOption extends Enumeration {
    val union, common = Value
  }

  def getClausesInCounterExamples(clauses: Clauses,simpHints: VerificationHints, disjunctive: Boolean, predicateGenerator: Dag[AndOrNode[NormClause, Unit]] =>
    Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom, NormClause)]]): Clauses = {
    //val (_,predGenerator)=getPredAbs(clauses,simpHints,disjunctive,predicateGenerator)
    val CEMiner = new CounterexampleMiner(clauses, predicateGenerator)
    val minedCEs = if (GlobalParameters.get.ceMiningOption == CounterExampleMiningOption.union)
      CEMiner.unionMinimalCounterexampleIndexs
    else
      CEMiner.commonCounterexampleIndexs
    val clausesInCE = for ((c, i) <- clauses.zipWithIndex; if minedCEs.contains(i)) yield c
    printMinedClausesInCounterExamples(clauses,clausesInCE)

    clausesInCE

  }

  def printMinedClausesInCounterExamples(originalClauses: Clauses, minedClauses: Clauses): Unit = {
    if (GlobalParameters.get.log) {
      writeSMTFormatToFile(originalClauses, "simplified")
      writeSMTFormatToFile(minedClauses, "clausesInCEs")
      println("-" * 10 + " original clauses " + originalClauses.length + "-" * 10)
      originalClauses.map(_.toPrologString).foreach(println(_))
      println("-" * 10 + " clauses in counter-examples" + minedClauses.length + "-" * 10)
      minedClauses.map(_.toPrologString).foreach(println(_))
    }

  }

  def getPrunedClauses(clauses: Clauses): Clauses = {
    println(Console.BLUE + "-" * 10 + " getPrunedClauses " + "-" * 10)
    if (GlobalParameters.get.pruneClauses == true) {
      val clausesInCounterExample = getRandomCounterExampleClauses(clauses)
      val prunedClauses = clauses.filterNot(x => clausesInCounterExample.contains(x))
      printPrunedReults(clauses, prunedClauses, clausesInCounterExample)
      prunedClauses

    } else {
      clauses
    }


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
