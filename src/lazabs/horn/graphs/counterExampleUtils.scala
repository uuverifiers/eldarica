package lazabs.horn.graphs

import lazabs.GlobalParameters
import lazabs.horn.graphs.Utils.writeSMTFormatToFile
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

object counterExampleUtils {

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
      clauses.foreach(println(_))
      println("-" * 10 + " clauses in counter-examples " + clausesInCounterExample.length + "-" * 10)
      clausesInCounterExample.foreach(println(_))
      println("-" * 10 + " pruned clauses " + prunedClauses.length + "-" * 10)
      prunedClauses.foreach(println(_))

    }
  }


}
