package lazabs.horn.graphs

import lazabs.GlobalParameters
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

object counterExampleUtils {

  def getPrunedClauses(clauses: Clauses): Clauses = {
    println(Console.BLUE + "-"*10+" getPrunedClauses "+"-"*10)
    if (GlobalParameters.get.pruneClauses == true) {
      val rand = new scala.util.Random
      if (GlobalParameters.get.fixRandomSeed)
        rand.setSeed(42)
      val clausesInCounterExample = for (c <- clauses; if rand.nextInt(10) < 5) yield c
      val prunedClauses = clauses.filter(x => clausesInCounterExample.contains(x))
      printPrunedReults(clauses,prunedClauses,clausesInCounterExample)
      prunedClauses
    } else {
      clauses
    }


  }

  def printPrunedReults(clauses:Clauses,prunedClauses:Clauses,clausesInCounterExample:Clauses): Unit ={
    if(GlobalParameters.get.log){
      println("-" * 10 + "original clauses" + "-" * 10)
      clauses.foreach(println(_))
      println("-" * 10 + "pruned clauses" + "-" * 10)
      prunedClauses.foreach(println(_))
      println("-" * 10 + "clauses in counter-examples" + "-" * 10)
      clausesInCounterExample.foreach(println(_))
    }
  }


}
