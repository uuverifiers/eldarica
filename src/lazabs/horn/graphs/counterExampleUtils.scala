package lazabs.horn.graphs

import lazabs.GlobalParameters
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

object counterExampleUtils {

  def getPrunedClauses(clauses: Clauses): Clauses = {
    if (GlobalParameters.get.pruneClauses == true) {
      val rand = new scala.util.Random
      if (GlobalParameters.get.fixRandomSeed)
        rand.setSeed(42)
      val clausesInCounterExample = for (c <- clauses; if rand.nextInt(10) < 5) yield c
      val prunedClauses = clauses.filter(x => clausesInCounterExample.contains(x))
      println("-" * 10 + "original clauses" + "-" * 10)
      clausesInCounterExample.foreach(println(_))
      println("-" * 10 + "pruned clauses" + "-" * 10)
      prunedClauses.foreach(println(_))
      prunedClauses
    } else {
      clauses
    }


  }


}
