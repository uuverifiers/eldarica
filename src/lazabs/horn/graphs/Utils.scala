package lazabs.horn.graphs

import ap.parser.{EquivExpander, IAtom, PartialEvaluator, SMTLineariser, Transform2Prenex}
import ap.terfor.conjunctions.Conjunction
import lazabs.GlobalParameters
import ap.terfor.preds.Predicate
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{CEGAR, HornClauses, HornPredAbs, NormClause}
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

object Utils {


  def writeSMTFormatToFile(simpClauses: Clauses, suffix: String): Unit = {
    val fileName=GlobalParameters.get.fileName.substring(0,GlobalParameters.get.fileName.length-4)+suffix+".smt2"
    println("write " + fileName + " to file")
    val out = new java.io.FileOutputStream(fileName)
    Console.withOut(out) {
      val clauseFors =
        for (c <- simpClauses) yield {
          val f = c.toFormula
          // eliminate remaining operators like eps
          Transform2Prenex(EquivExpander(PartialEvaluator(f)))
        }

      val allPredicates =
        HornClauses allPredicates simpClauses

      SMTLineariser("C_VC", "HORN", "unknown",
        List(), allPredicates.toSeq.sortBy(_.name),
        clauseFors)
    }
    out.close

  }

  def printListMap[A, B](m: Map[A, Seq[B]], title: String = ""): Unit = {
    println("-" * 10 + title + "-" * 10)
    for ((k, v) <- m) {
      println(k)
      for (vv <- v)
        println(vv)
    }
  }

  def getPredAbs(simplifiedClauses:Clauses, simpHints: VerificationHints, disjunctive: Boolean,
                 predGenerator: Dag[AndOrNode[NormClause, Unit]] =>
    Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom, NormClause)]]):
  (HornPredAbs[HornClauses.Clause]) ={
    val counterexampleMethod =
      if (disjunctive)
        CEGAR.CounterexampleMethod.AllShortest
      else
        CEGAR.CounterexampleMethod.FirstBestShortest
    val predAbs =
      new HornPredAbs(simplifiedClauses,
        simpHints.toInitialPredicates, predGenerator,
        counterexampleMethod)
    predAbs
  }

}
