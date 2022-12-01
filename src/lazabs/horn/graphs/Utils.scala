package lazabs.horn.graphs

import ap.parser.{EquivExpander, IAtom, PartialEvaluator, SMTLineariser, Transform2Prenex}
import ap.terfor.conjunctions.Conjunction
import lazabs.GlobalParameters
import ap.terfor.preds.Predicate
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{CEGAR, HornClauses, HornPredAbs, HornTranslator, NormClause}
import lazabs.horn.graphs.GraphUtils.seqToString
import lazabs.horn.parser.HornReader.fromSMT
import lazabs.horn.preprocessor.HornPreprocessor.Clauses
import play.api.libs.json.{JsSuccess, JsValue, Json}

import java.io.PrintWriter

object Utils {


  def getClausesAccordingToLabels(originalSimplifiedClauses:Clauses): Clauses ={
    GlobalParameters.get.hornGraphLabelType match {
      case HornGraphLabelType.unsatCore => {
        val simplifiedClausesFileName = GlobalParameters.get.fileName + ".simplified"
        if (new java.io.File(simplifiedClausesFileName).exists) // for solvable training data .simplified.smt2 existed
          readSMTFormatFromFile(simplifiedClausesFileName)
        else originalSimplifiedClauses
      }
      case HornGraphLabelType.template => originalSimplifiedClauses
    }
  }
  def readSMTFormatFromFile(fileName:String): Clauses ={
    val _hornTranslator=new HornTranslator
    fromSMT(fileName) map ((_hornTranslator).transform(_))
  }
  def writeSMTFormatToFile(simpClauses: Clauses, suffix: String): Unit = {
    val fileName = GlobalParameters.get.fileName+"."+suffix
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

  def getPredAbs(simplifiedClauses: Clauses, simpHints: VerificationHints, disjunctive: Boolean,
                 predGenerator: Dag[AndOrNode[NormClause, Unit]] =>
                   Either[Seq[(Predicate, Seq[Conjunction])],
                     Dag[(IAtom, NormClause)]]):
  (HornPredAbs[HornClauses.Clause]) = {
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


  def writeOneLineJson(head: String, body: String, writer: PrintWriter, changeLine: Boolean = true, lastEntry: Boolean = false): Unit = {
    if (lastEntry == false) {
      if (changeLine == true)
        writer.write("\"" + head + "\"" + ":\n" + seqToString(body) + "," + "\n")
      else
        writer.write("\"" + head + "\"" + ":" + seqToString(body) + "," + "\n")
    } else {
      writer.write("\"" + head + "\"" + ":\n" + seqToString(body) + "\n")
    }

  }

  def readJSONFile(fileName: String): JsValue = {
    val json_content = scala.io.Source.fromFile(fileName).mkString
    Json.parse(json_content)
  }

  def readJsonFieldInt(fileName: String, readLabelName: String): Array[Int] = {
    val json_data = readJSONFile(fileName)
    val readLabel = (json_data \ readLabelName).validate[Array[Int]] match {
      case JsSuccess(templateLabel, _) => templateLabel
    }
    readLabel
  }

  def readJsonFieldDouble(fileName: String, readLabelName: String): Array[Double] = {
    val json_data = readJSONFile(fileName)
    val readLabel = (json_data \ readLabelName).validate[Array[Double]] match {
      case JsSuccess(templateLabel, _) => templateLabel
    }
    readLabel
  }

}
