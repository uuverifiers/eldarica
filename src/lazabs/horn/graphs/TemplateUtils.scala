package lazabs.horn.graphs

import ap.parser.IExpression.Eq

import java.io.{File, FileWriter}
import ap.parser.{IAtom, ITerm, IVariable, Simplifier}
import ap.terfor.preds.Predicate
import ap.types.Sort
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints.{VerifHintTplEqTerm, VerifHintTplInEqTerm, VerifHintTplPredPosNeg}
import lazabs.horn.abstractions.{AbsReader, EmptyVerificationHints, LoopDetector, VerificationHints}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses}
import lazabs.horn.graphs.GraphUtils._

object TemplateUtils {
  val sp = new Simplifier

  def getTemplateMap(clauses: Clauses): Map[String, VerificationHints] = {
    val fileTypeList = Seq("unlabeled", "labeled", "predicted", "mined")
    val unlabeledTemplates = logTime(generateTemplates(clauses),"generate template")
    writeTemplatesToFile(unlabeledTemplates,"unlabeled")
    (for (t <- fileTypeList) yield t -> readTemplateFromFile(clauses, t)).toMap
  }

  def readTemplateFromFile(clauses: Clauses, templateType: String): VerificationHints = {
    val fileName = GlobalParameters.get.fileName +"."+ templateType + ".tpl"
    if (new File(fileName).exists) {
      val name2Pred =
        (for (Clause(head, body, _) <- clauses.iterator;
              IAtom(p, _) <- (head :: body).iterator)
        yield (p.name -> p)).toMap

      val readTemplates = readHints(fileName, name2Pred)
      if (GlobalParameters.get.log)
        printListMap(readTemplates.predicateHints,templateType)
      readTemplates
    } else VerificationHints(Map())
  }

  def readHints(filename: String,
                name2Pred: Map[String, Predicate])
  : VerificationHints = filename match {
    case "" =>
      EmptyVerificationHints
    case hintsFile => {
      val reader = new AbsReader(
        new java.io.BufferedReader(
          new java.io.FileReader(hintsFile)))
      val hints =
        (for ((predName, hints) <- reader.allHints.toSeq.sortBy(_._1).iterator;
              pred = name2Pred get predName;
              if {
                if (pred.isDefined) {
                  if (pred.get.arity != reader.predArities(predName))
                    throw new Exception(
                      "Hints contain predicate with wrong arity: " +
                        predName + " (should be " + pred.get.arity + " but is " +
                        reader.predArities(predName) + ")")
                } else {
                  Console.err.println(
                    "   Ignoring hints for " + predName + "\n")
                }
                pred.isDefined
              }) yield {
          (pred.get, hints)
        }).toMap
      VerificationHints(hints)
    }
  }


  def generateTemplates(simplifiedClauses: Clauses, onlyLoopHead: Boolean = true): VerificationHints = {
    //1. single boolean terms // predicate-2
    //2. single positive and negative integer terms //term
    //3. Eq: integer_term1 +/- integer_term2 =0 //term
    //3. InEq: +/- (integer_term1 +/- integer_term2) >=0  //inequality-term
    val loopHeads =
    if (onlyLoopHead)
      getLoopHeadsWithSort(simplifiedClauses)
    else
      (for (c <- simplifiedClauses; a <- c.allAtoms; if a.pred.name != "FALSE") yield a.pred -> (a.args zip HornPredAbs.predArgumentSorts(a.pred))).distinct

    if (loopHeads.isEmpty) {
      println("-" * 10 + "loopHead empty" + "-" * 10)
      writeLog("Exception: loop head empty")
    }

    VerificationHints((for ((pred, args) <- loopHeads) yield {
      val singleBooleanTerms = for ((a, i) <- args.zipWithIndex; if a._2 == Sort.MultipleValueBool) yield IVariable(i, a._2)
      val singlePositiveTerms = for ((a, i) <- args.zipWithIndex; if a._2 != Sort.MultipleValueBool) yield IVariable(i, a._2)
      val singleNegativeTerms = for ((a, i) <- args.zipWithIndex; if a._2 != Sort.MultipleValueBool) yield -IVariable(i, a._2)
      //val argumentComb=singlePositiveTerms.combinations(2).map(listToTuple2(_)).toSeq
      val (combinationsTermsForEq, combinationsTermsForInEq) = if (singlePositiveTerms.length > 1) {
        val argumentLinearComb = for (t <- singlePositiveTerms.tail) yield (singlePositiveTerms.head, t) //only interact with the first argument
        ((for ((v1, v2) <- argumentLinearComb) yield {
          Seq(v1 - v2, v1 + v2)
        }).flatten,
          (for ((v1, v2) <- argumentLinearComb) yield {
            Seq(v1 - v2, v2 - v1, v1 + v2, -v1 - v2)
          }).flatten)
      } else {
        (Seq(), Seq())
      }

      val allTermsEq = (singlePositiveTerms ++ combinationsTermsForEq).map(sp.apply(_))
      val allTermsInEq = (singlePositiveTerms ++ singleNegativeTerms ++ combinationsTermsForInEq).map(sp.apply(_)) //singleBooleanTerms
      val allTermsPredicate = singleBooleanTerms.map(Eq(_, 0)) //.map(sp.apply(_))
      val allTypeElements = Seq(
        allTermsEq.map(VerifHintTplEqTerm(_, 1)), //term
        allTermsPredicate.map(VerifHintTplPredPosNeg(_, 1)), //predicate-2
        allTermsInEq.map(VerifHintTplInEqTerm(_, 1))) // inequality-term

      pred -> allTypeElements.reduce(_ ++ _)
    }).filterNot(_._2.isEmpty).sortBy(_._1.name).toMap)
  }

  def getLoopHeadsWithSort(simplifiedClauses: Clauses): Seq[(Predicate, Seq[(ITerm, Sort)])] = {
    val loopDetector = new LoopDetector(simplifiedClauses)
    val uniqueAtoms = (for (c <- simplifiedClauses; a <- c.allAtoms) yield a.pred -> (a.args zip HornPredAbs.predArgumentSorts(a.pred))).distinct
    for (a <- uniqueAtoms; if loopDetector.loopHeads.map(_.name).contains(a._1.name)) yield a
  }

  def writeTemplatesToFile(t: VerificationHints, absOption: String): Unit = {
    Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName + "." + absOption + ".tpl")) {
      AbsReader.printHints(t)
    }
  }

  def createNewLogFile(): Unit ={
    new FileWriter(GlobalParameters.get.fileName+".log", false)
  }

  def logTime[A](input: => A,message:String="")={
    val start=System.currentTimeMillis()
    val result = input
    val end = System.currentTimeMillis()
    writeLog(message + " using time:" + (end-start).toString + " milliseconds")
    result
  }

  def writeLog(message:String): Unit ={
    val fw = new FileWriter(GlobalParameters.get.fileName+".log", true)
    try {
      fw.write(message + "\n")
    }
    finally fw.close()
  }

}
