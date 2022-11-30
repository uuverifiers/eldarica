package lazabs.horn.graphs

import ap.parser.IExpression.Predicate
import ap.parser.{IAtom, IExpression, IFormula, SymbolCollector}
import ap.terfor.conjunctions.Conjunction
import lazabs.GlobalParameters
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType
import lazabs.horn.abstractions.VerificationHints.{VerifHintTplEqTerm, VerifHintTplInEqTerm, VerifHintTplInEqTermPosNeg, VerifHintTplPred, VerifHintTplPredPosNeg}
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.{HornPredAbs, NormClause}
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.graphs.Utils.{getClausesAccordingToLabels, readSMTFormatFromFile, writeOneLineJson}
import lazabs.horn.graphs.TemplateUtils._
import lazabs.horn.graphs.counterExampleUtils.{getPredictedCounterExampleClauses, getPrunedClauses}
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import play.api.libs.json.{JsSuccess, JsValue, Json}

import java.io.{File, PrintWriter}

object EvaluateUtils {

  object CombineTemplateStrategy extends Enumeration {
    val union, random, off = Value
  }


  def getSolvability(unsimplifiedClauses: Seq[Clause],
                     originalSimplifiedClauses: Seq[Clause],
                     predGenerator: Dag[AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]]): Unit = {

    val simplifiedClauses = getClausesAccordingToLabels(originalSimplifiedClauses)

    //get pruned clauses from predicted
    val clausesForSolvabilityCheck = getPrunedClauses(simplifiedClauses)

    //get predicate generator from predicted or existed heuristics
    val predGeneratorForSolvabilityCheck = getPredicateGenerator(clausesForSolvabilityCheck, predGenerator)

    println(Console.BLUE + "-" * 10 + " check solvability " + "-" * 10)
    val (solvingTimeFileName, meansureFields, initialFields) = writeInitialFixedFieldsToSolvabilityFile(
      unsimplifiedClauses, simplifiedClauses, clausesForSolvabilityCheck)

    //run CEGAR
    val outStream = Console.err
    val predAbs = Console.withOut(outStream) {
      new HornPredAbs(iClauses = clausesForSolvabilityCheck, initialPredicates = Map(), predicateGenerator = predGeneratorForSolvabilityCheck)
    }


    if (new java.io.File(solvingTimeFileName).exists) { //update the solving time for current abstract option in JSON file
      val satisfiability = predAbs.result match {
        case Left(res) => 1 //SAT
        case Right(cex) => 0 //UNSAT
      }
      val solvingTime = (predAbs.cegar.cegarEndTime - predAbs.cegar.cegarStartTime) //milliseconds
      val cegarIterationNumber = predAbs.cegar.iterationNum
      val generatedPredicateNumber = 0 //predAbs.cegar.generatedPredicateNumber
      val averagePredicateSize = 0 //predAbs.cegar.averagePredicateSize
      val predicateGeneratorTime = predAbs.cegar.predicateGeneratorTime
      val resultList = Seq(solvingTime, cegarIterationNumber, generatedPredicateNumber,
        averagePredicateSize, predicateGeneratorTime, satisfiability).map(_.toInt).map(_.toString)
      for ((m, v) <- meansureFields.zip(resultList)) {
        val newField = {
          m match {
            case "satisfiability"=> {
              if (GlobalParameters.get.hornGraphLabelType==HornGraphLabelType.unsatCore)
                ("satisfiability" + "-" + GlobalParameters.get.hornGraphType.toString, v)
              else
              ("satisfiability", v)
            }
            case _=> (m + "_" + GlobalParameters.get.templateBasedInterpolationType +
              "_" + GlobalParameters.get.hornGraphType + "_" + GlobalParameters.get.combineTemplateStrategy
              + "_" + GlobalParameters.get.explorationRate + "_splitClauses_" + GlobalParameters.get.splitClauses.toString
              + "_cost_" + GlobalParameters.get.readCostType, v)
          }
        }

        val oldFields = readJSONFieldToMap(solvingTimeFileName, fieldNames = initialFields.keys.toSeq)
        val updatedFields =
          if (oldFields.map(_._1).toSeq.contains(newField._1))
            oldFields.updated(newField._1, newField._2)
          else
            (oldFields.toSeq ++ Seq((newField._1, newField._2))).toMap
        writeSolvingTimeToJSON(solvingTimeFileName, updatedFields)

      }
    }

  }

  def writeInitialFixedFieldsToSolvabilityFile(unsimplifiedClauses: Clauses, simplifiedClauses: Clauses, prunedClauses: Clauses): (String, Seq[String], Map[String, String]) = {
    val unlabeledTemplates = readTemplateFromFile(simplifiedClauses, "unlabeled")
    val unlabeledTemplatesStatistics = getVerificationHintsStatistics(unlabeledTemplates)
    val labeledTemplates = readTemplateFromFile(simplifiedClauses, "labeled")
    val labeledTemplatesStatistics = getVerificationHintsStatistics(labeledTemplates)
    val minedTemplates = readTemplateFromFile(simplifiedClauses, "mined")
    val minedTemplatesStatistics = getVerificationHintsStatistics(minedTemplates)
    val solvingTimeFileName = GlobalParameters.get.fileName + "." + "solvability.JSON"
    val fixedFields: Map[String, Int] = Map(
      "satisfiability" -> -1,
      "satisfiability-CDHG" -> -1,
      "satisfiability-CG" -> -1,
      "clauseNumberBeforeSimplification" -> unsimplifiedClauses.length,
      "clauseNumberAfterSimplification" -> simplifiedClauses.length,
      "clauseNumberAfterPruning" -> prunedClauses.length,
      "smt2FileSizeByte" -> new File(GlobalParameters.get.fileName).length().toInt, //bytes,
      "relationSymbolNumberBeforeSimplification" -> (if (unsimplifiedClauses.length != 0) unsimplifiedClauses.map(_.allAtoms.length).reduce(_ + _) else 0),
      "relationSymbolNumberAfterSimplification" ->
        (if (simplifiedClauses.size != 0) simplifiedClauses.map(_.allAtoms.length).reduce(_ + _) else 0),
      "relationSymbolNumberAfterPruning" ->
        (if (prunedClauses.size != 0) prunedClauses.map(_.allAtoms.length).reduce(_ + _) else 0),
      "minedSingleVariableTemplatesNumber" -> minedTemplatesStatistics._1,
      "minedBinaryVariableTemplatesNumber" -> minedTemplatesStatistics._2,
      "minedTemplateNumber" -> minedTemplatesStatistics._3,
      "minedTemplateRelationSymbolNumber" -> minedTemplatesStatistics._4,
      "labeledSingleVariableTemplatesNumber" -> labeledTemplatesStatistics._1,
      "labeledBinaryVariableTemplatesNumber" -> labeledTemplatesStatistics._2,
      "labeledTemplateNumber" -> labeledTemplatesStatistics._3,
      "labeledTemplateRelationSymbolNumber" -> labeledTemplatesStatistics._4,
      "unlabeledSingleVariableTemplatesNumber" -> unlabeledTemplatesStatistics._1,
      "unlabeledBinaryVariableTemplatesNumber" -> unlabeledTemplatesStatistics._2,
      "unlabeledTemplateNumber" -> unlabeledTemplatesStatistics._3,
      "unlabeledTemplateRelationSymbolNumber" -> unlabeledTemplatesStatistics._4)
    val meansureFields = Seq("solvingTime", "cegarIterationNumber", "generatedPredicateNumber",
      "averagePredicateSize", "predicateGeneratorTime", "satisfiability")
    val combianedOptions = Seq("Term", "Octagon", "RelationalEqs", "RelationalIneqs")
    val explorationRate = Seq(0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9)
    val combinedAbstractTypeFields = for (g <- Seq("_CDHG_union_", "_CG_union_"); a <- combianedOptions) yield a + g + "0.0"
    val combinedOffAbstractTypeFields = for (g <- Seq("_CDHG_off_", "_CG_off_"); a <- combianedOptions ++ Seq("PredictedCG", "PredictedCDHG", "Empty", "Unlabeled", "Mined", "Random")) yield a + g + "0.0"
    val randomAbstractTypeFields = for (g <- Seq("_CDHG_random_", "_CG_random_"); e <- explorationRate.map(_.toString); a <- combianedOptions) yield a + g + e
    val AbstractionTypeFields = combinedAbstractTypeFields ++ combinedOffAbstractTypeFields ++ randomAbstractTypeFields
    val splitClausesOption = Seq("splitClauses_0", "splitClauses_1")
    val costOption = Seq("cost_shape", "cost_logit", "cost_same")
    val initialFieldsSeq = (for (m <- meansureFields if m != "satisfiability"; a <- AbstractionTypeFields; s <- splitClausesOption; c <- costOption) yield (m + "_" + a + "_" + s + "_" + c) -> (m, a, s, c)).toMap
    val timeout = 60 * 60 * 3 * 1000 //milliseconds
    val initialFields: Map[String, Int] = (for ((k, v) <- initialFieldsSeq) yield k -> timeout) ++ fixedFields
    val stringlFields: Map[String, String] = Map("unsatCoreThreshold" -> GlobalParameters.get.unsatCoreThreshold.toString)
    val allFields = initialFields.mapValues(_.toString) ++ stringlFields
    if (!new java.io.File(solvingTimeFileName).exists) {
      writeSolvingTimeToJSON(solvingTimeFileName, allFields)
    }
    (solvingTimeFileName, meansureFields, allFields)
  }

  def readJSONFieldToMap(solvingTimeFileName: String, fieldNames: Seq[String] = Seq("RelationalEqs", "Term", "Octagon", "RelationalIneqs", "splitClauses")): Map[String, String] = {
    var fields: Map[String, String] = Map()
    val json_content = scala.io.Source.fromFile(solvingTimeFileName).mkString
    val json_data = Json.parse(json_content)
    for (f <- fieldNames)
      fields = readOneJSONFieldToMap(fieldName = f, fileName = solvingTimeFileName, json_data = json_data, fields = fields)
    fields
  }

  def readOneJSONFieldToMap(fieldName: String, fileName: String, json_data: JsValue, fields: Map[String, String]): Map[String, String] = {
    try {
      val stRelationalEqs = (json_data \ fieldName).validate[Array[String]] match {
        case JsSuccess(st, _) => st
      }
      fields ++ Map(fieldName -> stRelationalEqs.head)
    } catch {
      case _ => fields
    }
  }

  def getVerificationHintsStatistics(verifHints: VerificationHints): (Int, Int, Int, Int) = {
    //predicate-2 matches TplEqTerm, need to be differentiate by Sort if necessary
    var twoVariablesTemplatesList: Seq[IExpression] = Seq()
    var oneVariablesTemplatesList: Seq[IExpression] = Seq()

    def incrementTemplateList(e: IExpression): Unit = {
      if (SymbolCollector.variables(e).size < 2)
        oneVariablesTemplatesList :+= e
      else
        twoVariablesTemplatesList :+= e
    }

    for (e <- verifHints.predicateHints.values.flatten) {
      e match {
        case VerifHintTplPred(ve, cost) => oneVariablesTemplatesList :+= ve
        case VerifHintTplPredPosNeg(ve, cost) => {
          oneVariablesTemplatesList :+= ve
        }
        case VerifHintTplEqTerm(ve, cost) => {
          incrementTemplateList(ve)
        }
        case VerifHintTplInEqTerm(ve, _) => {
          incrementTemplateList(ve)
        }
        case VerifHintTplInEqTermPosNeg(ve, _) => {
          incrementTemplateList(ve)
        }
      }
    }
    (oneVariablesTemplatesList.size, twoVariablesTemplatesList.size, verifHints.predicateHints.values.size, verifHints.predicateHints.keys.size)
  }

  private def writeSolvingTimeToJSON(solvingTimeFileName: String, fields: Map[String, String]): Unit = {
    val writer = new PrintWriter(new File(solvingTimeFileName))
    writer.write("{\n")
    for (f <- fields.dropRight(1)) {
      writeOneLineJson(f._1, "[\"" + f._2 + "\"]", writer, changeLine = true)
    }
    val lastField = fields.last
    writeOneLineJson(lastField._1, "[\"" + lastField._2 + "\"]", writer, changeLine = true, lastEntry = true)
    writer.write("}")
    writer.close()


  }

}
