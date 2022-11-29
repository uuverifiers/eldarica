package lazabs.horn.graphs

import ap.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
import ap.basetypes.IdealInt
import ap.parser.IExpression.Eq

import java.io.{File, FileWriter}
import ap.parser.{IAtom, IConstant, IExpression, IFormula, IIntLit, IPlus, ISortedVariable, ITerm, ITimes, IVariable, Simplifier, SymbolCollector}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.types.Sort
import ap.types.Sort.{:::, AnyBool}
import ap.util.Seqs
import lazabs.GlobalParameters
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, VerifHintTplElement, VerifHintTplEqTerm, VerifHintTplInEqTerm, VerifHintTplInEqTermPosNeg, VerifHintTplPred, VerifHintTplPredPosNeg}
import lazabs.horn.abstractions.{AbsReader, EmptyVerificationHints, LoopDetector, StaticAbstractionBuilder, VerificationHints}
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{CEGAR, DisjInterpolator, HornPredAbs, NormClause, PredicateMiner, TemplateInterpolator}
import lazabs.horn.graphs.EvaluateUtils.CombineTemplateStrategy
import lazabs.horn.graphs.GraphUtils.graphFileNameMap
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import lazabs.horn.graphs.Utils._
import play.api.libs.json.{JsSuccess, Json}

import scala.util.Random

object TemplateUtils {
  val sp = new Simplifier
  val timeoutForPredicateDistinct = 2000 // timeout in milli-seconds used in containsPred

  def generateTemplates(clauses: Clauses): Unit = {
    if (readTemplateFromFile(clauses, "unlabeled").isEmpty) {
      val unlabeledTemplates = logTime(generateUnlabeledTemplates(clauses), "generate template")
      writeTemplatesToFile(unlabeledTemplates, "unlabeled")
    }
    val templateteTypeStr = GlobalParameters.get.templateBasedInterpolationType.toString
    val transformedtemplateTypeStr = templateteTypeStr.substring(0, 1).toLowerCase + templateteTypeStr.substring(1, templateteTypeStr.length)
    val writeTemplate = new StaticAbstractionBuilder(clauses, GlobalParameters.get.templateBasedInterpolationType)
    writeTemplatesToFile(writeTemplate.abstractionHints, transformedtemplateTypeStr)
  }

  def writeTemplateMap(clauses: Clauses): Unit = {
    //notice: templates are only correspond to the original clauses
    val unlabeledTemplates = logTime(generateUnlabeledTemplates(clauses), "generate template")
    writeTemplatesToFile(unlabeledTemplates, "unlabeled")
    val minedTemplates = readTemplateFromFile(clauses, "mined")
    val labeledTemplates = getLabeledTemplates(unlabeledTemplates, minedTemplates)
    writeTemplatesToFile(labeledTemplates, "labeled")
  }

  def readTemplateMap(clauses: Clauses): Map[String, VerificationHints] = {
    //notice: templates are only correspond to the original clauses
    val fileTypeList = Seq("unlabeled", "labeled", "predicted", "mined")
    (for (t <- fileTypeList) yield t -> readTemplateFromFile(clauses, t)).toMap
  }

  def getLabeledTemplates(unlabeled: VerificationHints, mined: VerificationHints): VerificationHints = {
    //filter mined templates by cost
    val filterThreshold = 99
    val filteredMinedTemplates = for ((p, pes) <- mined.predicateHints) yield {
      val filteredElements = for (pe <- pes; if getVerifHintElementContent(pe)._2 < filterThreshold) yield {
        transformBooleanTermToVerifHintTplPredPosNeg(pe)
      }
      p -> filteredElements
    }
    val labeledTemplates = (for ((unlabeledP, unlabeledEs) <- unlabeled.predicateHints) yield {
      val labeledEs = for (f <- filteredMinedTemplates(unlabeledP); if verifHintElementContains(unlabeledEs, f)) yield {
        f
      }
      unlabeledP -> labeledEs
    }).filterNot(x => x._2.isEmpty)
    VerificationHints(labeledTemplates)
  }

  def transformBooleanTermToVerifHintTplPredPosNeg(e: VerifHintElement): VerifHintElement = {
    e match {
      case VerifHintTplEqTerm(term, cost) => {
        term match { //predicate-2 (VerifHintTplPredPosNeg) will match TplEqTerm, differentiate boolean by Sort
          case (e: ITerm) ::: AnyBool(_) => VerifHintTplPredPosNeg(Eq(e, 0), cost)
          case (e: ITerm) => VerifHintTplEqTerm(term, cost)
        }
      }
      case _ => e
    }
  }


  def getVerifHintElementContent(e: VerifHintElement): (IExpression, Int, String) = {
    e match {
      case VerifHintTplPred(e, cost) => (e, cost, "VerifHintTplPred")
      case VerifHintTplPredPosNeg(e, cost) => (e, cost, "VerifHintTplPredPosNeg")
      case VerifHintTplEqTerm(term, cost) => {
        term match { //predicate-2 (VerifHintTplPredPosNeg) will match TplEqTerm, differentiate boolean by Sort
          case (e: ITerm) ::: AnyBool(_) => (Eq(e, 0), cost, "VerifHintTplPredPosNeg")
          case (e: ITerm) => (e, cost, "VerifHintTplEqTerm")
        }
      }
      case VerifHintTplInEqTerm(e, cost) => (e, cost, "VerifHintTplInEqTerm")
      case VerifHintTplInEqTermPosNeg(e, cost) => (e, cost, "VerifHintTplInEqTermPosNeg")
    }
  }


  def mineTemplates(simplifiedClauses: Clauses, simpHints: VerificationHints, disjunctive: Boolean,
                    predGenerator: Dag[AndOrNode[NormClause, Unit]] =>
                      Either[Seq[(Predicate, Seq[Conjunction])],
                        Dag[(IAtom, NormClause)]]): Unit = {
    /*
    output mined.tpl
    notice:
     different abstract option cause different mined Templates
     use the abstract option that takes shortest time to solve the problem
     */
    val predAbs = getPredAbs(simplifiedClauses, simpHints, disjunctive, predGenerator)
    val predMiner = new PredicateMiner(predAbs)
    val minedTemplates = predMiner.unitTwoVariableTemplates
    //predMiner.variableTemplates
    writeTemplatesToFile(minedTemplates, "mined")
  }

  def readTemplateLabelFromJSON(simplifiedClauses: Clauses,
                                readLabel: String = "predictedLabel"): VerificationHints = {

    val input_file = GlobalParameters.get.fileName + "." + graphFileNameMap(GlobalParameters.get.hornGraphType) + ".JSON"
    //same sort in AbsReader printHints
    val unlabeledTemplates = readTemplateFromFile(simplifiedClauses, "unlabeled").predicateHints.toSeq sortBy (_._1.name)
    println("read predicted label from " + input_file)
    try {
      val json_content = scala.io.Source.fromFile(input_file).mkString
      val json_data = Json.parse(json_content)
//      val predictedLabel = (json_data \ readLabel).validate[Array[Int]] match {
//        case JsSuccess(templateLabel, _) => templateLabel
//      }
      val predictedLabel=readJsonFieldInt(input_file,readLabel)
      val mapLengthList = for ((k, v) <- unlabeledTemplates) yield v.length
      val splitedPredictedLabel = splitLabel(mapLengthList, predictedLabel)
      val predictedLabelLogit = readJsonFieldDouble(input_file,readLabel+"Logit")
//      (json_data \ (readLabel + "Logit")).validate[Array[Double]] match {
//        case JsSuccess(templateLabel, _) => templateLabel
//      }
      val normalizedPredictedLabelLogit = predictedLabelLogit.map(sigmoid(_))

      val splitedPredictedLabelLogit = splitLabel(mapLengthList, normalizedPredictedLabelLogit)
      val labeledPredicates =
        (for ((((k, v), label), labelLogit) <- unlabeledTemplates zip splitedPredictedLabel zip splitedPredictedLabelLogit) yield {
          k -> (for (((p, l), logit) <- v zip label zip labelLogit if l != 0) yield {
            p match {
              case VerifHintTplEqTerm(t, c) => VerifHintTplEqTerm(t, getCost(t, logit, c))
              case VerifHintTplInEqTerm(t, c) => VerifHintTplInEqTerm(t, getCost(t, logit, c))
              case VerifHintTplPredPosNeg(t, c) => VerifHintTplPredPosNeg(t, getCost(t, logit, c))
            }
          }).distinct //match labels with predicates
        }).filterNot(_._2.isEmpty).toMap //delete empty head
      //add single terms with cost 100
      val reconstructedTemplates = addSingleTermsWithHighestCost(VerificationHints(labeledPredicates))
      if (GlobalParameters.get.log == true) {
        println("input_file", input_file)
        println("predictedLabel", predictedLabel.toList.length, predictedLabel.toList)
        for (x <- splitedPredictedLabel)
          println(x.toSeq, x.size)
        printListMap(labeledPredicates, "labeledTemplates")
        printListMap(reconstructedTemplates.predicateHints, "reconstructedTemplates")
      }
      reconstructedTemplates
    } catch {
      case _ => VerificationHints(Map())
    }
  }

  private def addSingleTermsWithHighestCost(labeledTemplates: VerificationHints): VerificationHints = {
    VerificationHints(for ((pred, templates) <- labeledTemplates.predicateHints) yield {
      val argSorts = HornPredAbs.predArgumentSorts(pred)
      val singleBooleanTerms = for ((a, i) <- argSorts.zipWithIndex; if a == Sort.MultipleValueBool) yield IVariable(i, a)
      val singlePositiveTerms = for ((a, i) <- argSorts.zipWithIndex; if a != Sort.MultipleValueBool) yield IVariable(i, a)
      val singleNegativeTerms = for ((a, i) <- argSorts.zipWithIndex; if a != Sort.MultipleValueBool) yield -IVariable(i, a)
      val allTermsEq = singlePositiveTerms.map(sp.apply(_)).map(VerifHintTplEqTerm(_, 100))
      val allTermsInEq = (singlePositiveTerms ++ singleNegativeTerms).map(sp.apply(_)).map(VerifHintTplInEqTerm(_, 100)) //singleBooleanTerms
      val allTermsPredicate = singleBooleanTerms.map(Eq(_, 0)).map(VerifHintTplPredPosNeg(_, 100)) //.map(sp.apply(_))
      val singleTermsToAdd = for (t <- (allTermsEq ++ allTermsInEq ++ allTermsPredicate); if !verifHintElementContains(templates, t)) yield t
      pred -> (singleTermsToAdd ++ templates)
    })
  }

  private def getCostbyTemplateShape(e: IExpression): Int = {
    2 - SymbolCollector.variables(e).size
  }

  private def getCostByLogitValue(logitValue: Double): Int = {
    100 - (logitValue * 100).toInt
  }

  private def getCost(e: IExpression, logitValue: Double, originalCost: Int): Int = {
    GlobalParameters.get.readCostType match {
      case "shape" => getCostbyTemplateShape(e)
      case "logit" => getCostByLogitValue(logitValue)
      case "same" => originalCost
    }
  }


  def sigmoid(x: Double): Double = {
    math.pow(math.E, x) / (math.pow(math.E, x) + 1)
  }

  private def splitLabel[T](mapLengthList: Seq[Int], readLabel: Array[T]): Seq[Array[T]] = {
    var splitTail = readLabel
    val splitedPredictedLabel = for (l <- mapLengthList) yield {
      val temp = splitTail.splitAt(l)._1
      splitTail = splitTail.splitAt(l)._2
      temp
    }
    splitedPredictedLabel
  }

  def randomLabelTemplates(unlabeledPredicates: VerificationHints, ratio: Double): VerificationHints = {
    val labeledTemplates = for ((k, v) <- unlabeledPredicates.predicateHints) yield {
      val numberOfLabeledTemplates = (v.size * ratio).toInt
      val random = new Random
      if (GlobalParameters.get.fixRandomSeed)
        random.setSeed(42)
      val randomShuffledTemplates = random.shuffle(v)
      k -> (for (i <- 0 to numberOfLabeledTemplates) yield randomShuffledTemplates(i))
    }
    VerificationHints(labeledTemplates)
  }

  def getPredicateGenerator(simplifiedClauses: Clauses, existedPredGenerator: Dag[DisjInterpolator.AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]]):
  Dag[DisjInterpolator.AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]] = {
    println(Console.BLUE + "-"*10+" getPredicateGenerator"+"-"*10)
    val (template, templateGNN) = getPairOfCombTemplates(simplifiedClauses)
    GlobalParameters.get.combineTemplateStrategy match {
      case CombineTemplateStrategy.union => {
        combinedPredicateGenerator(simplifiedClauses, template, templateGNN)
      }
      case CombineTemplateStrategy.random => {
        randomPredicateGenerator(simplifiedClauses, template, templateGNN)
      }
      case CombineTemplateStrategy.off => {
        existedPredGenerator
      }
    }
  }

  def getPairOfCombTemplates(simplifiedClauses: Clauses): (AbstractionMap, AbstractionMap) = {
    val templateGNN = GlobalParameters.get.hornGraphType match {
      case HornGraphType.CG => new StaticAbstractionBuilder(simplifiedClauses, AbstractionType.PredictedCG).abstractionRecords
      case HornGraphType.CDHG => new StaticAbstractionBuilder(simplifiedClauses, AbstractionType.PredictedCDHG).abstractionRecords
    }
    val template = new StaticAbstractionBuilder(simplifiedClauses, GlobalParameters.get.templateBasedInterpolationType).abstractionRecords
    (template, templateGNN)
  }

  def combinedPredicateGenerator(simplifiedClauses: Clauses, template: AbstractionMap, templateGNN: AbstractionMap)
                                (clauseDag: Dag[AndOrNode[NormClause, Unit]])
  : Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]] = {
    val baseInterpolationTimeOut = GlobalParameters.get.templateBasedInterpolationTimeout
    val predgen1 = TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(template, baseInterpolationTimeOut)
    val predgen2 = TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(templateGNN, baseInterpolationTimeOut)

    (predgen1(clauseDag), predgen2(clauseDag)) match {
      case (Left(newPredicate1), Left(newPredicate2)) => {

        val commonHead = (for (p1 <- newPredicate1; p2 <- newPredicate2; if p1._1 == p2._1) yield {
          (p1._1, (p1._2 ++ p2._2).distinct)
        }).distinct
        val p1Unique = for (p1 <- newPredicate1; if !newPredicate2.map(_._1).contains(p1._1)) yield p1
        val p2Unique = for (p2 <- newPredicate2; if !newPredicate1.map(_._1).contains(p2._1)) yield p2
        val mergedPredicates = commonHead ++ p1Unique ++ p2Unique

        Left(mergedPredicates)
      }
      case (Right(cex1), Right(cex2)) => {
        Right(cex1)
      }
    }
  }

  def randomPredicateGenerator(simplifiedClauses: Clauses, template: AbstractionMap, templateGNN: AbstractionMap)
                              (clauseDag: Dag[AndOrNode[NormClause, Unit]])
  : Either[Seq[(Predicate, Seq[Conjunction])], //new predicate
    Dag[(IAtom, NormClause)]] = {
    val baseInterpolationTimeOut = GlobalParameters.get.templateBasedInterpolationTimeout
    val predgen1 = TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(template, baseInterpolationTimeOut)
    val predgen2 = TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(templateGNN, baseInterpolationTimeOut)
    (predgen1(clauseDag), predgen2(clauseDag)) match {
      case (Left(newPredicate1), Left(newPredicate2)) => {
        val random = new Random
        if (GlobalParameters.get.fixRandomSeed)
          random.setSeed(42)
        if (random.nextInt(10) < 10 * GlobalParameters.get.explorationRate) {
          Left(newPredicate2)
        } else {
          Left(newPredicate1)
        }
      }
      case (Right(cex1), Right(cex2)) => {
        Right(cex1)
      }
    }
  }

  def readTemplateFromFile(clauses: Clauses, templateType: String): VerificationHints = {
    val fileName = GlobalParameters.get.fileName + "." + templateType + ".tpl"
    if (new File(fileName).exists) {
      val name2Pred =
        (for (Clause(head, body, _) <- clauses.iterator;
              IAtom(p, _) <- (head :: body).iterator)
        yield (p.name -> p)).toMap
      val readTemplates = readHints(fileName, name2Pred)
      val transformedReadTemplates = VerificationHints(for ((k, v) <- readTemplates.predicateHints) yield k -> v.map(transformBooleanTermToVerifHintTplPredPosNeg(_)))
      if (GlobalParameters.get.log)
        printListMap(transformedReadTemplates.predicateHints, templateType)
      transformedReadTemplates
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


  def generateUnlabeledTemplates(simplifiedClauses: Clauses, onlyLoopHead: Boolean = false): VerificationHints = {
    //1. single boolean terms // predicate-2
    //2. single positive and negative integer terms //term
    //3. Eq: integer_term1 +/- integer_term2 =0 //term
    //3. InEq: +/- (integer_term1 +/- integer_term2) >=0  //inequality-term
    val loopHeads =
    if (onlyLoopHead==true)
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

  def createNewLogFile(append: Boolean = false): Unit = {
    new FileWriter(GlobalParameters.get.fileName + ".log", append)
    if (append)
      writeLog("-" * 10)
  }

  def logTime[A](input: => A, message: String = "") = {
    val start = System.currentTimeMillis()
    val result = input
    val end = System.currentTimeMillis()
    writeLog(message + " using time:" + (end - start).toString + " milliseconds")
    result
  }

  def writeLog(message: String): Unit = {
    val fw = new FileWriter(GlobalParameters.get.fileName + ".log", true)
    try {
      fw.write(message + "\n")
    }
    finally fw.close()
  }

  def verifHintElementContains(elementList: Seq[VerifHintElement], target: VerifHintElement): Boolean = {
    val (targetExpression, _, targetType) = getVerifHintElementContent(target)
    elementList.find(x => getVerifHintElementContent(x)._3 == targetType && verifHintElementEq(x, targetExpression)).isDefined
  }

  private def verifHintElementEq(e: VerifHintElement, targetExpression: IExpression): Boolean = {
    e match {
      case VerifHintTplEqTerm(eExpression, _) => {
        (equalTerms(targetExpression.asInstanceOf[ITerm], eExpression)
          || equalMinusTerms(targetExpression.asInstanceOf[ITerm], eExpression))
      }
      case VerifHintTplInEqTerm(eExpression, _) => {
        equalMinusTerms(targetExpression.asInstanceOf[ITerm], eExpression)
      }
      case VerifHintTplPred(eExpression, _) => {
        containsPred(targetExpression.asInstanceOf[IFormula], Seq(eExpression))
      }
      case VerifHintTplPredPosNeg(eExpression, _) => {
        containsPred(targetExpression.asInstanceOf[IFormula], Seq(eExpression))
      }
    }
  }

  private def equalTerms(s: ITerm, t: ITerm): Boolean = {
    noConstantTerm(s) && noConstantTerm(t) &&
      (symbols(s + t) forall { c => constVarCoeff(s, c) == constVarCoeff(t, c) })
  }

  private def equalMinusTerms(s: ITerm, t: ITerm): Boolean = {
    noConstantTerm(s) && noConstantTerm(t) &&
      (symbols(s + t) forall { c => constVarCoeff(s, c) == -constVarCoeff(t, c) })
  }

  private def symbols(t: ITerm): Set[ITerm] = {
    val (vars, consts, _) = SymbolCollector varsConstsPreds t
    (consts.toSet map IConstant) ++ vars.toSet
  }

  private def constVarCoeff(t: ITerm, c: ITerm): IdealInt = {
    assert(c.isInstanceOf[IConstant] || c.isInstanceOf[IVariable])
    import IExpression._
    val Sum = SymbolSum(c)
    t match {
      case Sum(coeff, _) => coeff
      case _ => 0
    }
  }

  private def noConstantTerm(t: ITerm): Boolean = t match {
    case _: IIntLit => false
    case IPlus(a, b) => noConstantTerm(a) && noConstantTerm(b)
    case ITimes(_, s) => noConstantTerm(s)
    case _: IConstant | _: IVariable => true
  }

  private def containsPred(pred: IFormula,
                           otherPreds: Iterable[IFormula]): Boolean = try {
    SimpleAPI.withProver { p =>
      implicit val _ = p
      import p._
      import IExpression._
      var qCounter = 0
      val predSyms =
        SymbolCollector.variables(pred) ++ SymbolCollector.constants(pred)

      withTimeout(timeoutForPredicateDistinct) {
        otherPreds exists {
          q => {
            //println(Console.GREEN + "q",qCounter,q)
            qCounter = qCounter + 1
            val qSyms =
              SymbolCollector.variables(q) ++ SymbolCollector.constants(q)

            if (!predSyms.isEmpty && !qSyms.isEmpty &&
              Seqs.disjoint(predSyms, qSyms)) {
              // if the predicates do not share any symbols, we can
              // assume they are not equivalent
              false
            } else scope {
              //val c = pred <=> q
              val c = (pred <=> q) ||| (pred == q)
              val vars =
                SymbolCollector.variables(c)

              // replace variables with constants
              val varSorts =
                (for (ISortedVariable(n, s) <- vars.iterator)
                  yield (n -> s)).toMap
              val maxVar = if (vars.isEmpty) 0 else
                (for (IVariable(n) <- vars.iterator) yield n).max
              val varSubst =
                (for (n <- 0 to maxVar) yield (varSorts get n) match {
                  case Some(s) => createConstant(s)
                  case None => v(n)
                }).toList
              ??(subst(c, varSubst, 0))
              //              println("pred",pred)
              //              println("vars",vars)
              //              println("c",c)
              //              if(??? == ProverStatus.Valid)
              //                println("pred",pred,"q",q)
              ??? == ProverStatus.Valid
            }
          }
        }
      }
    }
  } catch {
    case SimpleAPI.TimeoutException => false
  }

}
