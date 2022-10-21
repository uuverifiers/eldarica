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
import ap.util.Seqs
import lazabs.GlobalParameters
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, VerifHintTplElement, VerifHintTplEqTerm, VerifHintTplInEqTerm, VerifHintTplInEqTermPosNeg, VerifHintTplPred, VerifHintTplPredPosNeg}
import lazabs.horn.abstractions.{AbsReader, EmptyVerificationHints, LoopDetector, VerificationHints}
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{CEGAR, HornPredAbs, NormClause, PredicateMiner}
import lazabs.horn.preprocessor.HornPreprocessor.Clauses
import lazabs.horn.graphs.GraphUtils._

object TemplateUtils {
  val sp = new Simplifier
  val timeoutForPredicateDistinct = 2000 // timeout in milli-seconds used in containsPred

  def writeTemplateMap(clauses: Clauses): Unit= {
    //notice: templates are only correspond to the original clauses
    val fileTypeList = Seq("unlabeled", "labeled", "predicted", "mined")
    val unlabeledTemplates = logTime(generateTemplates(clauses), "generate template")
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
        pe
      }
      p -> filteredElements
    }

    val labeledTemplates = (for ((unlabeledP, unlabeledEs) <- unlabeled.predicateHints) yield {
      val labeledEs = for (f <- filteredMinedTemplates(unlabeledP); if VerifHintElementContains(unlabeledEs, f)) yield {
        f
      }
      unlabeledP -> labeledEs
    }).filterNot(x => x._2.isEmpty)
    VerificationHints(labeledTemplates)
  }


  def getVerifHintElementContent(e: VerifHintElement): (IExpression, Int, String) = {
    e match {
      case VerifHintTplPred(e, cost) => (e, cost, "VerifHintTplPred")
      case VerifHintTplPredPosNeg(e, cost) => (e, cost, "VerifHintTplPredPosNeg")
      case VerifHintTplEqTerm(e, cost) => (e, cost, "VerifHintTplEqTerm")
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
    val counterexampleMethod =
      if (disjunctive)
        CEGAR.CounterexampleMethod.AllShortest
      else
        CEGAR.CounterexampleMethod.FirstBestShortest
    val predAbs =
      new HornPredAbs(simplifiedClauses,
        simpHints.toInitialPredicates, predGenerator,
        counterexampleMethod)
    val predMiner = new PredicateMiner(predAbs)
    val minedTemplates = predMiner.unitTwoVariableTemplates
    writeTemplatesToFile(minedTemplates, "mined")
  }

  def readTemplateFromFile(clauses: Clauses, templateType: String): VerificationHints = {
    val fileName = GlobalParameters.get.fileName + "." + templateType + ".tpl"
    if (new File(fileName).exists) {
      val name2Pred =
        (for (Clause(head, body, _) <- clauses.iterator;
              IAtom(p, _) <- (head :: body).iterator)
        yield (p.name -> p)).toMap

      val readTemplates = readHints(fileName, name2Pred)
      if (GlobalParameters.get.log)
        printListMap(readTemplates.predicateHints, templateType)
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

  def createNewLogFile(): Unit = {
    new FileWriter(GlobalParameters.get.fileName + ".log", false)
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

  private def VerifHintElementContains(elementList: Seq[VerifHintElement], target: VerifHintElement): Boolean = {
    var res = false
    val (targetExpression, _, targetType) = getVerifHintElementContent(target)
    for (e <- elementList) {
      val (eExpression, _, eType) = getVerifHintElementContent(e)
      if (eType == targetType) {
        e match {
          case VerifHintTplEqTerm(_, _) => {
            if (equalTerms(targetExpression.asInstanceOf[ITerm], eExpression.asInstanceOf[ITerm])
              || equalMinusTerms(targetExpression.asInstanceOf[ITerm], eExpression.asInstanceOf[ITerm]))
              res = true
          }
          case VerifHintTplInEqTerm(_, _) => {
            if (equalMinusTerms(targetExpression.asInstanceOf[ITerm], eExpression.asInstanceOf[ITerm]))
              res = true
          }
          case VerifHintTplPred(_, _) => {
            if (containsPred(targetExpression.asInstanceOf[IFormula], Seq(eExpression.asInstanceOf[IFormula])))
              res = true
          }
          case VerifHintTplPredPosNeg(_, _) => {
            if (containsPred(targetExpression.asInstanceOf[IFormula], Seq(eExpression.asInstanceOf[IFormula])))
              res = true
          }
        }
      }
    }
    res
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
