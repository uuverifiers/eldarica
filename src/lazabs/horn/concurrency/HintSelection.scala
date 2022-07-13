/**
 * Copyright (c) 2011-2020 Philipp Ruemmer, CHencheng Liang. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 * list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package lazabs.horn.concurrency
import ap.parser.ConstantSubstVisitor
import ap.SimpleAPI.ProverStatus
import ap.{PresburgerTools, Prover, SimpleAPI}
import ap.basetypes.IdealInt
import ap.parser.IExpression.{Predicate, _}
import ap.parser.{IExpression, IFormula, _}
import ap.proof.certificates.ReduceInference
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.theories.TheoryCollector
import ap.types.Sort.MultipleValueBool
import ap.types.Sort.MultipleValueBool.{False, True}
import ap.types.{MonoSortedPredicate, Sort, SortedPredicate, TypeTheory}
import ap.util.{Seqs, Timeout}
import lazabs.GlobalParameters
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, _}
import lazabs.horn.abstractions.{TemplateType, VerificationHints, _}
import lazabs.horn.bottomup
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.CEGAR
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.bottomup.PrincessFlataWrappers.MHashMap
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{HornClauses, _}
import lazabs.horn.concurrency.DrawHornGraph.HornGraphType
import lazabs.horn.concurrency.GraphTranslator.getBatchSize
import lazabs.horn.concurrency.TemplateSelectionUtils.outputPrologFile
import lazabs.horn.preprocessor.{ConstraintSimplifier, HornPreprocessor, SymbolSplitter}
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, NameFactory, VerificationHints, simplify}
import lazabs.horn.preprocessor.SymbolSplitter.{BoolSort, ClausePropagator, concreteArguments, wrapBool}

import java.io.{File, FilenameFilter, PrintWriter}
import java.lang.System.currentTimeMillis
import java.nio.file.{Files, Paths, StandardCopyOption}
import scala.collection.mutable.{ArrayBuffer, LinkedHashMap, HashSet => MHashSet}
import scala.io.Source
import play.api.libs.json._

import scala.collection.immutable.BitSet
import scala.util.Random

case class wrappedHintWithID(ID:Int,head:String, hint:String)

class LiteralCollector extends CollectingVisitor[Unit, Unit] {
  val literals = new MHashSet[IdealInt]
  def postVisit(t : IExpression, arg : Unit,
                subres : Seq[Unit]) : Unit = t match {
    case IIntLit(v)  =>
      literals += v
    case _ => ()
  }
}

object HintsSelection {
  val sp =new Simplifier
  val spAPI = ap.SimpleAPI.spawn
  val cs=new ConstraintSimplifier
  val timeoutForPredicateDistinct = 2000 // timeout in milli-seconds used in containsPred
  def getPredGenerator(absMaps:Seq[AbstractionMap],outStream : java.io.OutputStream):  Util.Dag[DisjInterpolator.AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Util.Dag[(IAtom, NormClause)]] ={
    val predGenerator = Console.withErr(outStream) {
      if (lazabs.GlobalParameters.get.templateBasedInterpolation) {
        val fullAbstractionMap =absMaps.reduce(AbstractionRecord.mergeMaps(_,_))
        if (fullAbstractionMap.isEmpty)
          DagInterpolator.interpolatingPredicateGenCEXAndOr _
        else
          TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
            fullAbstractionMap,
            lazabs.GlobalParameters.get.templateBasedInterpolationTimeout)
      } else {
        DagInterpolator.interpolatingPredicateGenCEXAndOr _
      }
    }
    predGenerator
  }

  def filterInvalidInputs(simplifiedClausesForGraph: Clauses): Unit ={
    //simplified to false<-false
    if (simplifiedClausesForGraph.length==1 && simplifiedClausesForGraph.head.body.isEmpty){
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName, "../benchmarks/exceptions/no-simplified-clauses/" + GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/"), GlobalParameters.get.fileName.length), message = "no-simplified-clauses")
      sys.exit()
    }
    //no argument
//    val argumentList=(for (c<-simplifiedClausesForGraph;a<-c.allAtoms) yield {a.args}).flatten
//    if (argumentList.length==0){
//      HintsSelection.moveRenameFile(GlobalParameters.get.fileName, "../benchmarks/exceptions/no-dataflow/" + GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/"), GlobalParameters.get.fileName.length), message = "no-dataflow")
//      sys.exit()
//    }

  }
  def checkMaxNode(simplifiedClausesForGraph: Clauses): Unit = {
    var totalNodeNumebr = 0
    val clauseNumber = simplifiedClausesForGraph.length
    val preds = (for (c <- simplifiedClausesForGraph) yield {
      c.predicates
    }).flatten
    val totalArgNumber = (for (p <- preds) yield {
      p.arity
    }).sum
    GlobalParameters.get.hornGraphType match { //add differernt number when graph type is differernt
      case DrawHornGraph.HornGraphType.hyperEdgeGraph | DrawHornGraph.HornGraphType.concretizedHyperedgeGraph | DrawHornGraph.HornGraphType.equivalentHyperedgeGraph=> {
        val uniquePred=preds.distinct
        totalNodeNumebr=clauseNumber+uniquePred.length + (for (p <- uniquePred) yield {p.arity}).sum
      }
      case _ =>{
        val headAndBodyNumber= (for(c<-simplifiedClausesForGraph)yield c.allAtoms.length).sum
        totalNodeNumebr=clauseNumber+preds.distinct.length+totalArgNumber+headAndBodyNumber
      }
    }

    if (totalNodeNumebr >= GlobalParameters.get.maxNode) {
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName, "../benchmarks/exceptions/exceed-max-node/" + GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/"), GlobalParameters.get.fileName.length), message = "node number >= maxNode")
      //HintsSelection.removeRelativeFiles(GlobalParameters.get.fileName)
      sys.exit()
    }

  }

  def getAllOptionFold(simplifiedClausesForGraph:Clauses,disjunctive:Boolean):  Map[String, (VerificationHints, StaticAbstractionBuilder)] ={
    println("ap.CmdlMain.version", ap.CmdlMain.version)
    //read from unlabeled .tpl file
    //val simpleGeneratedInitialPredicates=transformPredicateMapToVerificationHints(HintsSelection.wrappedReadHints(simplifiedClausesForGraph,"unlabeledPredicates").toInitialPredicates.mapValues(_.filterNot(_.isTrue).filterNot(_.isFalse)))
    //val fullInitialPredicates = HintsSelection.wrappedReadHints(simplifiedClausesForGraph, "unlabeledPredicates")
    val unlabeledPredicateFileName= ".unlabeledPredicates"
    val labeledPredicateFileName= ".labeledPredicates"
    val fullInitialPredicates =
      if (new java.io.File(GlobalParameters.get.fileName + unlabeledPredicateFileName + ".tpl").exists) {
        HintsSelection. wrappedReadHints(simplifiedClausesForGraph, unlabeledPredicateFileName)
      } else
        HintsSelection.generateCombinationTemplates(simplifiedClausesForGraph)
    val emptyInitialPredicates = VerificationHints(Map())
    val predictedPredicates = HintsSelection.readPredictedHints(simplifiedClausesForGraph, fullInitialPredicates)
    val truePredicates = if ((new java.io.File(GlobalParameters.get.fileName + labeledPredicateFileName + ".tpl")).exists == true)
      HintsSelection.wrappedReadHints(simplifiedClausesForGraph, labeledPredicateFileName) else emptyInitialPredicates
    //val truePredicates = emptyInitialPredicates
    val randomPredicates = HintsSelection.randomLabelTemplates(fullInitialPredicates, 0.2)

    //add other abstract option
    val abstractFold= if (GlobalParameters.get.generateTemplates){
      val abstractTermTemplates=new StaticAbstractionBuilder(simplifiedClausesForGraph, AbstractionType.Term)
      val abstractOctTemplates=new StaticAbstractionBuilder(simplifiedClausesForGraph, AbstractionType.Octagon)
      val abstractrelEqsTemplates=new StaticAbstractionBuilder(simplifiedClausesForGraph, AbstractionType.RelationalEqs)
      val abstractrelIneqsTemplates=new StaticAbstractionBuilder(simplifiedClausesForGraph, AbstractionType.RelationalEqs)
      Map("termInitialPredicates"->(abstractTermTemplates.termAbstractions,abstractTermTemplates),"" +
        "octInitialPredicates"->(abstractOctTemplates.octagonAbstractions,abstractOctTemplates),
        "relEqsInitialPredicates"->(abstractrelEqsTemplates.relationAbstractions(false),abstractrelEqsTemplates),
        "relIneqsInitialPredicates"->(abstractrelIneqsTemplates.relationAbstractions(true),abstractrelIneqsTemplates))
    }else Map()
    val emptyAbsBuilder=new StaticAbstractionBuilder(simplifiedClausesForGraph, AbstractionType.Empty)//could read from coomand line
    val dataFold = abstractFold++
      Map("predictedInitialPredicates" -> (predictedPredicates,emptyAbsBuilder),
        "randomInitialPredicates"->(randomPredicates,emptyAbsBuilder),
        "emptyInitialPredicates" -> (emptyInitialPredicates,emptyAbsBuilder),
        "fullInitialPredicates" -> (fullInitialPredicates,emptyAbsBuilder),
        "trueInitialPredicates" -> (truePredicates,emptyAbsBuilder))

    dataFold
  }

  def getReconstructedInitialTemplatesForPrediction(simplifiedClauses:Clauses,initialTemplates:VerificationHints): VerificationHints ={
    //add single positive terms
    val loopHeadsWithSort= getLoopHeadsWithSort(simplifiedClauses)
    val transformedInitialTemplates = initialTemplates.predicateHints.transform((k,v)=>v.map(getParametersFromVerifHintElement(_)))
    VerificationHints((for ((pred,args) <- loopHeadsWithSort;if initialTemplates.predicateHints.keySet.map(_.name).contains(pred.name)) yield{
      val singleBooleanTerms = for ((a,i)<-args.zipWithIndex; if a._2==Sort.MultipleValueBool) yield IVariable(i,a._2)
      val singlePositiveTerms = for ((a,i)<-args.zipWithIndex; if a._2!=Sort.MultipleValueBool) yield IVariable(i,a._2)
      val allTermsPredicate=singleBooleanTerms.map(Eq(_,0))//.map(sp.apply(_))
      val allTermsEq=(singlePositiveTerms).map(sp.apply(_))//++singleBooleanTerms++allTermsPredicate
      val allTypeElements=for (t<-allTermsEq
                               ;if !HintsSelection.termContains(transformedInitialTemplates(pred),(t,1,TemplateType.TplEqTerm))._1) yield VerifHintTplEqTerm(t,20)
      //val allTypeElements=Seq(allTermsEq.map(VerifHintTplEqTerm(_,20)))
      pred-> (allTypeElements ++ initialTemplates.predicateHints(pred))
    }).sortBy (_._1.name).toMap)
  }

  def randomLabelTemplates(unlabeledPredicates:VerificationHints,ratio:Double): VerificationHints ={
    val labeledTemplates=for((k,v)<-unlabeledPredicates.predicateHints) yield {
      val numberOfLabeledTemplates=(v.size*ratio).toInt
      val randomShuffledTemplates=Random.shuffle(v)
      k-> (for (i<-0 to numberOfLabeledTemplates) yield randomShuffledTemplates(i))
    }
    VerificationHints(labeledTemplates)
  }
  def getLoopHeadsWithSort(simplifiedClauses:Clauses):  Seq[(Predicate, Seq[(ITerm, Sort)])] ={
    val loopDetector = new LoopDetector(simplifiedClauses)
    val uniqueAtoms= (for(c<-simplifiedClauses;a<-c.allAtoms) yield a.pred->(a.args zip HornPredAbs.predArgumentSorts(a.pred)) ).distinct
    for (a<-uniqueAtoms;if loopDetector.loopHeads.map(_.name).contains(a._1.name)) yield a
  }

  def generateCombinationTemplates(simplifiedClauses: Clauses, onlyLoopHead: Boolean = true): VerificationHints = {
    val predicatesForCombTemplateGeneration =
      if (onlyLoopHead)
        getLoopHeadsWithSort(simplifiedClauses)
      else {
        (for (c <- simplifiedClauses; a <- c.allAtoms; if a.pred.name!="FALSE") yield a.pred -> (a.args zip HornPredAbs.predArgumentSorts(a.pred))).distinct
      }

    if (predicatesForCombTemplateGeneration.isEmpty) {
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName, "../benchmarks/exceptions/loop-head-empty/" + getFileName(), "loopHeads is empty")
      sys.exit()
    }
    VerificationHints((for ((pred, args) <- predicatesForCombTemplateGeneration) yield {
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
      //      val combinationsTermsForEq=(for ((v1,v2)<-argumentLinearComb) yield{
      //        Seq(v1-v2,v1+v2)
      //      }).flatten
      //      val combinationsTermsForInEq=(for ((v1,v2)<-argumentLinearComb) yield{
      //        Seq(v1-v2,v2-v1,v1+v2,-v1-v2)
      //      }).flatten
      val allTermsEq = (singlePositiveTerms ++ combinationsTermsForEq).map(sp.apply(_))
      val allTermsInEq = (singlePositiveTerms ++ singleNegativeTerms ++ combinationsTermsForInEq).map(sp.apply(_)) //singleBooleanTerms
      val allTermsPredicate = singleBooleanTerms.map(Eq(_, 0)) //.map(sp.apply(_))
      val allTypeElements = Seq(
        allTermsEq.map(VerifHintTplEqTerm(_, 1)),
        allTermsPredicate.map(VerifHintTplPredPosNeg(_, 1)),
        allTermsInEq.map(VerifHintTplInEqTerm(_, 1)))
      pred -> allTypeElements.reduce(_ ++ _)
    }).filterNot(_._2.isEmpty).sortBy(_._1.name).toMap)
  }

  def resetElementCost(element:VerifHintElement,c:Int):VerifHintElement=element match {
    case VerifHintTplPred(f,cost)=>{VerifHintTplPred(f,c)}
    case VerifHintTplPredPosNeg(f,cost)=>{VerifHintTplPredPosNeg(f,c)}
    case VerifHintTplEqTerm(t,cost)=>{VerifHintTplEqTerm(t,c)}
    case VerifHintTplInEqTerm(t,cost)=>{VerifHintTplInEqTerm(t,c)}
    case VerifHintTplInEqTermPosNeg(t,cost)=>{VerifHintTplInEqTermPosNeg(t,c)}
  }

  def setAllCost(hints : VerificationHints,cost:Int=1): VerificationHints ={
    VerificationHints(for ((pred, els) <- hints.predicateHints) yield {
      val modifiedEls= for(e<-els) yield {
        e match {
          case VerifHintTplEqTerm(t,c)=>VerifHintTplEqTerm(t,cost)
          case VerifHintTplInEqTerm(t,c)=>VerifHintTplInEqTerm(t,cost)
        }
      }
      pred->modifiedEls
    })
}

  def mergeTemplates(hints : VerificationHints) : VerificationHints = {
    val newPredHints =
      (for ((pred, els) <- hints.predicateHints) yield {
        val sorted = els.sortBy {
          case el : VerifHintTplElement => el.cost
          case _ => Int.MinValue
        }

        val res = new ArrayBuffer[VerifHintElement]

        for (el <- sorted) el match {
          case VerifHintTplEqTerm(s, _) =>
            if (!(res exists {
              case VerifHintTplEqTerm(t, _) =>
                equalTerms(s, t) || equalMinusTerms(s, t)
              case _ =>
                false
            })) {
              res += el
            }
          case VerifHintTplInEqTerm(s, _) =>
            if (!(res exists {
              case VerifHintTplInEqTerm(t, _) =>
                equalTerms(s, t)
              case VerifHintTplEqTerm(t, _) =>
                equalTerms(s, t) || equalMinusTerms(s, t)
              case _ =>
                false
            }))
              res += el
        }

        pred -> res.toSeq
      }).toMap

    VerificationHints(newPredHints)
  }

  def equalTerms(s : ITerm, t : ITerm) : Boolean = {
    noConstantTerm(s) && noConstantTerm(t) &&
      (symbols(s + t) forall { c => constVarCoeff(s, c) == constVarCoeff(t, c) })
  }
  def equalMinusTerms(s : ITerm, t : ITerm) : Boolean = {
    noConstantTerm(s) && noConstantTerm(t) &&
      (symbols(s + t) forall { c => constVarCoeff(s, c) == -constVarCoeff(t, c) })
  }

  private def symbols(t : ITerm) : Set[ITerm] = {
    val (vars, consts, _) = SymbolCollector varsConstsPreds t
    (consts.toSet map IConstant) ++ vars.toSet
  }
  private def constVarCoeff(t : ITerm, c : ITerm) : IdealInt = {
    assert(c.isInstanceOf[IConstant] || c.isInstanceOf[IVariable])
    import IExpression._
    val Sum = SymbolSum(c)
    t match {
      case Sum(coeff, _) => coeff
      case _ => 0
    }
  }
  private def noConstantTerm(t : ITerm) : Boolean = t match {
    case _ : IIntLit                   => false
    case IPlus(a, b)                   => noConstantTerm(a) && noConstantTerm(b)
    case ITimes(_, s)                  => noConstantTerm(s)
    case _ : IConstant | _ : IVariable => true
  }


  def getVerificationHintsStatistics(verifHints:VerificationHints): (Int,Int,Int,Int) ={
    //todo: //predicate-2 matches TplEqTerm, need to be differentiate by Sort if necessary
    var twoVariablesTemplatesList:Seq[IExpression]=Seq()
    var oneVariablesTemplatesList:Seq[IExpression]=Seq()
    def incrementTemplateList(e:IExpression): Unit ={
      if (e.length<2)
        oneVariablesTemplatesList:+=e
      else
        twoVariablesTemplatesList:+=e
    }
    for (e<-verifHints.predicateHints.values.flatten){
      val ve =getParametersFromVerifHintElement(e)
      ve._3 match {
        case TemplateType.TplPred=> oneVariablesTemplatesList:+=ve._1
        case TemplateType.TplPredPosNeg =>{oneVariablesTemplatesList:+=ve._1}
        case TemplateType.TplEqTerm => {incrementTemplateList(ve._1)}
        case TemplateType.TplInEqTerm=> {incrementTemplateList(ve._1)}
        case TemplateType.TplInEqTermPosNeg=>{incrementTemplateList(ve._1)}
      }
    }
    (oneVariablesTemplatesList.size,twoVariablesTemplatesList.size,verifHints.totalPredicateNumber,verifHints.totalHeadNumber)
  }

  def getParametersFromVerifHintElement(element:VerifHintElement):(IExpression,Int,TemplateType.Value)=element match {
    case VerifHintTplPred(f,cost)=>{
      //println(Console.BLUE+"TplPred "+f.toString)
      (f,cost,TemplateType.TplPred)}
    case VerifHintTplPredPosNeg(f,cost)=>{
      //println(Console.RED+"TplPredPosNeg "+f.toString)
      (f,cost,TemplateType.TplPredPosNeg)}
    case VerifHintTplEqTerm(t,cost)=>{
      //println(Console.BLUE+"TplEqTerm "+t.toString)
      (t,cost,TemplateType.TplEqTerm)}
    case VerifHintTplInEqTerm(t,cost)=>{
      //println(Console.BLUE+"TplInEqTerm "+t.toString)
      (t,cost,TemplateType.TplInEqTerm)}
    case VerifHintTplInEqTermPosNeg(t,cost)=>{
      //println(Console.BLUE+"TplInEqTermPosNeg "+t.toString)
      (t,cost,TemplateType.TplInEqTermPosNeg)}
  }

  def getInitialPredicates(simplifiedClausesForGraph:Clauses,simpHints:VerificationHints): VerificationHints ={
    if (GlobalParameters.get.readHints == true) {
//      val unlabeledPredicateFileName="-"+HintsSelection.getClauseType()+ ".unlabeledPredicates"
//      val labeledPredicateFileName="-"+HintsSelection.getClauseType()+ ".labeledPredicates"
val unlabeledPredicateFileName=".unlabeledPredicates"
      val labeledPredicateFileName= ".labeledPredicates"
      val initialPredicates = VerificationHints(HintsSelection.wrappedReadHints(simplifiedClausesForGraph, unlabeledPredicateFileName).toInitialPredicates.mapValues(_.map(sp(_)).map(VerificationHints.VerifHintInitPred(_)))) //simplify after read
      val initialHintsCollection = new VerificationHintsInfo(initialPredicates, VerificationHints(Map()), VerificationHints(Map()))
      val truePositiveHints = if (new java.io.File(GlobalParameters.get.fileName + labeledPredicateFileName + ".tpl").exists == true)
        VerificationHints(HintsSelection.wrappedReadHints(simplifiedClausesForGraph, labeledPredicateFileName).toInitialPredicates.mapValues(_.map(sp(_)).map(VerificationHints.VerifHintInitPred(_))))
      else HintsSelection.readPredicateLabelFromOneJSON(initialHintsCollection,"templateRelevanceLabel")
      truePositiveHints
    } else if (GlobalParameters.get.generateSimplePredicates == true) {
      val (simpleGeneratedPredicates, _, _) =
        HintsSelection.getSimplePredicates(simplifiedClausesForGraph,verbose=false,deduplicate = false)
      transformPredicateMapToVerificationHints(simpleGeneratedPredicates) ++simpHints
    }
    else simpHints
  }


  def checkSolvability(simplePredicatesGeneratorClauses: HornPreprocessor.Clauses, originalPredicates: Map[Predicate, Seq[IFormula]],
                       predicateGen: Dag[DisjInterpolator.AndOrNode[NormClause, Unit]] =>
                         Either[Seq[(Predicate, Seq[Conjunction])],
                           Dag[(IAtom, NormClause)]], counterexampleMethod: CEGAR.CounterexampleMethod.Value,outStream:java.io.OutputStream,
                       fileName: String = "noFileName", moveFileFolder: String = "solvability-timeout", moveFile: Boolean = true,
                       exit: Boolean = true, coefficient: Int = 1,message:String=""): (Int, Map[Predicate, Seq[IFormula]], Either[Map[Predicate, IFormula], Dag[(IAtom, Clause)]]) = {
    println("check solvability using current predicates:",message)
    var solveTime = (GlobalParameters.get.solvabilityTimeout / 1000).toInt
    var satisfiability = false
    val solvabilityTimeoutChecker = clonedTimeChecker(GlobalParameters.get.solvabilityTimeout, coefficient)
    val startTime = currentTimeMillis()
    var cegarGeneratedPredicates: Map[Predicate, Seq[IFormula]] = Map()
    var res: Either[Map[Predicate, IFormula], Dag[(IAtom, Clause)]] = Left(Map())
    try GlobalParameters.parameters.withValue(solvabilityTimeoutChecker) {
      val cegar = Console.withOut(outStream) {new HornPredAbs(simplePredicatesGeneratorClauses,
        originalPredicates, predicateGen,
        counterexampleMethod)}
      solveTime = ((currentTimeMillis - startTime) / 1000).toInt
      res = cegar.result
      res match {
        case Left(a) => {
          satisfiability = true
          cegarGeneratedPredicates = transformPredicatesToCanonical(cegar.relevantPredicates, simplePredicatesGeneratorClauses)
        }
        case Right(b) => {
          println(Console.RED + "-" * 10 + "unsat" + "-" * 10)
          if (moveFile == true)
            HintsSelection.moveRenameFile(GlobalParameters.get.fileName, "../benchmarks/exceptions/unsat/" + fileName)
          if (exit == true)
            sys.exit()
        }
      }

    }
    catch {
      case lazabs.Main.TimeoutException => {
        println(Console.RED + "-" * 10 + moveFileFolder + "-" * 10)
        if (moveFile == true)
          HintsSelection.moveRenameFile(GlobalParameters.get.fileName, "../benchmarks/exceptions/" + moveFileFolder + "/" + fileName)
        if (exit == true)
          sys.exit() //throw TimeoutException
        //solveTime = ((currentTimeMillis - startTime) / 1000).toInt
      }
      case _ => println(Console.RED + "-" * 10 + "solvability-debug" + "-" * 10)
    }
    (solveTime, cegarGeneratedPredicates, res)
  }

  def transformPredicatesToCanonical(lastPredicates:Map[Predicate,Seq[IFormula]],simplePredicatesGeneratorClauses: HornPreprocessor.Clauses):
  Map[Predicate, Seq[IFormula]] ={
    val atomList=(for(c<-simplePredicatesGeneratorClauses;a<-c.allAtoms) yield a.pred->a.args).toMap
    val predicateFromCEGAR = for ((head, preds) <- lastPredicates) yield{
      // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
      //val subst = (for ((c, n) <- atomList(head).zipWithIndex) yield (new ConstantTerm(c.toString), IVariable(n))).toMap
      val subst = getSubst(atomList(head),head)
      //val headPredicate=new Predicate(head.name,head.arity) //class Predicate(val name : String, val arity : Int)
      val predicateSequence = for (p <- preds) yield {
        val simplifiedPredicate = spAPI.simplify(p)
        val varPred = ConstantSubstVisitor(simplifiedPredicate, subst) //transform variables to _1,_2,_3...
        varPred
      }
      head -> predicateSequence.distinct.toSeq
    }
    predicateFromCEGAR
  }

  def getSubst(args:Seq[ITerm],pred:Predicate):  Map[ConstantTerm, IVariable] ={
      val sorts = HornPredAbs predArgumentSorts pred
      (for (((IConstant(arg), s), n) <- (args zip sorts).zipWithIndex)
        yield arg -> IVariable(n, s)).toMap
  }

  def measurePredicates(simplePredicatesGeneratorClauses:Clauses,predGenerator:  Dag[DisjInterpolator.AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]],
                        counterexampleMethod: CEGAR.CounterexampleMethod.Value,outStream:java.io.OutputStream,
                        predictedPredicates:VerificationHints,
                        fullPredicates:VerificationHints,
                        minimizedPredicates:VerificationHints,dataFold:Map[String,(VerificationHints,StaticAbstractionBuilder)]): Unit ={
    val(solveTime,_,_)=HintsSelection.checkSolvability(simplePredicatesGeneratorClauses, predictedPredicates.toInitialPredicates, predGenerator, counterexampleMethod, outStream, moveFile = false,message = "")
    val measurementAverageTime= if (solveTime<60) 20 else 5
    for ((fieldName,template)<-dataFold){
      val templatesAbstraction=template._2.loopDetector.hints2AbstractionRecord(template._1)
      val currentGenerator= getPredGenerator(Seq(templatesAbstraction),outStream)
      for (i<-Range(0,20,1)){
        val trial=averageMeasureCEGAR(simplePredicatesGeneratorClauses, Map(), currentGenerator,
          counterexampleMethod,outStream,averageTime = 1,fieldName=fieldName)
        println(i,trial(0))
      }
    }
    println(Console.BLUE+"-----------------------------")
    println(Console.BLUE+"-----------------------------")
    println(Console.BLUE+"-----------------------------")
    val measurementList = if (GlobalParameters.get.generateTemplates) {
      (for ((fieldName,template)<-dataFold) yield {
        val foldName=fieldName.substring(0,fieldName.indexOf("InitialPredicates"))
        val templatesAbstraction=template._2.loopDetector.hints2AbstractionRecord(template._1)
        val currentGenerator= getPredGenerator(Seq(templatesAbstraction),outStream)
        println("--------------------")
//        println("fieldName",fieldName)
//        template._1.pretyPrintHints()
        val currentMeasurement= averageMeasureCEGAR(simplePredicatesGeneratorClauses, Map(), currentGenerator,
          counterexampleMethod,outStream,averageTime = measurementAverageTime,fieldName=fieldName)
        ("measurementWith"+foldName+"Label", currentMeasurement)
      }).toSeq
    } else {
      //val(solveTime,_,_)=HintsSelection.checkSolvability(simplePredicatesGeneratorClauses, predictedPredicates.toInitialPredicates, predGenerator, counterexampleMethod, outStream, moveFile = false)
      //val measurementAverageTime= if (solveTime<60) 20 else 5
      //trails is run in average measuremetnCEGAR
      val measurementWithPredictedLabel = averageMeasureCEGAR(simplePredicatesGeneratorClauses, predictedPredicates.toInitialPredicates, predGenerator, counterexampleMethod,outStream,averageTime=measurementAverageTime)
      val measurementWithEmptyLabel = averageMeasureCEGAR(simplePredicatesGeneratorClauses, Map(), predGenerator, counterexampleMethod,outStream,averageTime=measurementAverageTime)
      val measurementWithFullLabel = averageMeasureCEGAR(simplePredicatesGeneratorClauses, fullPredicates.toInitialPredicates, predGenerator, counterexampleMethod,outStream,averageTime=measurementAverageTime)
      val measurementWithTrueLabel = if (minimizedPredicates.isEmpty) measurementWithEmptyLabel else averageMeasureCEGAR(simplePredicatesGeneratorClauses, minimizedPredicates.toInitialPredicates, predGenerator, counterexampleMethod,outStream,averageTime=measurementAverageTime)

      Seq(("measurementWithtrueLabel", measurementWithTrueLabel), ("measurementWithfullLabel", measurementWithFullLabel),
        ("measurementWithemptyLabel", measurementWithEmptyLabel), ("measurementWithpredictedLabel", measurementWithPredictedLabel))
    }

    HintsSelection.writeMeasurementToJSON(measurementList)
  }
  def getExceptionalPredicatedGenerator():  Dag[AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]] ={
      (x: Dag[DisjInterpolator.AndOrNode[NormClause, Unit]]) =>
        //throw new RuntimeException("interpolator exception")
        throw lazabs.Main.TimeoutException //if catch Counterexample and generate predicates, throw timeout exception
  }
  def getCounterexampleMethod(disjunctive:Boolean):  CEGAR.CounterexampleMethod.Value ={
    if (disjunctive)
      CEGAR.CounterexampleMethod.AllShortest
    else
      CEGAR.CounterexampleMethod.FirstBestShortest
  }
  def getFileName(): String ={
    GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/")+1,GlobalParameters.get.fileName.length)
  }
  def getMinimumSetPredicates(originalPredicates: Map[Predicate, Seq[IFormula]],simplePredicatesGeneratorClauses:Clauses,
                              exceptionalPredGen: Dag[AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]]=getExceptionalPredicatedGenerator(),
                              counterexampleMethod: CEGAR.CounterexampleMethod.Value=getCounterexampleMethod(GlobalParameters.get.disjunctive)):
  (Map[Predicate, Seq[IFormula]],Long) ={
    val startTimeForExtraction = System.currentTimeMillis()
    val mainTimeoutChecker = () => {
      if ((currentTimeMillis - startTimeForExtraction) > GlobalParameters.get.mainTimeout)
        throw lazabs.Main.MainTimeoutException //Main.TimeoutException
    }
    val predicatesExtractingBeginTime=System.currentTimeMillis
    var currentInitialPredicates:Map[Predicate,Seq[IFormula]]=sortHints(originalPredicates)
    var pIndex = 0
    if (!originalPredicates.isEmpty) {
      for ((head, preds) <- sortHints(originalPredicates)) {
        //var leftPredicates:Seq[IFormula]=preds
        for (p <- preds) {
          //delete p and useless predicates
          currentInitialPredicates=currentInitialPredicates.transform((k,v)=>if (k.name==head.name) {
            pIndex = v.indexWhere(x=>x.toString==p.toString)
            v.filterNot(x=>x.toString==p.toString)
          } else v)
          //leftPredicates=leftPredicates.filterNot(x=>x.toString==p.toString)
          //currentInitialPredicates=sortHints(currentInitialPredicates.filterNot(_._1==head)  ++ Map(head->leftPredicates))
          val predicateUsefulnessTimeoutChecker=clonedTimeChecker(GlobalParameters.get.threadTimeout)
          try GlobalParameters.parameters.withValue(predicateUsefulnessTimeoutChecker){
            println("----------------------------------- CEGAR --------------------------------------")
            new HornPredAbs(simplePredicatesGeneratorClauses, currentInitialPredicates, exceptionalPredGen,counterexampleMethod).result
            //p is useless
            mainTimeoutChecker()//check total used time for minimizing process
          }catch{
            case lazabs.Main.TimeoutException=>{
              //p is useful,append p to usefulPredicatesInCurrentHead, add it back to left predicates
              //leftPredicates=leftPredicates.:+(p)
              currentInitialPredicates=currentInitialPredicates.transform((k,v)=>if(k.name==head.name) {
                v.take(pIndex).:+(p) ++ v.drop(pIndex)
                //v.:+(p)
              } else v)
            }
            case _=>{throw lazabs.Main.MainTimeoutException}
          }
        }
        //minimumSetPredicate=minimumSetPredicate++Map(head->leftPredicates)
      }
    }
    val predicatesExtractingTime=(System.currentTimeMillis-predicatesExtractingBeginTime)/1000
    (currentInitialPredicates.mapValues(_.map(sp(_)).filter(!_.isTrue).filter(!_.isFalse)),predicatesExtractingTime)
  }


  def conjunctTwoPredicates(A: Map[Predicate, Seq[IFormula]],
                            B: Map[Predicate, Seq[IFormula]]): Map[Predicate, Seq[IFormula]] = {
    if (A.isEmpty || B.isEmpty)
      Map()
    else
      for ((h, preds) <- A; if B.exists(_._1 == h)) yield {
        h -> (for (p <- preds; if containsPred(p, B(h))) yield p)
      }
  }

  def differentTwoPredicated(A: Map[Predicate, Seq[IFormula]],
                             B: Map[Predicate, Seq[IFormula]]): Map[Predicate, Seq[IFormula]] = {
    if (B.isEmpty)
      A
    else
      for ((h, preds) <- A; if B.exists(_._1 == h)) yield {
        h -> (for (p <- preds; if !containsPred(p, B(h))) yield p)
      }
  }
 

  def printPredicateInMapFormat(p:Map[Predicate,Seq[IExpression]],message:String=""): Unit ={
    println(message)
    for ((h,b)<-p) {
      println(h)
      for (bb<-b)
        println(bb)
    }
  }

  def clonedTimeChecker(to: Int, coefficient: Int = 1): GlobalParameters = {
    val startTimePredicateGenerator = currentTimeMillis
    val clonedGlovalParameter = GlobalParameters.get.clone
    clonedGlovalParameter.timeoutChecker = () => {
      //println("time check point:solvabilityTimeout", ((System.currentTimeMillis - startTimePredicateGenerator)/1000).toString + "/" + ((GlobalParameters.get.solvabilityTimeout * 5)/1000).toString)
      if ((currentTimeMillis - startTimePredicateGenerator) > (to * coefficient)) //timeout seconds
        throw lazabs.Main.TimeoutException //Main.TimeoutException
    }
    clonedGlovalParameter
  }

  def normalizedClausesForGraphs(simplifiedClauses:Clauses,hints:VerificationHints): Clauses ={
    import lazabs.horn.bottomup.HornWrapper._
    GlobalParameters.get.hornGraphType match {
      case HornGraphType.hyperEdgeGraph | HornGraphType.equivalentHyperedgeGraph | HornGraphType.concretizedHyperedgeGraph=>{
        val normalizedHornSMT2FileName = GlobalParameters.get.fileName + "-normalized.smt2"
        if (new java.io.File(normalizedHornSMT2FileName).exists == true && GlobalParameters.get.readSMT2) {
          println("read " + GlobalParameters.get.fileName + "-normalized.smt2")
          lazabs.horn.parser.HornReader.fromSMT(normalizedHornSMT2FileName) map ((new HornTranslator).transform(_))
        }else{
          val uniqueClauses = HintsSelection.distinctByString(simplifiedClauses)
          val (csSimplifiedClauses,_,_)=cs.process(uniqueClauses.distinct,hints)

          val normalized= for (c<-csSimplifiedClauses) yield c.normalize()
          val bodyReplaced=(for ((c,i)<-normalized.zipWithIndex) yield replaceMultiSamePredicateInBody(c,i)).flatten// replace multiple same predicate in body
          val argumentReplaced= for (c<-bodyReplaced) yield DrawHyperEdgeHornGraph.replaceIntersectArgumentInBody(c)
          val simplified= for (c<-argumentReplaced) yield HintsSelection.getSimplifiedClauses(c)
          val normalizedClauses=simplified
          if(GlobalParameters.get.getSMT2){
            HintsSelection.writeSMTFormatToFile(normalizedClauses, GlobalParameters.get.fileName + "-normalized")
            outputPrologFile(normalizedClauses,"normalized")
          }
          normalizedClauses
        }
      }
      case _=>{getSimplifiedSMT2Files(simplifiedClauses)}
    }
  }

  def getSimplifiedSMT2Files(simplifiedClauses: Clauses): Clauses ={
    val simplifiedHornSMT2FileName = GlobalParameters.get.fileName + "-simplified.smt2"
    if (new java.io.File(simplifiedHornSMT2FileName).exists && GlobalParameters.get.readSMT2) {
      println("read " + GlobalParameters.get.fileName + "-simplified.smt2")
      lazabs.horn.parser.HornReader.fromSMT(simplifiedHornSMT2FileName) map ((new HornTranslator).transform(_))
    }else{
      if(GlobalParameters.get.getSMT2){
        HintsSelection.writeSMTFormatToFile(simplifiedClauses, GlobalParameters.get.fileName + "-simplified")
        outputPrologFile(simplifiedClauses,"simplified")
      }
      simplifiedClauses
    }
  }
  def getHornGraphTypeString(): Unit = {
    GlobalParameters.get.hornGraphType match {
      case HornGraphType.hyperEdgeGraph => {}
      case HornGraphType.equivalentHyperedgeGraph => {}
      case HornGraphType.concretizedHyperedgeGraph => {}
      case HornGraphType.monoDirectionLayerGraph=>{}
      case HornGraphType.hybridDirectionLayerGraph=>{}
      case HornGraphType.biDirectionLayerGraph=>{}
      case HornGraphType.clauseRelatedTaskLayerGraph=>{}
      case HornGraphType.fineGrainedEdgeTypeLayerGraph=>{}
    }
  }


  def writeInfoToJSON[A](fields:Seq[(String, A)],suffix:String=""): Unit ={
    val writer = new PrintWriter(new File(GlobalParameters.get.fileName + "." + suffix + ".JSON"))
    writer.write("{\n")
    writeFildToJSON(writer,fields)
    writer.write("}")
    writer.close()
  }

  def writeMeasurementToJSON(measurementList:Seq[(String,Seq[(String, Double)])]): Unit ={
    val writer = new PrintWriter(new File(GlobalParameters.get.fileName + "." + "measurement" + ".JSON"))
    writer.write("{\n")
    for(m<-measurementList.dropRight(1)){
      writer.write(DrawHornGraph.addQuotes(m._1)+": {\n")
      writeFildToJSON(writer,m._2)
      writer.write("},\n")
    }
    val last=measurementList.last
    writer.write(DrawHornGraph.addQuotes(last._1)+": {\n")
    writeFildToJSON(writer,last._2)
    writer.write("}\n")

    writer.write("\n}")
    writer.close()
  }
  def writeFildToJSON[A](writer:PrintWriter,fields:Seq[(String, A)]): Unit ={
    for (field<-fields.dropRight(1)){
      writer.write(DrawHornGraph.addQuotes(field._1)+":"+DrawHornGraph.addQuotes(field._2.toString)+",\n")
    }
    val last=fields.last
    writer.write(DrawHornGraph.addQuotes(last._1)+":"+DrawHornGraph.addQuotes(last._2.toString)+"\n")
  }

  def averageMeasureCEGAR(simplePredicatesGeneratorClauses: HornPreprocessor.Clauses,initialHints: Map[Predicate, Seq[IFormula]],predicateGenerator :  Dag[DisjInterpolator.AndOrNode[NormClause, Unit]]=>
    Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom,NormClause)]],counterexampleMethod : CEGAR.CounterexampleMethod.Value =
  CEGAR.CounterexampleMethod.FirstBestShortest,outStream:java.io.OutputStream,averageTime:Int=20,fieldName:String=""): Seq[Tuple2[String,Double]] ={

    val avg=(for (i<-Range(0,averageTime,1)) yield{
      val mList=measureCEGAR(simplePredicatesGeneratorClauses,initialHints,predicateGenerator,counterexampleMethod,outStream)
      println(fieldName,i)
      println(mList(0))
      for (x<-mList) yield x._2
    }).transpose.map(_.sum/averageTime)
    val measurementNameList=Seq("timeConsumptionForCEGAR","itearationNumber","generatedPredicateNumber","averagePredicateSize","predicateGeneratorTime","averagePredicateSize")
    for((m,name)<-avg.zip(measurementNameList)) yield Tuple2(name,m)
  }

  def measureCEGAR(simplePredicatesGeneratorClauses: HornPreprocessor.Clauses,
                   initialHints: Map[Predicate, Seq[IFormula]],
                   predicateGenerator :  Dag[DisjInterpolator.AndOrNode[NormClause, Unit]] =>
    Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom, NormClause)]],counterexampleMethod : CEGAR.CounterexampleMethod.Value =
  CEGAR.CounterexampleMethod.FirstBestShortest,outStream:java.io.OutputStream): Seq[Tuple2[String,Double]] ={
    val startCEGARTime=currentTimeMillis()
    val Cegar = Console.withOut(outStream){
      new HornPredAbs(simplePredicatesGeneratorClauses,
        initialHints,
        predicateGenerator,
        counterexampleMethod).cegar
    }
    val timeConsumptionForCEGAR=(currentTimeMillis()-startCEGARTime)
    //println(Console.GREEN + "timeConsumptionForCEGAR (ms)",timeConsumptionForCEGAR)
    val measurementList:Seq[Tuple2[String,Double]]=Seq(Tuple2("timeConsumptionForCEGAR",timeConsumptionForCEGAR),Tuple2("itearationNumber",Cegar.iterationNum),
      Tuple2("generatedPredicateNumber",Cegar.generatedPredicateNumber),Tuple2("averagePredicateSize",Cegar.averagePredicateSize),
      Tuple2("predicateGeneratorTime",Cegar.predicateGeneratorTime))

    measurementList
  }

  def getClauseType(): String = {
    GlobalParameters.get.hornGraphType match {
      case HornGraphType.hyperEdgeGraph | HornGraphType.equivalentHyperedgeGraph | HornGraphType.concretizedHyperedgeGraph => "normalized"
      case _ => "simplified"
    }
  }
  def writePredicatesToFiles(unlabeledPredicates:VerificationHints,labeledPredicates:VerificationHints,minedPredicates:VerificationHints,fileName:String=GlobalParameters.get.fileName): Unit ={
    val clauseType = ""//"-"+getClauseType()
    Console.withOut(new java.io.FileOutputStream(fileName+clauseType+".unlabeledPredicates.tpl")) {AbsReader.printHints(unlabeledPredicates)}
    Console.withOut(new java.io.FileOutputStream(fileName+clauseType+".labeledPredicates.tpl")) {AbsReader.printHints(labeledPredicates)}
    if(!minedPredicates.isEmpty)
      Console.withOut(new java.io.FileOutputStream(fileName+clauseType+".minedPredicates.tpl")) {AbsReader.printHints(minedPredicates)}
  }

  def writeTemplateDistributionToFiles(simplifiedClauses:Clauses,initialTemplates:VerificationHints,minedTemplates:VerificationHints): Unit ={
    val loopHeadsWithSort= getLoopHeadsWithSort(simplifiedClauses)
    val predicateWithArgumentSort=(for ((pred,args) <- loopHeadsWithSort) yield {
      val singleBooleanTerms = for ((a, i) <- args.zipWithIndex; if a._2 == Sort.MultipleValueBool) yield IVariable(i, a._2)
      val singleIntegerTerms = for ((a, i) <- args.zipWithIndex; if a._2 != Sort.MultipleValueBool) yield IVariable(i, a._2)
      pred->(singleIntegerTerms,singleBooleanTerms)
    }).toMap

    val integerTermsFromInitialTemplates = (for(p<-initialTemplates.predicateHints.keys;if predicateWithArgumentSort.keys.map(_.name).toSeq.contains(p.name)) yield{
      p->predicateWithArgumentSort(p)._1
    }).filterNot(_._2.isEmpty).toMap
    val booleanTermsFromInitialTemplates = (for(p<-initialTemplates.predicateHints.keys;if predicateWithArgumentSort.keys.map(_.name).toSeq.contains(p.name)) yield{
      p->predicateWithArgumentSort(p)._2
    }).filterNot(_._2.isEmpty).toMap
    val integerTermsFromMinedTemplates=(for((k,singleTerms)<-predicateWithArgumentSort)yield{
      k->{
        for(v<-singleTerms._1;e<-minedTemplates.predicateHints(k);ee=getParametersFromVerifHintElement(e);if ee._2<20&&isAtomaticTerm(ee._1)&&ContainsSymbol(ee._1,v)) yield{
          //println(ee._1,v)
          ee._1
        }
      }
    }).filterNot(_._2.isEmpty)
    val booleanTermsFromMinedTemplates=(for((k,singleTerms)<-predicateWithArgumentSort)yield{
      k->{
        for(v<-singleTerms._2;e<-minedTemplates.predicateHints(k);ee=getParametersFromVerifHintElement(e);if ee._2<20&&ContainsSymbol(ee._1,v)) yield{
          ee._1
        }
      }
    }).filterNot(_._2.isEmpty)


    println("--------------------")
    val integerEqOccurenceInMinedTemplates=(for((k,singleTerms)<-predicateWithArgumentSort)yield{
      k->{
        for(v<-singleTerms._1;e<-minedTemplates.predicateHints(k);ee=getParametersFromVerifHintElement(e);
            if ee._2<20&&isAtomaticTerm(ee._1)&&ContainsSymbol(ee._1,v)&&ee._3==TemplateType.TplEqTerm) yield{
          ee._1
        }
      }
    }).filterNot(_._2.isEmpty)
    if (GlobalParameters.get.debugLog){
      printPredicateInMapFormat(integerEqOccurenceInMinedTemplates,"integerEqOccurenceInMinedTemplates")
      printPredicateInMapFormat(integerTermsFromInitialTemplates,"integerTermsFromInitialTemplates")
      printPredicateInMapFormat(booleanTermsFromInitialTemplates,"booleanTermsFromInitialTemplates")
      printPredicateInMapFormat(integerTermsFromMinedTemplates,"integerTermsFromMinedTemplates")
      printPredicateInMapFormat(booleanTermsFromMinedTemplates,"booleanTermsFromMinedTemplates")
    }


    val fields=Seq(
      ("numberOfIntegerEqOccurenceInMinedTemplates",integerEqOccurenceInMinedTemplates.toMap.values.flatten.size),
      ("numberOfIntegerTermsFromInitialTemplates",integerTermsFromInitialTemplates.toMap.values.flatten.size),
      ("numberOfBooleanTermsFromInitialTemplates",booleanTermsFromInitialTemplates.toMap.values.flatten.size),
      ("numberOfIntegerTermsFromMinedTemplates",integerTermsFromMinedTemplates.toMap.values.flatten.size),
      ("numberOfBooleanTermsFromMinedTemplates",booleanTermsFromMinedTemplates.toMap.values.flatten.size)
    )
    writeInfoToJSON(fields,"TemplatesDistribution")//write to json
  }
  def isAtomaticTerm(e:IExpression):Boolean= e match {
    case  IVariable(i)=>true
    case _ =>false
  }

  def writePredicateDistributionToFiles(initialPredicates:VerificationHints,selectedPredicates:VerificationHints,
                                        labeledPredicates:VerificationHints,unlabeledPredicates:VerificationHints,simpleGeneratedPredicates:VerificationHints,
                                        constraintPredicates:VerificationHints,pairwisePredicate:VerificationHints,
                                        clauses:Clauses,writeToFile:Boolean=true):  Seq[(String, Int)] ={

    val guardMap=
      (for (clause<-clauses) yield{
        val (dataflow,guardList)=HintsSelection.getDataFlowAndGuardWitoutPrint(clause)
        clause->guardList
      }).toMap

    var currentGuardList:Seq[IFormula]=Seq()

    for ((clause,guardList)<-guardMap;atom<-clause.allAtoms){
      val replacedGuardSet=for (g<-guardList) yield{
        //val subst=(for(c<-SymbolCollector.constants(g);(arg,n)<-a.args.zipWithIndex ; if c.name==arg.toString)yield  c->IVariable(n)).toMap
        val subst = getSubst(atom.args,atom.pred)
        predicateQuantify(ConstantSubstVisitor(g,subst))
      }
      currentGuardList=nonredundantSet(currentGuardList,replacedGuardSet)
    }

    val positiveGaurd=for ((k,v)<-selectedPredicates.toInitialPredicates) yield{
      for (vv<-v;if HintsSelection.containsPred(vv,currentGuardList)) yield {k->vv}
    }
    val guardSize=currentGuardList.size//guardMap.values.flatten.size
    val redundantGuardSize=guardMap.values.flatten.size
//    println("guardSize",guardSize)
//    println("positiveGaurd",positiveGaurd.size)


    val initialPredicateSize=initialPredicates.toInitialPredicates.values.flatten.size
    val positiveSimpleGeneratedPredicates=conjunctTwoPredicates(simpleGeneratedPredicates.toInitialPredicates,selectedPredicates.toInitialPredicates)
    val positiveConstraintPredicates = conjunctTwoPredicates(constraintPredicates.toInitialPredicates,selectedPredicates.toInitialPredicates)
    val positiveConstraintPredicatesSize = positiveConstraintPredicates.values.flatten.size
    val positivePairwisePredicateTemp = conjunctTwoPredicates(pairwisePredicate.toInitialPredicates,selectedPredicates.toInitialPredicates)
    val positivePairwisePredicate= for ((k,v)<-positivePairwisePredicateTemp) yield {k->nonredundantSet(Seq(),v)}
    val positivePairwisePredicateSize=positivePairwisePredicate.values.flatten.size

    val predicatesFromCEGAR = differentTwoPredicated(initialPredicates.toInitialPredicates,simpleGeneratedPredicates.toInitialPredicates)
    val predicatesFromCEGARSize = predicatesFromCEGAR.values.flatten.size
    val positivePredicatesFromCEGAR = conjunctTwoPredicates(predicatesFromCEGAR,selectedPredicates.toInitialPredicates)
    val positivePredicatesFromCEGARSize=positivePredicatesFromCEGAR.values.flatten.size

    val differntiatedPairwisePredicates=differentTwoPredicated(simpleGeneratedPredicates.toInitialPredicates,constraintPredicates.toInitialPredicates)
    val differntiatedPairwisePredicatesSize=differntiatedPairwisePredicates.values.flatten.size
    val positiveDifferntiatedPairwisePredicates=conjunctTwoPredicates(differntiatedPairwisePredicates,selectedPredicates.toInitialPredicates)
    val positiveDifferntiatedPairwisePredicatesSize=positiveDifferntiatedPairwisePredicates.values.flatten.size

    val repeatativePairwisePredicates=differentTwoPredicated(pairwisePredicate.toInitialPredicates,differntiatedPairwisePredicates)
    val repeatativePairwisePredicatesSize=repeatativePairwisePredicates.values.flatten.size

    val simpleGeneratedPredicatesSize=simpleGeneratedPredicates.toInitialPredicates.values.flatten.size
    val constraintPredicatesSize=constraintPredicates.toInitialPredicates.values.flatten.size
    val pairwisePredicatesSize=pairwisePredicate.toInitialPredicates.values.flatten.size

    val fields=Seq(
      ("initialPredicates (initial predicatesFromCEGAR, heuristic simpleGeneratedPredicates)",initialPredicateSize),
      ("minimizedPredicates (initialPredicates go through CEGAR Filter)",selectedPredicates.toInitialPredicates.values.flatten.size),
      ("simpleGeneratedPredicates",simpleGeneratedPredicatesSize),
      ("positiveSimpleGeneratedPredicates",positiveSimpleGeneratedPredicates.values.flatten.size),
      ("constraintPredicates",constraintPredicatesSize),
      ("positiveConstraintPredicates",positiveConstraintPredicatesSize),
      ("differentiatedPairwisePredicate",differntiatedPairwisePredicatesSize),
      ("positiveDifferntiatedPairwisePredicatesSize",positiveDifferntiatedPairwisePredicatesSize),
      ("redundantPairwisePredicate",pairwisePredicatesSize),
      ("positiveRedundantPairwisePredicate",positivePairwisePredicateSize),
      ("total guards",guardSize),
      ("redundant guards",redundantGuardSize),
      ("positiveGuards",positiveGaurd.size),
      ("predicatesFromCEGAR",predicatesFromCEGARSize),
      ("positivePredicatesFromCEGAR",positivePredicatesFromCEGARSize),
      ("unlabeledPredicates",unlabeledPredicates.toInitialPredicates.values.flatten.size),
      ("labeledPredicates",labeledPredicates.toInitialPredicates.values.flatten.size)
    )
    if(writeToFile){
      writeInfoToJSON(fields,"predicateDistribution")//write to json
      val writer=new PrintWriter(new File(GlobalParameters.get.fileName + ".predicateDistribution"))//write to file
      writer.println("vary predicates: " + (if(GlobalParameters.get.varyGeneratedPredicates==true) "on" else "off"))
      writer.println("Predicate distributions: ")
      writer.println("initialPredicates (initial predicatesFromCEGAR, heuristic simpleGeneratedPredicates):"+initialPredicateSize.toString)
      writer.println("minimizedPredicates (initialPredicates go through CEGAR Filter):"+selectedPredicates.toInitialPredicates.values.flatten.size.toString)
      writer.println("simpleGeneratedPredicates:"+simpleGeneratedPredicatesSize.toString)
      writer.println("positiveSimpleGeneratedPredicates:"+positiveSimpleGeneratedPredicates.values.flatten.size.toString)
      writer.println("   constraintPredicates:"+constraintPredicatesSize.toString)
      writer.println("       positiveConstraintPredicates:"+positiveConstraintPredicatesSize.toString)
      writer.println("       negativeConstraintPredicates:"+ (constraintPredicatesSize - positiveConstraintPredicatesSize).toString)

      writer.println("   differentiatedPairwisePredicate:"+differntiatedPairwisePredicatesSize.toString)
      writer.println("       positiveDifferentiatedPairwisePredicate:"+positiveDifferntiatedPairwisePredicatesSize.toString)
      writer.println("       negativeDifferentiatedPairwisePredicate:"+ (differntiatedPairwisePredicatesSize - positiveDifferntiatedPairwisePredicatesSize).toString)

      writer.println("   redundantPairwisePredicate:"+pairwisePredicatesSize.toString)
      writer.println("       positiveRedundantPairwisePredicate:"+positivePairwisePredicateSize.toString)
      writer.println("       negativeRedundantPairwisePredicate:"+ (pairwisePredicate.toInitialPredicates.values.flatten.size - positivePairwisePredicateSize).toString)

      //writer.println("   repeatativePairwisePredicatesSize:"+repeatativePairwisePredicatesSize.toString)

      writer.println("predicatesFromCEGAR(initialPredicates - simpleGeneratedPredicates):"+predicatesFromCEGARSize.toString)
      writer.println("       positivePredicatesFromCEGAR:"+positivePredicatesFromCEGARSize.toString)
      writer.println("       negativePredicatesFromCEGAR:"+(predicatesFromCEGAR.values.flatten.size-positivePredicatesFromCEGARSize).toString)

      writer.println("total guards:"+guardSize.toString)
      writer.println("       redundantGuards:"+redundantGuardSize.toString)
      writer.println("       positiveGuards:"+positiveGaurd.size.toString)
      writer.println("       negativeGuards:"+(guardSize-positiveGaurd.size).toString)

      writer.println("unlabeledPredicates:"+unlabeledPredicates.toInitialPredicates.values.flatten.size.toString)
      writer.println("labeledPredicates:"+labeledPredicates.toInitialPredicates.values.flatten.size.toString)
      writer.close()
    }




    if (GlobalParameters.get.debugLog==true){
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".simpleGenerated.tpl")) {
        AbsReader.printHints(simpleGeneratedPredicates)}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".constraintPredicates.tpl")) {
        AbsReader.printHints(constraintPredicates)}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".positiveConstraintPredicates.tpl")) {
        AbsReader.printHints(transformPredicateMapToVerificationHints(positiveConstraintPredicates))}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".argumentConstantEqualPredicate.tpl")) {
        AbsReader.printHints(pairwisePredicate)}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".positiveArgumentConstantEqualPredicate.tpl")) {
        AbsReader.printHints(transformPredicateMapToVerificationHints(positivePairwisePredicate))}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".initial.tpl")) {
        AbsReader.printHints(initialPredicates)}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".predicatesFromCEGAR.tpl")) {
        AbsReader.printHints(transformPredicateMapToVerificationHints(predicatesFromCEGAR))}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".positivePredicatesFromCEGAR.tpl")) {
        AbsReader.printHints(transformPredicateMapToVerificationHints(positivePredicatesFromCEGAR))}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".selected.tpl")) {
        AbsReader.printHints(selectedPredicates)}
    }
    fields
  }


  def intersectPredicatesByString(first: Map[Predicate, Seq[IFormula]],
                                  second:Map[Predicate, Seq[IFormula]]): Map[Predicate, Seq[IFormula]] ={
    for ((fk,fv)<-first;(sk,sv)<-second;if fk.equals(sk)) yield {
      fk->(for (p<-fv if sv.map(_.toString).contains(p.toString)) yield p)
    }
  }

  //associativity
  //replace a-b to -1*x + b
  def varyPredicateWithOutLogicChanges(f: IFormula): IFormula =
    f match {
      case Eq(a, b) => {
        //println(a.toString,"=",b.toString)
        Eq(varyTerm(a), varyTerm(b))
      }
      case Geq(a, b) => {
        //println(a.toString,">=",b.toString)
        Geq(varyTerm(a), varyTerm(b))
      }
      case INot(subformula) => INot(varyPredicateWithOutLogicChanges(subformula))
      case IQuantified(quan, subformula) => IQuantified(quan, varyPredicateWithOutLogicChanges(subformula))
      case IBinFormula(j, f1, f2) => IBinFormula(j, varyPredicateWithOutLogicChanges(f1), varyPredicateWithOutLogicChanges(f2))
      case _ => f
    }


  def varyTerm(e: ITerm): ITerm =
    e match {
      case IPlus(t1, t2) => IPlus(varyTerm(t2), varyTerm(t1))
      case Difference(t1, t2) => IPlus(varyTerm(t1), varyTerm(-1 * t2))
      //case ITimes(coeff, subterm) => ITimes(coeff, varyTerm(subterm))
      case _ => e
    }


  def varyPredicates(optimizedPredicate: Map[Predicate, Seq[IFormula]],verbose:Boolean=false): Map[Predicate, Seq[IFormula]] ={
    val transformedPredicates=optimizedPredicate.mapValues(_.map(HintsSelection.varyPredicateWithOutLogicChanges(_)).map(sp(_)))
    val mergedPredicates= mergePredicateMaps(transformedPredicates,optimizedPredicate)
    if (verbose==true){
      println("predicates before transform")
      transformPredicateMapToVerificationHints(optimizedPredicate).pretyPrintHints()
      //optimizedPredicate.foreach(k=>{println(k._1);k._2.foreach(println)})
      println("transformed predicates")
      transformPredicateMapToVerificationHints(transformedPredicates).pretyPrintHints()
      //transformedPredicates.foreach(k=>{println(k._1);k._2.foreach(println)})
      println("merged predicates")
      transformPredicateMapToVerificationHints(mergedPredicates).pretyPrintHints()
      //mergedPredicates.foreach(k=>{println(k._1);k._2.foreach(println)})
    }
    mergedPredicates.mapValues(distinctByString(_)).mapValues(_.filterNot(_.isFalse).filterNot(_.isTrue))
  }


  def readPredictedHints(simplifiedClausesForGraph: Clauses, fullInitialPredicates: VerificationHints): VerificationHints = {
    val predictedHints = {
      if (new java.io.File(GlobalParameters.get.fileName + "." + "predictedHints" + ".tpl").exists) {
        HintsSelection.wrappedReadHints(simplifiedClausesForGraph, "predictedHints")
        //VerificationHints(HintsSelection.wrappedReadHints(simplifiedClausesForGraph, "predictedHints").toInitialPredicates.mapValues(_.map(sp(_)).map(VerificationHints.VerifHintInitPred(_))))
      } else {
        val initialHintsCollection = new VerificationHintsInfo(fullInitialPredicates, VerificationHints(Map()), VerificationHints(Map()))
        if (GlobalParameters.get.separateByPredicates == true)
          HintsSelection.readPredicateLabelFromMultipleJSON(initialHintsCollection, simplifiedClausesForGraph, "predictedLabel")
        else if (new java.io.File(GlobalParameters.get.fileName + "."+GlobalParameters.get.hornGraphType.toString+".JSON").exists)
          HintsSelection.readPredicateLabelFromOneJSON(initialHintsCollection, "predictedLabel")
        else VerificationHints(Map())
      }
    }
    if (GlobalParameters.get.debugLog == true)
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName + ".predictedHints.tpl")) {
        AbsReader.printHints(predictedHints)
      }
    predictedHints
  }


  def detectIfAJSONFieldExists(readLabel: String = "predictedLabel",fileName:String=GlobalParameters.get.fileName): Boolean ={
    val input_file = fileName+"."+GlobalParameters.get.hornGraphType.toString+".JSON"
    val json_content = scala.io.Source.fromFile(input_file).mkString
    val json_data = Json.parse(json_content)
    try{(json_data \ readLabel).validate[Array[Int]] match {
      case JsSuccess(templateLabel,_)=> true}
    }catch {
      case _=>{
        println("read json file field error")
        false}
    }
  }

  def readPredicateLabelFromMultipleJSON(initialHintsCollection: VerificationHintsInfo,
                                         simplifiedClausesForGraph: Clauses,readLabel:String="predictedLabel"): VerificationHints ={
    //restore predicates from separated files
    val emptyMap:Map[Predicate,Seq[VerifHintElement]]=Map()
    val totalPredicateNumber=initialHintsCollection.initialHints.totalPredicateNumber
    val batch_size=getBatchSize(simplifiedClausesForGraph,totalPredicateNumber)
    val trunk=(totalPredicateNumber/batch_size.toFloat).ceil.toInt
    val fimeNameList= for (t<- (0 until trunk))yield{GlobalParameters.get.fileName+"-"+t.toString}
    val allPositiveList=(for (fileName<-fimeNameList)yield{
      if(new java.io.File(fileName+"."+GlobalParameters.get.hornGraphType.toString+".JSON").exists == true){
        val unlabeledPredicateFileName= ".unlabeledPredicates"
        val currenInitialHints=wrappedReadHints(simplifiedClausesForGraph,unlabeledPredicateFileName,fileName).predicateHints.toSeq sortBy (_._1.name)
        readPredicateLabelFromJSON(fileName, currenInitialHints, readLabel)
      }else{
        emptyMap
      }

    }).reduceLeft(mergePredicateMaps(_,_))
    VerificationHints(allPositiveList)
  }

  def readPredicateLabelFromOneJSON(initialHintsCollection: VerificationHintsInfo,readLabel:String="predictedLabel"): VerificationHints ={
    val initialHints=initialHintsCollection.initialHints.predicateHints.toSeq sortBy (_._1.name)
    VerificationHints(readPredicateLabelFromJSON(GlobalParameters.get.fileName, initialHints, readLabel))
  }


  def readPredicateLabelFromJSON(fileName:String, initialHints:Seq[(Predicate, Seq[VerifHintElement])],
                                 readLabel:String="predictedLabel"): Map[Predicate, Seq[VerifHintElement]]={
    val input_file=fileName+"."+GlobalParameters.get.hornGraphType.toString+".JSON"
    if(detectIfAJSONFieldExists(readLabel,fileName)==true){
      val json_content = scala.io.Source.fromFile(input_file).mkString
      val json_data = Json.parse(json_content)
      val predictedLabel= (json_data \ readLabel).validate[Array[Int]] match {
        case JsSuccess(templateLabel,_)=> templateLabel
      }
      val mapLengthList=for ((k,v)<-initialHints) yield v.length
      var splitTail=predictedLabel
      val splitedPredictedLabel = for(l<-mapLengthList) yield {
        val temp=splitTail.splitAt(l)._1
        splitTail=splitTail.splitAt(l)._2
        temp
      }
      val labeledPredicates=
      if (GlobalParameters.get.readCost){
        val res=(for (((k,v),label)<-initialHints zip splitedPredictedLabel) yield {
          k-> (for((p,l)<-v zip label) yield p match {
            case VerifHintTplEqTerm(t,c)=> VerifHintTplEqTerm(t,l)
            case VerifHintTplInEqTerm(t,c)=>VerifHintTplInEqTerm(t,l)
          })
        }).toMap
        res
      }else{ //read from multi-classification
        val res=(for (((k,v),label)<-initialHints zip splitedPredictedLabel) yield {
          k-> (for ((p,l)<-v zip label if l!=0) yield {
            l match {
              case 1=>{p match {
                case VerifHintTplEqTerm(t,c)=>VerifHintTplEqTerm(t,c)
                case VerifHintTplInEqTerm(t,c)=>VerifHintTplEqTerm(t,c)
                }
              }
              case 2=>{p match {
                case VerifHintTplEqTerm(t,c)=>VerifHintTplInEqTerm(t,c)
                case VerifHintTplInEqTerm(t,c)=>VerifHintTplInEqTerm(t,c)
                }
              }
              case 3|4=>{p}
            }
          } ).distinct //match labels with predicates
        }).filterNot(_._2.isEmpty).toMap //delete empty head
        if(GlobalParameters.get.debugLog==true){
          println("input_file",input_file)
          println("predictedLabel",predictedLabel.toList.length,predictedLabel.toList)
          for (x<-splitedPredictedLabel)
            println(x.toSeq,x.size)
          println("--------Filtered initial predicates---------")
          for((k,v)<-res) {
            println(k)
            for(p<-v)
              println(p)
          }
        }
        res
      }
      labeledPredicates

    }else Map()

  }


  def readPredicateLabelFromJSONBinaryClassification(fileName:String, initialHints:Seq[(Predicate, Seq[VerifHintElement])],
                                 readLabel:String="predictedLabel"): Map[Predicate, Seq[VerifHintElement]]={
    val input_file=fileName+"."+GlobalParameters.get.hornGraphType.toString+".JSON"
    if(detectIfAJSONFieldExists(readLabel,fileName)==true){
      val json_content = scala.io.Source.fromFile(input_file).mkString
      val json_data = Json.parse(json_content)
      val predictedLabel= (json_data \ readLabel).validate[Array[Int]] match {
        case JsSuccess(templateLabel,_)=> templateLabel
      }
      val mapLengthList=for ((k,v)<-initialHints) yield v.length
      var splitTail=predictedLabel
      val splitedPredictedLabel = for(l<-mapLengthList) yield {
        val temp=splitTail.splitAt(l)._1
        splitTail=splitTail.splitAt(l)._2
        temp
      }
      val labeledPredicates=
        if (GlobalParameters.get.readCost){
          val res=(for (((k,v),label)<-initialHints zip splitedPredictedLabel) yield {
            k-> (for((p,l)<-v zip label) yield p match {
              case VerifHintTplEqTerm(t,c)=> VerifHintTplEqTerm(t,l)
              case VerifHintTplInEqTerm(t,c)=>VerifHintTplInEqTerm(t,l)
            })
          }).toMap
          res
        }else{
          val res=(for (((k,v),label)<-initialHints zip splitedPredictedLabel) yield {
            k-> (for ((p,l)<-v zip label if l!=0) yield p
            ) //match labels with predicates
          }).filterNot(_._2.isEmpty).toMap //delete empty head
          if(GlobalParameters.get.debugLog==true){
            println("input_file",input_file)
            println("predictedLabel",predictedLabel.toList.length,predictedLabel.toList)
            for (x<-splitedPredictedLabel)
              println(x.toSeq,x.size)
            println("--------Filtered initial predicates---------")
            for((k,v)<-res) {
              println(k)
              for(p<-v)
                println(p)
            }
          }
          res
        }
      labeledPredicates
    }else Map()
  }

  def wrappedReadHintsCheckExistence(simplifiedClausesForGraph:Seq[Clause],templateTypeName:String,defaultTemplates:VerificationHints): VerificationHints ={
    if (new java.io.File(GlobalParameters.get.fileName +templateTypeName+ ".tpl").exists == true)
      HintsSelection.wrappedReadHints(simplifiedClausesForGraph, templateTypeName)
    else
      defaultTemplates
  }
  def wrappedReadHints(simplifiedClausesForGraph:Seq[Clause],hintType:String="",fileName:String=GlobalParameters.get.fileName):VerificationHints={
    val name2Pred =
      (for (Clause(head, body, _) <- simplifiedClausesForGraph.iterator;
            IAtom(p, _) <- (head :: body).iterator)
        yield (p.name -> p)).toMap
    println("read "+fileName+hintType+".tpl")
    val readHints=HintsSelection.readHints(fileName+hintType+".tpl", name2Pred)
    if (GlobalParameters.get.debugLog)
      readHints.pretyPrintHints()
    readHints
  }

  def readHints(filename : String,
                name2Pred : Map[String, Predicate])
  : VerificationHints = filename match {
    case "" =>
      EmptyVerificationHints
    case hintsFile => {
      val reader = new AbsReader (
        new java.io.BufferedReader (
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

  def predicateQuantify(predicate: IFormula): IFormula = {
    val constants = SymbolCollector.constants(predicate)
    if (constants.isEmpty)
      predicate
    else {
      IExpression.quanConsts(Quantifier.EX, constants, predicate)
    }
  }

  def clauseConstraintQuantify(clause: Clause): IFormula = {
    //println(Console.BLUE + "clauseConstraintQuantify begin")
    SimpleAPI.withProver { p =>
      p.scope {
        p.addConstantsRaw(clause.constants.toSeq.sortBy(_.toString()))
        val constants = for (a <- clause.allAtoms; c <- SymbolCollector.constants(a)) yield c
        try {
          p.withTimeout(5*1000) {
            p.projectEx(clause.constraint, constants)
          }
        }
        catch {
          case SimpleAPI.TimeoutException => clause.constraint
          case _ => clause.constraint
        }
      }
    }
  }
  def getSimplifiedClauses(clause: Clause): Clause = {
    val simplifyedConstraints = clauseConstraintQuantify(clause)
    //println(Console.BLUE + "clauseConstraintQuantify finished")
    Clause(clause.head, clause.body, simplifyedConstraints)
  }


  def replaceMultiSamePredicateInBody(clause: Clause,clauseIndex:Int): Clauses ={
    //if head == body: p(x)<-p(a) => p(x)<-p'(a), p'(a)<-p(a)
    //if multiple same relation symbos in the body: p(x)<-p'(a),p'(b)=> p(x)<-p'(a),p''(b), p''(b)<-p'(b)
    var originalBodyPredicatesList:List[IAtom]=List()
    var renamedBodyPredicatesList:List[IAtom]=List()
    val pbodyStrings= new MHashSet[String]
    pbodyStrings.add(clause.head.pred.name)
    var count=1
    val renamedClauseBodys=for(b<-clause.body)yield{
      if (!pbodyStrings.add(b.pred.name)){ //if there is repeatative body name
        val newPredicateName=b.pred.name+"_"+clauseIndex.toString+"_"+count.toString

        //val renamedBodyPredicate=IAtom(new Predicate(newPredicateName,b.pred.arity),b.args)
        val monosortedPredicate = MonoSortedPredicate(newPredicateName, predArgumentSorts(b.pred))
        val renamedBodyPredicate=IAtom(monosortedPredicate,b.args)

        renamedBodyPredicatesList=renamedBodyPredicatesList:+renamedBodyPredicate
        originalBodyPredicatesList=originalBodyPredicatesList:+b
        count=count+1
        renamedBodyPredicate
      }else{
        b
      }
    }

    val supplementaryClauses= for ((rb,ob)<- renamedBodyPredicatesList zip originalBodyPredicatesList) yield{
      Clause(rb, List(ob), true)}
    Seq(Clause(clause.head, renamedClauseBodys, clause.constraint)) ++ supplementaryClauses
  }
  def getDataFlowAndGuardWitoutPrint(clause: Clause): (Seq[IFormula], Seq[IFormula]) ={
    val normalizedClause=clause.normalize()
    //replace intersect arguments in body and add arg=arg' to constrains
    val replacedClause = DrawHyperEdgeHornGraph.replaceIntersectArgumentInBody(normalizedClause)
    val simplifyedClauses=getSimplifiedClauses(replacedClause)
    val finalSimplifiedClauses=simplifyedClauses //change to replacedClause see not simplified constraints
    var dataflowList = Set[IFormula]()
    var guardList = Set[IFormula]()
    val bodySymbolsSet = (for (body <- finalSimplifiedClauses.body; arg <- body.args) yield arg).toSet
    var counter=0
    for (x <- finalSimplifiedClauses.head.args) {
      val SE = IExpression.SymbolEquation(x)
      //for (f <- LineariseVisitor(finalSimplifiedClauses.constraint, IBinJunctor.And)) counter=counter+1
      for (f <- LineariseVisitor(finalSimplifiedClauses.constraint, IBinJunctor.And)) f match {
        case SE(coefficient, rhs) if !coefficient.isZero=> { //<1>
          //counter=counter+1
          if (!(dataflowList.map(_.toString) contains f.toString) // f is not in dataflowList
            && SymbolCollector.constants(rhs).map(_.toString).subsetOf(bodySymbolsSet.map(_.toString)) // <2>
          ) {
            // discovered dataflow from body to x
            dataflowList += f
          }else{
            guardList+=f
          }
        }
        case _ => { guardList+=f//println(Console.BLUE + f)
          //counter=counter+1
        }
      }
    }
    //println("counter",counter)
    //val guardList = (for (f <- LineariseVisitor(finalSimplifiedClauses.constraint, IBinJunctor.And)) yield f).diff(for (df <- dataflowList) yield df)//.map(sp(_))
    val dataFlowSeq = dataflowList.toSeq.sortBy(_.toString)
    val guardSeq = guardList.toSeq.sortBy(_.toString)
    (dataFlowSeq, guardSeq)
  }
  def getSimplePredicates( simplePredicatesGeneratorClauses: HornPreprocessor.Clauses,
                           verbose:Boolean=false,deduplicate:Boolean=true):  (Map[Predicate, Seq[IFormula]],Map[Predicate, Seq[IFormula]],Map[Predicate, Seq[IFormula]]) ={
    println("ap.CmdlMain.version",ap.CmdlMain.version)
    println("begin generating initial predicates")
    val generatePredicatesBeginTime=System.currentTimeMillis
    var constraintPredicates:Map[Predicate,Seq[IFormula]]=Map()
    var pairWiseVariablePredicates:Map[Predicate,Seq[IFormula]]=Map()
    var predicateMap:Map[Predicate,Seq[IFormula]]=Map()

    def addNewPredicateList(pMap: Map[Predicate, Seq[IFormula]], pred: Predicate, newList: Seq[IFormula]): Map[Predicate, Seq[IFormula]] = {
      val distinctedNewList=distinctByString(newList)
      var startMap:Map[Predicate,Seq[IFormula]]=pMap
      if (pMap.keys.map(_.name).toSeq.contains(pred.name)) {
        if(!distinctedNewList.isEmpty) {
          val differntiatedNewList=distinctedNewList.diff(pMap(pred)) //differentiate existed predicates
          //println("startMap(pred)",startMap(pred).size)
          //println("differntiatedNewList",differntiatedNewList.size)
          startMap = pMap.updated(pred, nonredundantSet(pMap(pred), differntiatedNewList))
          //println("startMap(pred) after",startMap(pred).size)
        }
      } else {
        startMap += (pred -> distinctedNewList)
      }
      startMap
    }
    //generate predicates from constraint
    val generatePredicatesFromConstraintBeginTime=System.currentTimeMillis
    for (clause<-simplePredicatesGeneratorClauses;atom<-clause.allAtoms){
      val subst = getSubst(atom.args,atom.pred)
      val argumentReplacedConstraints= ConstantSubstVisitor(clause.constraint,subst)
      val quantifiedConstraints=predicateQuantify(argumentReplacedConstraints)
      val simplifiedConstraint= {
      try{
        spAPI.withTimeout(1000){
          spAPI.simplify(quantifiedConstraints)
        }
      }
      catch {case _=>quantifiedConstraints}// new IBoolLit(true)
      }
      val variablesInConstraint = SymbolCollector.variables(simplifiedConstraint)

      val freeVariableReplacedPredicates= {
        if(clause.body.map(_.toString).contains(atom.toString)) {
          (for (p<-LineariseVisitor(simplifiedConstraint.unary_!,IBinJunctor.And)) yield p) ++ (for (p<-LineariseVisitor(simplifiedConstraint,IBinJunctor.And)) yield p.unary_!)
        } else {
          LineariseVisitor(simplifiedConstraint,IBinJunctor.And)
        }
      }.map(spAPI.simplify(_)).filterNot(_.isFalse).filterNot(_.isTrue)
//      println("--"+tempCounter+"--")
//      tempCounter=tempCounter+1
//      println("clause",clause.toPrologString)
//      val argsType=for(a<-atom.args) yield if(isArgBoolean(a)) "Bool" else "Int"
//      println("atom",atom,"type",argsType)
//      println("argumentReplacedPredicates",argumentReplacedPredicates)
//      println("quantifiedConstraints",quantifiedConstraints)
      println("simplifiedConstraint",simplifiedConstraint)
//      println("freeVariableReplacedPredicates",freeVariableReplacedPredicates)
      if (atom.args.size>=variablesInConstraint.size){
        if (constraintPredicates.keys.map(_.name).toSeq.contains(atom.pred.name))
            constraintPredicates=constraintPredicates.updated(atom.pred,(constraintPredicates(atom.pred)++freeVariableReplacedPredicates).distinct)
         else
            constraintPredicates=constraintPredicates++Map(atom.pred->freeVariableReplacedPredicates)
      }
    }
    val generatePredicatesFromConstraintTime=(System.currentTimeMillis-generatePredicatesFromConstraintBeginTime)/1000
    //HintsSelection.transformPredicateMapToVerificationHints(constraintPredicates).pretyPrintHints()
    println(Console.BLUE + "number of predicates from constraint:"+(for (k<-constraintPredicates) yield k._2).flatten.size,"time consumption:"+generatePredicatesFromConstraintTime+" s")

    //generate pairwise predicates from constraint
    val generatePredicatesFromPairwiseBeginTime=System.currentTimeMillis
    val integerConstantVisitor = new LiteralCollector
    val variableConstantPairs=Seq((1,1),(-1,1)).map(x=>Tuple2(IdealInt(x._1),IdealInt(x._2)))//(-1,-1), (1,1),(-1,1),(1,-1) is redundant for constant=0 or +-constant
    val constantList= (for(clause <- simplePredicatesGeneratorClauses) yield {
      integerConstantVisitor.visitWithoutResult(clause.constraint,()) //collect integer constant in clause
      val constantListTemp = (integerConstantVisitor.literals.toSeq ++ Seq(IdealInt(0),IdealInt(-1),IdealInt(1)) ++ (for (x<-integerConstantVisitor.literals.toSeq ) yield x.*(-1)))
      integerConstantVisitor.literals.clear()
      constantListTemp
    }).flatten.map(_.intValue).distinct.map(IdealInt(_))
    val uniqueAtoms= (for(clause <- simplePredicatesGeneratorClauses; atom <- clause.allAtoms) yield atom).groupBy(_.pred.name).map(_._2.head)
    for (atom <- uniqueAtoms; if !atom.args.isEmpty){
      val pairVariables=(for ((arg, n) <- atom.args.zipWithIndex) yield (arg,n)).combinations(2).map(listToTuple2(_))
      val preList=
      if (pairVariables.isEmpty) {
        (for ((arg, n) <- atom.args.zipWithIndex; if !isArgBoolean(arg)) yield argumentEquationGenerator(n, constantList)).flatten
      } else {
        //(1,0),(0,1) (-1,0),(0,-1) is redundant for combination
        val singleVariablePredicates= (for ((arg, n) <- atom.args.zipWithIndex;if !isArgBoolean(arg)) yield argumentEquationGenerator(n, constantList)).flatten
        val pairwisePredicates=(for ((v1,v2)<-pairVariables;if !isArgBoolean(v1._1) && !isArgBoolean(v2._1)) yield pairWiseEquationGenerator(v1,v2,variableConstantPairs,constantList)).flatten.toSeq
        singleVariablePredicates++pairwisePredicates
      }

      if (pairWiseVariablePredicates.keys.map(_.name).toSeq.contains(atom.pred.name))
        pairWiseVariablePredicates=pairWiseVariablePredicates.updated(atom.pred,(pairWiseVariablePredicates(atom.pred)++preList).distinct)
      else
        pairWiseVariablePredicates=pairWiseVariablePredicates++Map(atom.pred->preList)
    }
    val generatePredicatesFromPairwiseTime=(System.currentTimeMillis-generatePredicatesFromPairwiseBeginTime)/1000
    println(Console.BLUE + "number of pairwise predicates:"+(for (k<-pairWiseVariablePredicates) yield k._2).flatten.size,"time consumption:"+generatePredicatesFromPairwiseTime+" s")

//    val variedPredicates=
//      if(GlobalParameters.get.varyGeneratedPredicates==true)
//        HintsSelection.varyPredicates(predicateMap)
//      else
//        predicateMap
    val finalGeneratedPredicates=
      if (deduplicate==true) {
        //add constraint predicates to predicateMap
        val deduplicateConstraintPredicateBeginTime=System.currentTimeMillis
        for ((k,v)<-constraintPredicates){
          predicateMap=addNewPredicateList(predicateMap,k,v)
        }
        val deduplicateConstraintPredicateTime=(System.currentTimeMillis-deduplicateConstraintPredicateBeginTime)/1000
        println(Console.BLUE +"adding and deduplicating predicates from constraint to initial predicates, time consumption:"+deduplicateConstraintPredicateTime+" s")
        println(Console.BLUE + "number of predicates in initial predicates:"+(for (k<-predicateMap) yield k._2).flatten.size)
        println("-"*10)
        //add pairwise variable to predicateMap
        val deduplicatePairwisePredicateBeginTime=System.currentTimeMillis
        for ((k,v)<-pairWiseVariablePredicates){
          predicateMap=addNewPredicateList(predicateMap,k,v)
        }
        val deduplicatePairwisePredicateTime=(System.currentTimeMillis-deduplicatePairwisePredicateBeginTime)/1000
        println(Console.BLUE +"adding and deduplicating predicates from pairwise predicates to initial predicates, time consumption:"+deduplicatePairwisePredicateTime+" s")
        //println(Console.BLUE + "number of predicates in initial predicates:"+(for (k<-predicateMap) yield k._2).flatten.size)
        predicateMap
      } else {
        mergePredicateMaps(constraintPredicates,pairWiseVariablePredicates)
      }
    println(Console.BLUE + "number of predicates in initial predicates:"+finalGeneratedPredicates.values.flatten.size)

    val initialPredicateGeneratingTime=(System.currentTimeMillis-generatePredicatesBeginTime)/1000
    println("end generating initial predicates, time consumption",initialPredicateGeneratingTime,"(s)")
    if (verbose==true){
      println("--------predicates from constrains---------")
      for((k,v)<-constraintPredicates;p<-v) println(k,p)
//      println("--------predicates from constant and argumenteEqation---------")
//      for(cc<-argumentConstantEqualPredicate; b<-cc._2) println(cc._1,b)
      println("--------predicates from pairwise variables---------")
      for(cc<-pairWiseVariablePredicates; b<-cc._2) println(cc._1,b)
//      println("--------predicates from merged---------")
//      for(cc<-merge; b<-cc._2) println(cc._1,b)
      println("--------all generated predicates---------")
      for((k,v)<-finalGeneratedPredicates;(p,i)<-v.zipWithIndex) println(k,i,p)
    }
    (finalGeneratedPredicates,constraintPredicates,pairWiseVariablePredicates)
  }
  def mergePredicateMaps[A](first:Map[Predicate,Seq[A]],second:Map[Predicate,Seq[A]]): Map[Predicate,Seq[A]] ={
    if (first.isEmpty)
      second
    else if (second.isEmpty)
      first
    else
      (first.toSeq ++ second.toSeq).groupBy(_._1).map{case(k, v) => k -> v.flatMap(_._2)}
  }

  def distinctByString[A](formulas:Seq[A]): Seq[A] ={
    val FormulaStrings = new MHashSet[String]
    val uniqueFormulas= formulas filter {f => FormulaStrings.add(f.toString)} //de-duplicate formulas
    uniqueFormulas
  }

  def nonredundantSet(startSet : Seq[IFormula], newElements : Seq[IFormula]): Seq[IFormula] = {
    val res = new ArrayBuffer[IFormula]
    res ++= startSet
    //println("startSet",Console.YELLOW + startSet)
    for (q <- newElements) {
      //println("newElements",Console.YELLOW + q)
//      println("res.size",Console.YELLOW + res.size)
//      println("res",Console.YELLOW + res)
      if (!containsPred(q, res)) {
        res += q
      }//else println("q",q)
    }
    res.toSeq
  }

  def termContains(termList: Seq[(IExpression, Int, TemplateType.Value)], term: (IExpression, Int, TemplateType.Value)):
  (Boolean,Int) = {
    var r = false
    var cost=100
    for (t <- termList; if t._3 == term._3) {
      t._3 match {
        case TemplateType.TplInEqTerm => {
          if (HintsSelection.equalTerms(t._1.asInstanceOf[ITerm], term._1.asInstanceOf[ITerm])) {
            r = true
            cost=t._2
          }
        }
        case TemplateType.TplEqTerm => {
          if (HintsSelection.equalTerms(t._1.asInstanceOf[ITerm], term._1.asInstanceOf[ITerm]) ||
            HintsSelection.equalMinusTerms(t._1.asInstanceOf[ITerm], term._1.asInstanceOf[ITerm])) {
            r = true
            cost=t._2
          }
        }
        case TemplateType.TplPred | TemplateType.TplPredPosNeg=>{
          if (containsPred(term._1.asInstanceOf[IFormula], Seq(t._1.asInstanceOf[IFormula]))) {
              r = true
            cost=t._2
          }
        }
      }
    }
    (r,cost)
  }

  def containsPred(pred : IFormula,
                   otherPreds : Iterable[IFormula]): Boolean = try {
    SimpleAPI.withProver { p =>
      implicit val _ = p
      import p._
      import IExpression._
      var qCounter=0
      val predSyms =
        SymbolCollector.variables(pred) ++ SymbolCollector.constants(pred)

      withTimeout(timeoutForPredicateDistinct) {
        otherPreds exists {
          q => {
            //println(Console.GREEN + "q",qCounter,q)
            qCounter=qCounter+1
            val qSyms =
              SymbolCollector.variables(q) ++ SymbolCollector.constants(q)

            if (!predSyms.isEmpty && !qSyms.isEmpty &&
              Seqs.disjoint(predSyms, qSyms)) {
              // if the predicates do not share any symbols, we can
              // assume they are not equivalent
              false
            } else scope {
              //val c = pred <=> q
              val c = (pred <=> q) ||| (pred==q)
              val vars =
                SymbolCollector.variables(c)

              // replace variables with constants
              val varSorts =
                (for (ISortedVariable(n, s) <- vars.iterator)
                  yield (n -> s)).toMap
              val maxVar = if(vars.isEmpty) 0 else
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
  } catch
    {
      case SimpleAPI.TimeoutException => false
    }


  def isArgBoolean(arg: ITerm): Boolean =
    Sort.sortOf(arg) match {
      case Sort.MultipleValueBool => {
        true
      }
      case _ => {
        false
      }
    }

  def argumentEquationGenerator(n:Int,eqConstant:Seq[IdealInt]): Seq[IFormula] ={
      (for (c<-eqConstant) yield Seq(Eq(IVariable(n),c),Geq(IVariable(n),c))).flatten
    //Geq(IVariable(n).minusSimplify,-c)
  }

  def pairWiseEquationGenerator(v1: Tuple2[ITerm,Int], v2: Tuple2[ITerm,Int],variableConstantPairs: Seq[(IdealInt, IdealInt)],constantList: Seq[IdealInt]): Seq[IFormula] ={
    val equations=  for ((v1Const,v2Const)<-variableConstantPairs;c<-constantList; if !(v1Const.intValue<0 &&v2Const.intValue<0 && c.intValue<=0)) yield
      Eq(IPlus(IVariable(v1._2).*(v1Const),IVariable(v2._2).*(v2Const)),c)
    val inequations=for ((v1Const,v2Const)<-variableConstantPairs;c<-constantList) yield
      Geq(IPlus(IVariable(v1._2).*(v1Const),IVariable(v2._2).*(v2Const)),c)
    equations++inequations
  }
  def listToTuple2[A](x:Seq[A]): Tuple2[A,A] = x match {
      case Seq(a, b) => Tuple2(a, b)
    }

  def moveRenameFile(sourceFilename: String, destinationFilename: String,message:String=""): Unit = {
    println(Console.RED+"-"*5+message+"-"*5)
    if (GlobalParameters.get.moveFile==true){
      //println(Console.RED+"-"*5+"file moved"+"-"*5)
      val path = Files.copy(
        Paths.get(sourceFilename),
        Paths.get(destinationFilename),
        StandardCopyOption.REPLACE_EXISTING
      )
      if (path != null) {
        removeRelativeFiles(sourceFilename,true)
        println(s"moved the file $sourceFilename to $destinationFilename successfully")
//        if (GlobalParameters.get.extractTemplates==true || GlobalParameters.get.extractPredicates==true)
//          removeRelativeFiles(sourceFilename)
      } else {
        println(s"could NOT move the file $sourceFilename")
      }
    }
  }
  def removeRelativeFiles(fileName:String,removeSourceFile:Boolean=false): Unit ={
    val currentDirectory = new java.io.File(GlobalParameters.get.fileName).getParentFile.getPath
    val relativeFiles = new java.io.File(currentDirectory).listFiles(new FilenameFilter {
      override def accept(dir: java.io.File, name: String): Boolean = {
        name.startsWith(HintsSelection.getFileName())
      }
    })
    try {
      if (removeSourceFile == true)
        for (file <- relativeFiles)
          Files.delete(file.toPath)
      else
        for (file <- relativeFiles; if file.toString != GlobalParameters.get.fileName)
          Files.delete(file.toPath)
    } catch {
      case _ => println("no relative files")
    }
  }
  def copyRenameFile(sourceFilename: String, destinationFilename: String): Unit = {
    val path = Files.copy(
      Paths.get(sourceFilename),
      Paths.get(destinationFilename),
      StandardCopyOption.REPLACE_EXISTING
    )
    if (path != null) {
      println(s"moved the file $sourceFilename successfully")
    } else {
      println(s"could NOT move the file $sourceFilename")
    }
  }

  def getClausesInCounterExamples(result: Either[Map[Predicate, IFormula], Dag[(IAtom, Clause)]], clauses: Clauses): Clauses = {
    if (result.isRight)
    (result match {
      case Right(cex) => {
        for (node <- cex.subdagIterator; clau <- clauses if (node.d._2.equals(clau))) yield clau
      }
    }).toSeq
    else
      Seq()
  }

  def sortHints[A](hints: A): A =
    hints match {
      case h: VerificationHints => {
        var tempHints = VerificationHints(Map()) //sort the hints
        for ((oneHintKey, oneHintValue) <- h.predicateHints) {
          val tempSeq = oneHintValue.sortBy(_.toString)
          tempHints = tempHints.addPredicateHints(Map(oneHintKey -> tempSeq))
        }
        tempHints.asInstanceOf[A]
      }
      case h: Map[Predicate, Seq[IFormula]] => {
        val sortedByKey = h.toSeq.sortBy(_._1.name)
        (for ((oneHintKey, oneHintValue) <- sortedByKey) yield {
          val tempSeq = oneHintValue.sortBy(_.toString)
          oneHintKey -> tempSeq
        }).toMap.asInstanceOf[A]
      }
    }






  def tryAndTestSelectionTemplates(encoder: ParametricEncoder, simpHints: VerificationHints,
                                   simpClauses: Clauses, file: String, InitialHintsWithID: Seq[wrappedHintWithID], predGenerator: Util.Dag[DisjInterpolator.AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Util.Dag[(IAtom, NormClause)]],
                                   predicateFlag: Boolean = true): (VerificationHints, Either[Map[Predicate, IFormula], Dag[(IAtom, Clause)]]) = {


    val fileName = file.substring(file.lastIndexOf("/") + 1)
    val timeOut = GlobalParameters.get.threadTimeout //timeout
    var currentTemplates = simpHints
    var optimizedTemplates = VerificationHints(Map())
    var PositiveHintsWithID: Seq[wrappedHintWithID] = Seq()
    var NegativeHintsWithID: Seq[wrappedHintWithID] = Seq()

    println("-------------------------Hints selection begins------------------------------------------")
    if (simpHints.isEmpty) {
      val result: Either[Map[Predicate, IFormula], Dag[(IAtom, Clause)]] = Left(Map())
      (simpHints, result)
    } else {
      for ((head, preds) <- simpHints.predicateHints) {
        var criticalTemplatesSeq: Seq[VerifHintElement] = Seq()
        var redundantTemplatesSeq: Seq[VerifHintElement] = Seq()
        for (p <- preds) {
          //delete on template in a head
          val currentTemplatesList = currentTemplates.predicateHints(head).filter(_ != p)
          currentTemplates = currentTemplates.filterNotPredicates(Set(head))

          currentTemplates = currentTemplates.addPredicateHints(Map(head -> currentTemplatesList))

          //try cegar

          val startTime = currentTimeMillis
          val toParams = GlobalParameters.get.clone
          toParams.timeoutChecker = () => {
            if ((currentTimeMillis - startTime) > timeOut ) //timeout milliseconds
              throw lazabs.Main.TimeoutException //Main.TimeoutException
          }
          try {
            GlobalParameters.parameters.withValue(toParams) {
              println(
                "----------------------------------- CEGAR --------------------------------------")

              new HornPredAbs(simpClauses, // loop
                currentTemplates.toInitialPredicates, //emptyHints
                predGenerator).result

              // not timeout ...
              println("Delete a redundant hint:\n" + head + "\n" + p)
              redundantTemplatesSeq = redundantTemplatesSeq ++ Seq(p)

              for (wrappedHint <- InitialHintsWithID) { //add useless hint to NegativeHintsWithID   //ID:head->hint
                if (head.name.toString == wrappedHint.head && wrappedHint.hint == p.toString) {
                  NegativeHintsWithID = NegativeHintsWithID ++ Seq(wrappedHint)
                }
              }


            }

          } catch {
            // ,... Main.TimeoutException
            //time out
            case lazabs.Main.TimeoutException => {
              println("Add a critical hint\n" + head + "\n" + p)
              criticalTemplatesSeq = criticalTemplatesSeq ++ Seq(p)
              currentTemplates = currentTemplates.filterNotPredicates(Set(head))
              //currentTemplates=currentTemplates.filterPredicates(GSet(oneHintKey))
              currentTemplates = currentTemplates.addPredicateHints(Map(head -> (currentTemplatesList ++ Seq(p)))) //beforeDeleteHints

              for (wrappedHint <- InitialHintsWithID) { //add useful hint to PositiveHintsWithID
                if (head.name.toString() == wrappedHint.head && wrappedHint.hint == p.toString) {
                  PositiveHintsWithID = PositiveHintsWithID ++ Seq(wrappedHint)
                }
              }

            }

          } //catch end

        } // second for end
        if (!criticalTemplatesSeq.isEmpty) {
          optimizedTemplates = optimizedTemplates.addPredicateHints(Map(head -> criticalTemplatesSeq))
        }

      } // first for end


      println("\n------------DEBUG-Select critical hints end-------------------------")

      println("\n------------test selected hints-------------------------")
      val result = GlobalParameters.parameters.withValue(GlobalParameters.get.clone) {
        //interpolator
        val interpolator = if (GlobalParameters.get.templateBasedInterpolation)
          Console.withErr(Console.out) {
            val builder =
              new StaticAbstractionBuilder(
                simpClauses,
                GlobalParameters.get.templateBasedInterpolationType)
            val autoAbstractionMap =
              builder.abstractionRecords
            val abstractionMap =
              if (encoder.globalPredicateTemplates.isEmpty) {
                autoAbstractionMap
              } else {
                val loopDetector = builder.loopDetector
                print("Using interpolation templates provided in program: ")
                val hintsAbstractionMap =
                  loopDetector hints2AbstractionRecord currentTemplates //emptyHints criticalHints
                //DEBUG
                println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

                AbstractionRecord.mergeMaps(Map(), hintsAbstractionMap) //autoAbstractionMap=Map()
              }

            TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
              abstractionMap,
              GlobalParameters.get.templateBasedInterpolationTimeout)
          } else {
          DagInterpolator.interpolatingPredicateGenCEXAndOr _
        }

        println(
          "----------------------------------- CEGAR --------------------------------------")

        new HornPredAbs(simpClauses, // loop
          optimizedTemplates.toInitialPredicates, //emptyHints
          interpolator).result
      }

      //println("\nsimpHints Hints:")
      //simpHints.pretyPrintHints()
      println("\nOptimized Hints:")
      println("!@@@@")
      optimizedTemplates.pretyPrintHints()
      println("@@@@!")
      println("timeout:" + GlobalParameters.get.threadTimeout)
      //GlobalParameters.get.printHints=optimizedHints
      (optimizedTemplates, result)
    }
  }



  def transformPredicateMapToVerificationHints(originalPredicates:Map[Predicate, Seq[IFormula]]):  VerificationHints ={
    VerificationHints(originalPredicates.mapValues(_.map(VerificationHints.VerifHintInitPred(_))))
  }

  def initialIDForHints(simpHints: VerificationHints): Seq[wrappedHintWithID] = {
    var counter = 0
    val wrappedHintsList = for ((head,hints) <- simpHints.predicateHints;oneHint <- hints) yield{
      counter = counter + 1
      wrappedHintWithID(counter, head.name, oneHint.toString)
    }
    wrappedHintsList.toSeq
  }


  def writeHornClausesToFile(file: String, simpClauses: Clauses): Unit = {
    val writer = new PrintWriter(new File(file + ".horn"))
    for (clause <- simpClauses) {
      writer.write(clause.toPrologString + "\n")
    }
    writer.close()
  }


  def writeSMTFormatToFile(simpClauses: Clauses, fileName: String): Unit = {
    //val filename = basename + ".smt2"
    println("write " + fileName + " to smt format file")
    //val out = new java.io.FileOutputStream("trainData/"+fileName+".smt2")
    val out = new java.io.FileOutputStream(fileName + ".smt2") //python path
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


  def getArgumentInfo(argumentList: Array[(IExpression.Predicate, Int)]): ArrayBuffer[argumentInfo] = {
    var argID = 0
    var arguments: ArrayBuffer[argumentInfo] = ArrayBuffer[argumentInfo]()
    for ((arg, i) <- argumentList.zipWithIndex) {
      for ((a, j) <- (0 to arg._2 - 1).zipWithIndex) {
        arguments += new argumentInfo(argID, arg._1, a)
        argID = argID + 1
      }
    }
    arguments
  }

  def getArgumentInfoFromFile(argumentList: Array[(IExpression.Predicate, Int)]): ArrayBuffer[argumentInfo] = {
    val arguments = getArgumentInfo(argumentList)
    val argumentFileName = GlobalParameters.get.fileName + ".arguments"
    if (scala.reflect.io.File(argumentFileName).exists) {
      //read score from .argument file
      for (arg <- arguments; line <- Source.fromFile(argumentFileName).getLines) {
        val parsedLine = line.split(":")
        if (arg.head == parsedLine(1) && ("argument" + arg.index.toString) == parsedLine(2))
          arg.score = parsedLine(3).toInt
      }
    }

    arguments
  }

  def getArgumentBoundForSmt(argumentList: Array[(IExpression.Predicate, Int)], disjunctive: Boolean, simplifiedClauses: Seq[Clause], simpHints: VerificationHints
                             , predGenerator:  Dag[DisjInterpolator.AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]]): ArrayBuffer[argumentInfo] = {
    val counterexampleMethod =
      if (disjunctive)
        CEGAR.CounterexampleMethod.AllShortest
      else
        CEGAR.CounterexampleMethod.FirstBestShortest

    val simpPredAbs =
      new simplifiedHornPredAbsForArgumentBounds(simplifiedClauses, //HornPredAbs
        simpHints.toInitialPredicates, predGenerator,
        counterexampleMethod)
    getArgumentBound(argumentList, simpPredAbs.argumentBounds)
  }


  def getArgumentBound(argumentList: Array[(IExpression.Predicate, Int)], argumentBounds: scala.collection.mutable.Map[Predicate, Array[(String, String)]]): ArrayBuffer[argumentInfo] = {
    val arguments = getArgumentInfo(argumentList)
    for ((k, v) <- argumentBounds; arg <- arguments) if (arg.location.toString() == k.toString()) {
      arg.bound = v(arg.index)
    }
    arguments
  }

  def argumentBoundAnalysis(argumentList: Array[(IExpression.Predicate, Int)],simplifiedClausesForGraph:Clauses,
                            predGenerator:  Dag[DisjInterpolator.AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]]): ArrayBuffer[argumentInfo] ={
    val arguments = getArgumentInfo(argumentList)
    val b=new BoundAnalyzer(simplifiedClausesForGraph, predGenerator)
    for (arg<-arguments){
      val lowerB=matchArgumentBound(b.lowerBounds.get(arg.location,arg.index))
      val upperB=matchArgumentBound(b.upperBounds.get(arg.location,arg.index))
      if (GlobalParameters.get.graphPrettyPrint==true)
        println(arg.headName+":"+"argument"+arg.index+":["+lowerB+","+upperB+"]")
      arg.bound=(lowerB,upperB)
    }
    arguments
  }
  def matchArgumentBound[A](bound:Option[A]): String ={
    bound match {
      case Some(x) => "1"
      case None => "0"
    }
  }
  def getArgumentOccurrenceInHints(file: String,
                                   argumentList: Array[(IExpression.Predicate, Int)],
                                   positiveHints: VerificationHints,
                                   countOccurrence: Boolean = true): ArrayBuffer[argumentInfo] ={
    val arguments = getArgumentInfo(argumentList)
    if (countOccurrence == true) {
      //get hint info list
      var positiveHintInfoList: ArrayBuffer[hintInfo] = ArrayBuffer[hintInfo]()
      for ((head, hintList) <- positiveHints.predicateHints) {
        for (h <- hintList) h match {
          case VerifHintInitPred(p) => {
            positiveHintInfoList += new hintInfo(p, "VerifHintInitPred", head)
          }
          case VerifHintTplPred(p, _) => {
            positiveHintInfoList += new hintInfo(p, "VerifHintTplPred", head)
          }
          case VerifHintTplPredPosNeg(p, _) => {
            positiveHintInfoList += new hintInfo(p, "VerifHintTplPredPosNeg", head)
          }
          case VerifHintTplEqTerm(t, _) => {
            positiveHintInfoList += new hintInfo(t, "VerifHintTplEqTerm", head)
          }
          case VerifHintTplInEqTerm(t, _) => {
            positiveHintInfoList += new hintInfo(t, "VerifHintTplInEqTerm", head)
          }
          case VerifHintTplInEqTermPosNeg(t, _) => {
            positiveHintInfoList += new hintInfo(t, "VerifHintTplInEqTermPosNeg", head)
          }
          case _ => {}
        }
      }
      //go through all predicates and arguments count occurrence
      for (arg <- arguments) {
        for (hint <- positiveHintInfoList) {
          if (arg.location.equals(hint.head) && ContainsSymbol(hint.expression, IVariable(arg.index))) {
            arg.score = arg.score + 1
            arg.binaryOccurenceLabel = 1
          }
        }
      }

    }
    //normalize score
    //    val argumentIDList=for(arg<-arguments) yield arg.ID
    //    val argumentNameList=for(arg<-arguments) yield arg.location.toString()+":"+"argument"+arg.index
    //    val argumentOccurrence=for(arg<-arguments) yield arg.score
    (arguments)

  }
  def writeArgumentOccurrenceInHintsToFile(file: String,
                               argumentList: Array[(IExpression.Predicate, Int)],
                               positiveHints: VerificationHints,
                               countOccurrence: Boolean = true,writeToFile:Boolean=false): ArrayBuffer[argumentInfo]  = {
    val arguments = getArgumentOccurrenceInHints(file,argumentList,positiveHints,countOccurrence)
    if (writeToFile==true){
      println("Write arguments to file")
      val writer = new PrintWriter(new File(file + ".arguments")) //python path
      for (arg <- arguments) {
        writer.write(arg.ID + ":" + arg.location.toString() + ":" + "argument" + arg.index + ":" + arg.score + "\n")
      }
      writer.close()
    }
    arguments
  }
  def getArgumentLabel(simplifiedClausesForGraph:Clauses,simpHints: VerificationHints
                       , predGenerator:  Dag[DisjInterpolator.AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]],
                       disjunctive: Boolean,argumentOccurrence:Boolean,argumentBound:Boolean):  ArrayBuffer[argumentInfo] ={
    val argumentList = (for (p <- HornClauses.allPredicates(simplifiedClausesForGraph)) yield (p, p.arity)).toArray.sortBy(_._1.name)
    //for (a<-argumentList) println(a)
    val argumentInfo = if (argumentOccurrence==true && argumentBound==true){
      val argumentOccurrenceInfo = HintsSelection.writeArgumentOccurrenceInHintsToFile(GlobalParameters.get.fileName, argumentList, simpHints, countOccurrence = false)
      val argumentBoundInfo = GlobalParameters.get.boundsAnalysis match {
        case true=>argumentBoundAnalysis(argumentList,simplifiedClausesForGraph,predGenerator)
        case false=>getArgumentBoundForSmt(argumentList,disjunctive,simplifiedClausesForGraph,simpHints,predGenerator)
      }
      for (a<-(argumentOccurrenceInfo zip argumentBoundInfo)) yield {
        a._1.bound=a._2.bound
        a._1}
    }else if (argumentOccurrence==true){
      HintsSelection.writeArgumentOccurrenceInHintsToFile(GlobalParameters.get.fileName, argumentList, simpHints, countOccurrence = false)
    }else if (argumentBound==true){
      GlobalParameters.get.boundsAnalysis match {
        case true=>argumentBoundAnalysis(argumentList,simplifiedClausesForGraph,predGenerator)
        case false=>getArgumentBoundForSmt(argumentList,disjunctive,simplifiedClausesForGraph,simpHints,predGenerator)
      }
    } else{
      getArgumentInfo(argumentList)
    }
    argumentInfo
  }

}


class VerificationHintsInfo(val initialHints: VerificationHints, val positiveHints: VerificationHints,
                            val negativeHints: VerificationHints,val predictedHints:VerificationHints=VerificationHints(Map()))

class ClauseInfo(val simplifiedClause: Clauses, val clausesInCounterExample: Clauses)

class hintInfo(e: IExpression, t: String, h: IExpression.Predicate) {
  val head = h
  val expression = e
  val hintType = t
}

class argumentInfo(id: Int, loc: IExpression.Predicate, ind: Int) {
  val ID = id
  val location = loc
  val index = ind
  var score = 0
  val head = location.toString()
  val headName = location.name
  var bound: Pair[String, String] = ("\"None\"", "\"None\"")
  var binaryOccurenceLabel = 0
}

class simplifiedHornPredAbsForArgumentBounds[CC <% HornClauses.ConstraintClause](iClauses: Iterable[CC],
                                                                                 initialPredicates: Map[Predicate, Seq[IFormula]],
                                                                                 predicateGenerator:  Dag[DisjInterpolator.AndOrNode[NormClause, Unit]] =>
                                                                                   Either[Seq[(Predicate, Seq[Conjunction])],
                                                                                     Dag[(IAtom, NormClause)]], counterexampleMethod: CEGAR.CounterexampleMethod.Value = CEGAR.CounterexampleMethod.FirstBestShortest) {
  val theories = {
    val coll = new TheoryCollector
    coll addTheory TypeTheory
    for (c <- iClauses)
      c collectTheories coll
    coll.theories
  }
  implicit val sf = new SymbolFactory(theories)
  val relationSymbols =
    (for (c <- iClauses.iterator;
          lit <- (Iterator single c.head) ++ c.body.iterator;
          p = lit.predicate)
      yield (p -> RelationSymbol(p))).toMap

  // make sure that arguments constants have been instantiated
  for (c <- iClauses) {
    val preds = for (lit <- c.head :: c.body.toList) yield lit.predicate
    for (p <- preds.distinct) {
      val rs = relationSymbols(p)
      for (i <- 0 until (preds count (_ == p)))
        rs arguments i
    }
  }
  // translate clauses to internal form
  val (normClauses, relationSymbolBounds) = {
    val rawNormClauses = new LinkedHashMap[NormClause, CC]

    for (c <- iClauses) {
      lazabs.GlobalParameters.get.timeoutChecker()
      rawNormClauses.put(NormClause(c, (p) => relationSymbols(p)), c)
    }

    if (lazabs.GlobalParameters.get.intervals) {
      val res = new LinkedHashMap[NormClause, CC]

      val propagator =
        new IntervalPropagator(rawNormClauses.keys.toIndexedSeq,
          sf.reducerSettings)

      for ((nc, oc) <- propagator.result)
        res.put(nc, rawNormClauses(oc))
      (res.toSeq, propagator.rsBounds)
    } else {
      val emptyBounds =
        (for (rs <- relationSymbols.valuesIterator)
          yield (rs -> Conjunction.TRUE)).toMap
      (rawNormClauses.toSeq, emptyBounds)
    }
  }
  // print argument bounds
  var argumentBounds: scala.collection.mutable.Map[Predicate, Array[Tuple2[String, String]]] = scala.collection.mutable.Map()
  for ((rs, bounds) <- relationSymbolBounds; if (rs.pred.name != "FALSE")) { //don't learn from FALSE predicate
    //println(rs.pred.name + ":")
    var argumentBoundList: Array[Tuple2[String, String]] = Array()
    if (bounds.isTrue) { //FALSE's bounds is true
      for (s <- rs.arguments(0))
        argumentBoundList :+= Tuple2("\"None\"", "\"None\"")
    } else if (bounds.isFalse) {
      for (s <- rs.arguments(0))
        argumentBoundList :+= Tuple2("\"False\"", "\"False\"")
    } else {
      for (s <- rs.arguments(0)) {
        //print("  " + s + ": ")
        val lc = ap.terfor.linearcombination.LinearCombination(s, bounds.order)
        val lowerBound = PresburgerTools.lowerBound(lc, bounds) match {
          case Some(x) => x.toString()
          case _ => "\"None\""
        }
        //print(", ")
        val upperBound = (for (b <- PresburgerTools.lowerBound(-lc, bounds)) yield -b) match {
          case Some(x) => x.toString()
          case _ => "\"None\""
        }
        argumentBoundList :+= Tuple2(lowerBound, upperBound)
        //println()
      }
    }
    argumentBounds(rs.pred) = argumentBoundList
  }
}