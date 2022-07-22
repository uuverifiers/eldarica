/**
 * Copyright (c) 2011-2020 Philipp Ruemmer, Chencheng Liang All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
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

import ap.parser._
import lazabs.GlobalParameters
import lazabs.Main.PrintingFinishedException
import lazabs.ast.ASTree._
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, VerifHintInitPred, VerifHintTplEqTerm, VerifHintTplInEqTerm, VerifHintTplInEqTermPosNeg, VerifHintTplPred, VerifHintTplPredPosNeg}
import lazabs.horn.abstractions.{AbsLattice, AbsReader, EmptyVerificationHints, VerificationHints, _}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.PredicateMiner.TemplateExtraction
import lazabs.horn.bottomup.{HornTranslator, _}
import lazabs.horn.concurrency.HintsSelection.{containsPred, generateCombinationTemplates, getClausesInCounterExamples, getInitialPredicates, getParametersFromVerifHintElement, getPredGenerator, isArgBoolean, isAtomaticTerm, mergeTemplates, resetElementCost, setAllCost, termContains, transformPredicateMapToVerificationHints, writeTemplateDistributionToFiles}
import lazabs.horn.global._
import lazabs.horn.preprocessor.HornPreprocessor.BackTranslator
import lazabs.horn.preprocessor.{DefaultPreprocessor, HornPreprocessor}
import lazabs.horn.concurrency.TemplateSelectionUtils.outputPrologFile

import java.nio.file.{Files, Paths, StandardCopyOption}
import scala.util.Random

object TrainDataGeneratorTemplatesSmt2 {
  def apply(clauseSet: Seq[HornClause],
            uppaalAbsMap: Option[Map[String, AbsLattice]],
            global: Boolean,
            disjunctive: Boolean,
            drawRTree: Boolean,
            lbe: Boolean) = {


    val log = lazabs.GlobalParameters.get.log

    /*    if(clauseSet.size == 0) {
          println("No Horn clause")
          sys.exit(0)
        }       */

    val arities = clauseSet.map(cl => Horn.getRelVarArities(cl)).reduceLeft(_ ++ _)
    val timeStart = System.currentTimeMillis

    def printTime =
      if (lazabs.GlobalParameters.get.logStat)
        Console.err.println(
          "Total elapsed time (ms): " + (System.currentTimeMillis - timeStart))

    if (global) {
      val cegar = new HornCegar(clauseSet, log)
      val arg = cegar.apply

      printTime

      if (log && cegar.status == Status.SAFE) {
        for ((i, sol) <- arg.reportSolution) {
          val cl = HornClause(
            RelVar(i, (0 until arities(i)).map(p => Parameter("_" + p, lazabs.types.IntegerType())).toList),
            List(Interp(sol))
          )
          println(lazabs.viewer.HornPrinter.print(cl))
        }
      }
      if (drawRTree) lazabs.viewer.DrawGraph(arg)
    }
    else {
      //////////////////////////////////////////////////////////////////////////////////
      //horn wrapper   inputs
      // (new HornWrapper(clauseSet, uppaalAbsMap, lbe, disjunctive)).result

      //    class HornWrapper(constraints: Seq[HornClause],
      //                      uppaalAbsMap: Option[Map[String, AbsLattice]],
      //                      lbe: Boolean,
      //                      disjunctive : Boolean) {

      val constraints: Seq[HornClause] = clauseSet

      def printClauses(cs: Seq[Clause]) = {
        for (c <- cs) {
          println(c);
        }
      }

      val translator = new HornTranslator
      import translator._

      //////////////////////////////////////////////////////////////////////////////

      GlobalParameters.get.setupApUtilDebug

      val outStream =
        if (GlobalParameters.get.logStat)
          Console.err
        else
          HornWrapper.NullStream

      val originalClauses = constraints //=constraints
      val unsimplifiedClauses = originalClauses map (transform(_))

      //    if (GlobalParameters.get.printHornSimplified)
      //      printMonolithic(unsimplifiedClauses)

      val name2Pred =
        (for (Clause(head, body, _) <- unsimplifiedClauses.iterator;
              IAtom(p, _) <- (head :: body).iterator)
          yield (p.name -> p)).toMap

      //////////////////////////////////////////////////////////////////////////////
      val hints: VerificationHints =
        GlobalParameters.get.cegarHintsFile match {
          case "" =>
            EmptyVerificationHints
          case hintsFile => {
            val reader = new AbsReader(
              new java.io.BufferedReader(
                new java.io.FileReader(hintsFile)))
            val hints =
              (for ((predName, hints) <- reader.allHints.iterator;
                    pred = name2Pred get predName;
                    if {
                      if (pred.isDefined) {
                        if (pred.get.arity != reader.predArities(predName))
                          throw new Exception(
                            "Hints contain predicate with wrong arity: " +
                              predName + " (should be " + pred.get.arity + " but is " +
                              reader.predArities(predName) + ")")
                      } else {
                        Console.err.println("   Ignoring hints for " + predName + "\n")
                      }
                      pred.isDefined
                    }) yield {
                (pred.get, hints)
              }).toMap
            VerificationHints(hints)
          }
        }

      //////////////////////////////////////////////////////////////
      def preprocessClauses(clauses : Seq[Clause],
                            hints   : VerificationHints)
      :(Seq[Clause],
        VerificationHints,
        BackTranslator) = {
        //TemplateSelectionUtils.outputPrologFile(unsimplifiedClauses,"unsimplified")
        val (simplifiedClauses, simpPreHints, backTranslator) =
          Console.withErr(outStream) {
            if (lbe) {
              (unsimplifiedClauses, hints, HornPreprocessor.IDENTITY_TRANSLATOR)
            } else {
              val preprocessor = new DefaultPreprocessor
              preprocessor.process(unsimplifiedClauses, hints)
            }
          }
        //TemplateSelectionUtils.outputPrologFile(simplifiedClauses,"simplified")

        if (GlobalParameters.get.printHornSimplified) {
          //      println("-------------------------------")
          //      printClauses(simplifiedClauses)
          //      println("-------------------------------")

          println("Clauses after preprocessing:")
          for (c <- simplifiedClauses)
            println(c.toPrologString)
          throw PrintingFinishedException

          //val aux = simplifiedClauses map (horn2Eldarica(_))
          //      val aux = horn2Eldarica(simplifiedClauses)
          //      println(lazabs.viewer.HornPrinter(aux))
          //      simplifiedClauses = aux map (transform(_))
          //      println("-------------------------------")
          //      printClauses(simplifiedClauses)
          //      println("-------------------------------")

        }

        if (GlobalParameters.get.printHornSimplifiedSMT) {
          val predsToDeclare = (for (c <- simplifiedClauses
                                     if c.head.pred != HornClauses.FALSE) yield {
            c.predicates
          }).flatten.toSet.toList

          SMTLineariser("", "HORN", "", Nil, predsToDeclare,
            simplifiedClauses.map(_ toFormula))
          throw PrintingFinishedException
        }
        (simplifiedClauses, simpPreHints, backTranslator)
      }
      //////////////////////////////////////////////////////////////////////////////
      val (simplifiedClauses, simpHints, preprocBackTranslator) =preprocessClauses(unsimplifiedClauses,hints)
      GlobalParameters.get.timeoutChecker()

      /////////////////////////////////////////////////////////////////////////////

      //simplify clauses. get rid of some redundancy
      //      val spAPI = ap.SimpleAPI.spawn
      //      val sp=new Simplifier
      val simplifiedClausesForGraph=HintsSelection.normalizedClausesForGraphs(simplifiedClauses,VerificationHints(Map()))

      if (simplifiedClausesForGraph.isEmpty) {
        HintsSelection.moveRenameFile(GlobalParameters.get.fileName, "../benchmarks/exceptions/no-simplified-clauses/" + HintsSelection.getFileName(), message = "no simplified clauses")
        sys.exit()
      }

      if (GlobalParameters.get.generateTemplates){
        val unlabeledPredicateFileName=".unlabeledPredicates"
        val generatedTpl = generateCombinationTemplates(simplifiedClausesForGraph, onlyLoopHead = true) //false
        Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName + unlabeledPredicateFileName + ".tpl")) {AbsReader.printHints(generatedTpl)}
        sys.exit()
      }
      //HintsSelection.checkMaxNode(simplifiedClausesForGraph)
      /////////////////////////////////////////////////////////////////////////////
      lazy val absBuilder =
        new StaticAbstractionBuilder(simplifiedClausesForGraph, lazabs.GlobalParameters.get.templateBasedInterpolationType)
      lazy val autoAbstraction: AbstractionMap =
        absBuilder.abstractionRecords
      /** Manually provided interpolation abstraction hints */
      lazy val hintsAbstraction: AbstractionMap =
        if (simpHints.isEmpty)
          Map()
        else
          absBuilder.loopDetector hints2AbstractionRecord simpHints
      if (GlobalParameters.get.templateBasedInterpolationPrint &&
        !simpHints.isEmpty)
        ReaderMain.printHints(simpHints, name = "Manual verification hints:")


      val predGenerator =getPredGenerator(Seq(hintsAbstraction,autoAbstraction),outStream)

      //////////////////////////////////////////////////////////////////////////////


      val counterexampleMethod =HintsSelection.getCounterexampleMethod(disjunctive)
      GlobalParameters.get.timeoutChecker()

      val initialPredicatesForCEGAR =getInitialPredicates(simplifiedClausesForGraph,simpHints) //empty

      if (GlobalParameters.get.debugLog){
        simplifiedClausesForGraph.map(_.toPrologString).foreach(println)
        println("Solving by CEGAR...")
      }
      val predAbs=Console.withOut(outStream) {
        val predAbs =
          new HornPredAbs(simplifiedClausesForGraph,
            initialPredicatesForCEGAR.toInitialPredicates, predGenerator,
            counterexampleMethod)
        predAbs
      }
      def labelTemplates(unlabeledTemplates:VerificationHints): (VerificationHints,VerificationHints) ={
        if (GlobalParameters.get.debugLog){println("Mining the templates...")}
        val predMiner=Console.withOut(outStream){new PredicateMiner(predAbs)}
        //val predMiner=new PredicateMiner(predAbs)
        val positiveTemplates=predMiner.unitTwoVariableTemplates//predMiner.variableTemplates
        val costThreshold=99
        val filteredPositiveTemplates= VerificationHints((for((k,ps)<-positiveTemplates.predicateHints) yield {
          k->ps.filter(getParametersFromVerifHintElement(_)._2<costThreshold)
        }).filterNot(_._2.isEmpty))
        if (GlobalParameters.get.debugLog){
          println("predicates from " +lazabs.GlobalParameters.get.templateBasedInterpolationType.toString)
          absBuilder.abstractionHints.pretyPrintHints()
          println("mined predicates (unitTwoVariableTemplates)")
          positiveTemplates.pretyPrintHints()
          println("filtered mined predicates")
          filteredPositiveTemplates.pretyPrintHints()
        }
        if(filteredPositiveTemplates.isEmpty){
          HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/empty-mined-label/"+HintsSelection.getFileName(),"empty-mined-label")
          sys.exit()
        }
        val labeledTemplates=VerificationHints(for ((kp,vp)<-unlabeledTemplates.predicateHints;
                                                    (kf,vf)<-filteredPositiveTemplates.predicateHints;
                                                    if kp.name==kf.name) yield
          kp -> (for (p<-vp;if termContains(vf.map(getParametersFromVerifHintElement(_)),getParametersFromVerifHintElement(p))._1) yield p)
        )
        if (GlobalParameters.get.debugLog){
          println("-"*10+"unlabeledTemplates"+"-"*10)
          unlabeledTemplates.pretyPrintHints()
          println("-"*10+"labeledTemplates"+"-"*10)
          labeledTemplates.pretyPrintHints()
        }
        (positiveTemplates,labeledTemplates)
        //filteredPositiveTemplates
      }

      val combinationTemplates=generateCombinationTemplates(simplifiedClausesForGraph,onlyLoopHead = true)//false
      //todo: for debug: reconstruct labels
      //val unlabeledTemplates=VerificationHints(combinationTemplates.predicateHints.mapValues(x=>x.slice(2,3)++x.slice(8,9)))//2-8,3-10
      //val unlabeledTemplates=VerificationHints(combinationTemplates.predicateHints.mapValues(x=>x.slice(5,13)++x.slice(5,13)++x.slice(18,39)))
      //val unlabeledTemplates=VerificationHints(combinationTemplates.predicateHints.mapValues(x=>x.slice(5,6)++x.slice(7,8)++x.slice(9,10)++x.slice(11,12)++x.slice(23,24)++x.slice(27,28)++x.slice(31,32)++x.slice(35,36)))
      //val unlabeledTemplates=VerificationHints(combinationTemplates.predicateHints.mapValues(x=>x.slice(0,23)++x.slice(23,24)++x.slice(27,28)++x.slice(31,32)++x.slice(35,36)))
//      val unlabeledTemplates=VerificationHints(
//        Map(combinationTemplates.predicateHints.toSeq.head._1->combinationTemplates.predicateHints.toSeq.head._2.slice(5,10)) ++
//          Map(combinationTemplates.predicateHints.toSeq.tail.head._1->combinationTemplates.predicateHints.toSeq.tail.head._2.slice(5,10)))

      val unlabeledTemplates=combinationTemplates

      val (positiveTemplates,labeledTemplates)=labelTemplates(unlabeledTemplates)
      //val labeledTemplates=randomLabelTemplates(unlabeledTemplates,0.5)


      if(labeledTemplates.totalPredicateNumber==0){
        HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/no-predicates-selected/"+HintsSelection.getFileName(),"labeledPredicates is empty")
        sys.exit()
      }

      //HintsSelection.writePredicatesToFiles(unlabeledTemplates,labeledTemplates,positiveTemplates)
      HintsSelection.writeTemplatesToFile(unlabeledTemplates,"unlabeledPredicates")
      HintsSelection.writeTemplatesToFile(labeledTemplates,"labeledPredicates")
      HintsSelection.writeTemplatesToFile(positiveTemplates,"minedPredicates")
      //writeTemplateDistributionToFiles(simplifiedClausesForGraph,unlabeledTemplates,positiveTemplates)

//      if (GlobalParameters.get.getSMT2 == true) {
//        //HintsSelection.writeSMTFormatToFile(for (c <- simplifiedClauses) yield DrawHyperEdgeHornGraph.replaceIntersectArgumentInBody(c), GlobalParameters.get.fileName + "-simplified")
//        HintsSelection.writeSMTFormatToFile(simplifiedClauses, GlobalParameters.get.fileName + "-simplified")
//        val normalizedClauses=HintsSelection.normalizedClausesForGraphs(simplifiedClauses, simpHints)
//        HintsSelection.writeSMTFormatToFile(simplifiedClauses, GlobalParameters.get.fileName + "-normalized")
//        outputPrologFile(normalizedClauses)
//      }

//      //Output graphs
//      if(GlobalParameters.get.getHornGraph){
//        val clauseCollection = new ClauseInfo(simplifiedClausesForGraph,Seq())
//        val argumentInfo = HintsSelection.getArgumentLabel(simplifiedClausesForGraph,simpHints,predGenerator,disjunctive,
//          argumentOccurrence = GlobalParameters.get.argumentOccurenceLabel,argumentBound =GlobalParameters.get.argumentBoundLabel)
//        if (GlobalParameters.get.separateByPredicates==true){
//          GraphTranslator.separateGraphByPredicates(unlabeledTemplates,labeledTemplates,clauseCollection,argumentInfo)
//        }else{
//          val hintsCollection=new VerificationHintsInfo(unlabeledTemplates,labeledTemplates,VerificationHints(Map()))//labeledPredicates
//          GraphTranslator.drawAllHornGraph(clauseCollection,hintsCollection,argumentInfo)
//        }
//      }



      //todo: draw separate labels
//      var templateCounter=0
//      for((k,v)<-unlabeledTemplates.predicateHints){
//        for (vv<-v){
//          val fName=GlobalParameters.get.fileName.dropRight(".smt2".length) +"-"+ templateCounter.toString+".smt2"
//          val oneTemplate=VerificationHints(Map(k->Seq(vv)))
//          val hintsCollection=new VerificationHintsInfo(oneTemplate,labeledTemplates,VerificationHints(Map()))//labeledPredicates
//          GraphTranslator.drawAllHornGraph(clauseCollection,hintsCollection,argumentInfo,file = fName)
//          HintsSelection.writePredicatesToFiles(oneTemplate,labeledTemplates,fileName=fName)
//          val path = Files.copy(
//            Paths.get(GlobalParameters.get.fileName),
//            Paths.get(GlobalParameters.get.fileName.substring(0,GlobalParameters.get.fileName.lastIndexOf("/")+1)+fName),
//            StandardCopyOption.REPLACE_EXISTING
//          )
//          templateCounter=templateCounter+1
//        }
//      }

    }
  }
}



