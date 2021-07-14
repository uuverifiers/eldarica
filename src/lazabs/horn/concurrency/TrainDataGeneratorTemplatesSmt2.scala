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
import lazabs.ast.ASTree._
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, VerifHintInitPred, VerifHintTplEqTerm, VerifHintTplInEqTerm, VerifHintTplInEqTermPosNeg, VerifHintTplPred, VerifHintTplPredPosNeg}
import lazabs.horn.abstractions.{AbsLattice, AbsReader, EmptyVerificationHints, VerificationHints, _}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.PredicateMiner.TemplateExtraction
import lazabs.horn.bottomup.{HornTranslator, _}
import lazabs.horn.concurrency.HintsSelection.{generateCombinationTemplates, getClausesInCounterExamples, getInitialPredicates, getPredGenerator, isArgBoolean, mergeTemplates, resetElementCost, setAllCost, transformPredicateMapToVerificationHints}
import lazabs.horn.global._
import lazabs.horn.preprocessor.{DefaultPreprocessor, HornPreprocessor}

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

      //////////////////////////////////////////////////////////////////////////////

      val (simplifiedClauses, simpHints, preprocBackTranslator) =
        Console.withErr(outStream) {
          val (simplifiedClauses, simpHints, backTranslator) =
            if (lbe) {
              (unsimplifiedClauses, hints, HornPreprocessor.IDENTITY_TRANSLATOR)
            } else {
              val preprocessor = new DefaultPreprocessor
              preprocessor.process(unsimplifiedClauses, hints)
            }

          if (GlobalParameters.get.printHornSimplified) {
            //      println("-------------------------------")
            //      printClauses(simplifiedClauses)
            //      println("-------------------------------")

            println("Clauses after preprocessing:")
            for (c <- simplifiedClauses)
              println(c.toPrologString)

            //val aux = simplifiedClauses map (horn2Eldarica(_))
            //      val aux = horn2Eldarica(simplifiedClauses)
            //      println(lazabs.viewer.HornPrinter(aux))
            //      simplifiedClauses = aux map (transform(_))
            //      println("-------------------------------")
            //      printClauses(simplifiedClauses)
            //      println("-------------------------------")
          }

          (simplifiedClauses, simpHints, backTranslator)
        }
      GlobalParameters.get.timeoutChecker()
      val params =
        if (lazabs.GlobalParameters.get.templateBasedInterpolationPortfolio)
          lazabs.GlobalParameters.get.withAndWOTemplates
        else
          List()
      /////////////////////////////////////////////////////////////////////////////


      val abstractionType =
        lazabs.GlobalParameters.get.templateBasedInterpolationType

      lazy val absBuilder =
        new StaticAbstractionBuilder(simplifiedClauses, abstractionType)

      lazy val autoAbstraction: AbstractionMap =
        absBuilder.abstractionRecords

      val fileName=HintsSelection.getFileName()
      simplifiedClauses.map(_.toPrologString).foreach(println)
      val loopDetector = new LoopDetector(simplifiedClauses)
      if(loopDetector.loopHeads.isEmpty){
        HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/no-predicates-selected/"+fileName,"loopHeads is empty")
        sys.exit()
      }
      println("loop heads",loopDetector.loopHeads)
      println("abs1:termAbstractions")
      absBuilder.termAbstractions.pretyPrintHints()
      println("abs2:octagonAbstractions")
      absBuilder.octagonAbstractions.pretyPrintHints()
      println("abs3:relationAbstractions")
      absBuilder.relationAbstractions(false).pretyPrintHints()
//      println("abs4:relationAbstractions")
//      absBuilder.relationAbstractions(true).pretyPrintHints()
      println("mergedAutoAbstractions")
      val mergedHeuristic=mergeTemplates(VerificationHints.union(Seq(absBuilder.termAbstractions,absBuilder.octagonAbstractions,
        absBuilder.relationAbstractions(false))))//absBuilder.relationAbstractions(true)
      mergedHeuristic.pretyPrintHints()
      println("generatedCombinationTemplates")
      //set all cost to 0
      val combinationTemplates=generateCombinationTemplates(simplifiedClauses)
      combinationTemplates.pretyPrintHints()

      println("initialTemplates")
      val initialTemplates=setAllCost(mergedHeuristic)
      initialTemplates.pretyPrintHints()

      val initialTemplatesAbstraction=absBuilder.loopDetector.hints2AbstractionRecord(initialTemplates)

      /** Manually provided interpolation abstraction hints */
      lazy val hintsAbstraction: AbstractionMap =
        if (simpHints.isEmpty)
          Map()
        else
          absBuilder.loopDetector hints2AbstractionRecord simpHints


      //////////////////////////////////////////////////////////////////////////////

      val predGenerator =getPredGenerator(Seq(hintsAbstraction,autoAbstraction,
        initialTemplatesAbstraction),outStream)

      if (GlobalParameters.get.templateBasedInterpolationPrint &&
        !simpHints.isEmpty)
        ReaderMain.printHints(simpHints, name = "Manual verification hints:")

      //////////////////////////////////////////////////////////////////////////////


      val counterexampleMethod =HintsSelection.getCounterexampleMethod(disjunctive)
      GlobalParameters.get.timeoutChecker()

      //simplify clauses. get rid of some redundancy
      val spAPI = ap.SimpleAPI.spawn
      val sp=new Simplifier
      val simplifiedClausesForGraph=HintsSelection.simplifyClausesForGraphs(simplifiedClauses,simpHints)//hints
      val initialPredicatesForCEGAR =getInitialPredicates(simplifiedClausesForGraph,simpHints)
      val predAbs=Console.withOut(outStream) {
        val predAbs =
          new HornPredAbs(simplifiedClausesForGraph,
            initialPredicatesForCEGAR.toInitialPredicates, predGenerator,
            counterexampleMethod)
        predAbs
      }


      def labelTemplates(unlabeledPredicates:VerificationHints): VerificationHints ={
        val predMiner=Console.withOut(outStream){new PredicateMiner(predAbs)}
        //val predMiner=new PredicateMiner(predAbs)
        val positiveTemplates=predMiner.unitTwoVariableTemplates//predMiner.variableTemplates
        println("positiveTemplates")
        positiveTemplates.pretyPrintHints()
        positiveTemplates
//
//        val filteredPositiveTemplates=VerificationHints(for (p1<-predMiner.variableTemplates.predicateHints) yield{
//          var elms:Seq[VerifHintElement]=Seq()
//          for (p<-p1._2)  {
//            p match {
//              case VerifHintTplEqTerm(t,c)=>{if(!isArgBoolean(t)) elms=elms :+ p}
//              case VerifHintTplInEqTerm(t,c)=>{if(!isArgBoolean(t)) elms=elms :+ p}
//            }
//          }
//          p1._1-> elms
//        })
//        println("filteredPositiveTemplates")
//        filteredPositiveTemplates.pretyPrintHints()
//        filteredPositiveTemplates

      }

      val unlabeledTemplates=combinationTemplates
      val labeledTemplates=labelTemplates(unlabeledTemplates)
      //val labeledTemplates=randomLabelTemplates(unlabeledTemplates,0.5)
      println("-"*10+"unlabeledTemplates"+"-"*10)
      unlabeledTemplates.pretyPrintHints()
      println("-"*10+"labeledTemplates"+"-"*10)
      labeledTemplates.pretyPrintHints()

      if(labeledTemplates.totalPredicateNumber==0){
        HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/no-predicates-selected/"+fileName,"labeledPredicates is empty")
        sys.exit()
      }


      //Output graphs
      val clauseCollection = new ClauseInfo(simplifiedClausesForGraph,Seq())
      val argumentList = (for (p <- HornClauses.allPredicates(simplifiedClausesForGraph)) yield (p, p.arity)).toArray.sortBy(_._1.name)
      val argumentInfo = HintsSelection.writeArgumentOccurrenceInHintsToFile(GlobalParameters.get.fileName, argumentList, labeledTemplates,countOccurrence=true)
      if (GlobalParameters.get.separateByPredicates==true){
        GraphTranslator.separateGraphByPredicates(unlabeledTemplates,labeledTemplates,clauseCollection,argumentInfo)
      }else{
        val hintsCollection=new VerificationHintsInfo(unlabeledTemplates,labeledTemplates,VerificationHints(Map()))//labeledPredicates
        GraphTranslator.drawAllHornGraph(clauseCollection,hintsCollection,argumentInfo)
      }
      HintsSelection.writePredicatesToFiles(unlabeledTemplates,labeledTemplates)

    }
  }
}



