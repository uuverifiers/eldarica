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

package lazabs.horn
import ap.parser._
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.util.Timeout
import lazabs.GlobalParameters
import lazabs.ast.ASTree._
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.{AbsLattice, AbsReader, EmptyVerificationHints, VerificationHints, _}
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.HornClauses.{Clause, _}
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{HornTranslator, _}
import lazabs.horn.concurrency.HintsSelection.getClausesInCounterExamples
import lazabs.horn.concurrency._
import lazabs.horn.global._
import lazabs.horn.preprocessor.{ConstraintSimplifier, DefaultPreprocessor, HornPreprocessor}

import java.io.{File, PrintWriter}
import java.lang.System.currentTimeMillis
import scala.collection.mutable.{HashSet => MHashSet}

object TrainDataGeneratorPredicatesSmt2 {
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
      //InnerHornWrapper

      //      val result : Either[Map[Predicate, IFormula], Dag[IAtom]] =
      //        ParallelComputation(params) {
      //          new InnerWrapperPredicateSelection(unsimplifiedClauses, simplifiedClauses,
      //            simpHints, preprocBackTranslator,
      //            disjunctive, outStream).result
      //        }

      val abstractionType =
        lazabs.GlobalParameters.get.templateBasedInterpolationType

      lazy val absBuilder =
        new StaticAbstractionBuilder(simplifiedClauses, abstractionType)

      lazy val autoAbstraction: AbstractionMap =
        absBuilder.abstractionRecords

      /** Manually provided interpolation abstraction hints */
      lazy val hintsAbstraction: AbstractionMap =
        if (simpHints.isEmpty)
          Map()
        else
          absBuilder.loopDetector hints2AbstractionRecord simpHints

      //////////////////////////////////////////////////////////////////////////////

      val predGenerator =
        Console.withErr(outStream) {
          if (lazabs.GlobalParameters.get.templateBasedInterpolation) {
            val fullAbstractionMap =
              AbstractionRecord.mergeMaps(hintsAbstraction, autoAbstraction)
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

      if (GlobalParameters.get.templateBasedInterpolationPrint &&
        !simpHints.isEmpty)
        ReaderMain.printHints(simpHints, name = "Manual verification hints:")

      //////////////////////////////////////////////////////////////////////////////


      val counterexampleMethod =HintsSelection.getCounterexampleMethod(disjunctive)

      GlobalParameters.get.timeoutChecker()

      val fileName=HintsSelection.getFileName()
      //simplify clauses. get rid of some redundancy
      val spAPI = ap.SimpleAPI.spawn
      val sp=new Simplifier
      val simplePredicatesGeneratorClauses=HintsSelection.simplifyClausesForGraphs(simplifiedClauses,simpHints)//hints

      //read hint from file
      if (GlobalParameters.get.readHints==true){
        val hintType="unlabeledPredicates"
        println("-"*10 + "read predicate from ."+hintType+".tpl" + "-"*10)
        val initialPredicates =VerificationHints(HintsSelection.wrappedReadHints(simplePredicatesGeneratorClauses,hintType).toInitialPredicates.mapValues(_.map(sp(_)).map(VerificationHints.VerifHintInitPred(_))))//simplify after read
        val initialHintsCollection=new VerificationHintsInfo(initialPredicates,VerificationHints(Map()),VerificationHints(Map()))
        //read predicted hints from JSON
        val predictedPositiveHints= HintsSelection.readPredictedHints(simplePredicatesGeneratorClauses,initialPredicates)
        Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".predictedHints.tpl")) {
          AbsReader.printHints(predictedPositiveHints)}
        val truePositiveHints = if (new java.io.File(GlobalParameters.get.fileName + "." + "labeledPredicates" + ".tpl").exists == true)
          VerificationHints(HintsSelection.wrappedReadHints(simplePredicatesGeneratorClauses, "labeledPredicates").toInitialPredicates.mapValues(_.map(sp(_)).map(VerificationHints.VerifHintInitPred(_))))
        else HintsSelection.readPredicateLabelFromJSON(initialHintsCollection, "templateRelevanceLabel")
        val hintsCollection=new VerificationHintsInfo(initialPredicates,truePositiveHints,initialPredicates.filterPredicates(truePositiveHints.predicateHints.keySet))
        val clauseCollection = new ClauseInfo(simplePredicatesGeneratorClauses,Seq())

        if(GlobalParameters.get.measurePredictedPredicates){
          HintsSelection.measurePredicates(simplePredicatesGeneratorClauses,predGenerator,counterexampleMethod,
            predictedPositiveHints.toInitialPredicates,initialPredicates.toInitialPredicates,truePositiveHints.toInitialPredicates)

        } else{
          //Output graphs
          val argumentList = (for (p <- HornClauses.allPredicates(simplePredicatesGeneratorClauses)) yield (p, p.arity)).toArray
          val argumentInfo = HintsSelection.writeArgumentOccurrenceInHintsToFile(GlobalParameters.get.fileName, argumentList, truePositiveHints,countOccurrence=true)
          GraphTranslator.drawAllHornGraph(clauseCollection,hintsCollection,argumentInfo)
        }

        sys.exit()
      }



      /////////////////////////predicates extracting begin///////////////////////////////
      val timeConsumptionBeforePredicateExtractingProcess=(System.currentTimeMillis-timeStart)/1000
      var generatingInitialPredicatesTime:Long=0
      var drawingGraphAndFormLabelsTime:Long=0
      var predicatesExtractingTime:Long=0
      val predicatesExtractingBeginTime=System.currentTimeMillis

      val exceptionalPredGen=HintsSelection.getExceptionalPredicatedGenerator()

      println("begin generating initial predicates")
      val (simpleGeneratedPredicates,constraintPredicates,argumentConstantEqualPredicate) =  HintsSelection.getSimplePredicates(simplePredicatesGeneratorClauses)
      println("end generating initial predicates")
      val predicateGenerator= if (GlobalParameters.get.onlyInitialPredicates) exceptionalPredGen else predGenerator
      val (solvability,predicateFromCEGAR,_)=HintsSelection.checkSolvability(simplePredicatesGeneratorClauses,simpleGeneratedPredicates,predicateGenerator,counterexampleMethod,fileName = fileName,coefficient = 5)
      val originalPredicates = HintsSelection.mergePredicateMaps(HintsSelection.differentTwoPredicated(simpleGeneratedPredicates,predicateFromCEGAR).mapValues(_.map(sp(_)).map(spAPI.simplify(_))),simpleGeneratedPredicates).filterKeys(_.arity!=0).mapValues(_.filterNot(_.isFalse).filterNot(_.isTrue).toSeq)
      //val originalPredicates = predicateFromCEGAR.mapValues(_.map(sp(_)).map(spAPI.simplify(_))).filterKeys(_.arity!=0).mapValues(_.filterNot(_.isFalse).filterNot(_.isTrue).toSeq)
      //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
      val initialPredicates =
        if(GlobalParameters.get.varyGeneratedPredicates==true)
          HintsSelection.transformPredicateMapToVerificationHints(HintsSelection.varyPredicates(originalPredicates)) ++simpHints
        else
          HintsSelection.transformPredicateMapToVerificationHints(originalPredicates) ++simpHints


      generatingInitialPredicatesTime=(System.currentTimeMillis-predicatesExtractingBeginTime)/1000
      //double check if the generated predicates is enough to solve the problem
      HintsSelection.checkSolvability(simplePredicatesGeneratorClauses,initialPredicates.toInitialPredicates,exceptionalPredGen,counterexampleMethod,fileName)


      //predicates selection begin
      if (!initialPredicates.isEmpty) {
//        println("---initialHints-----")
//        for((k,v)<-initialPredicates.toInitialPredicates;p<-v)
//          println(k,p)
        val (optimizedPredicate,_)=HintsSelection.getMinimumSetPredicates(initialPredicates.toInitialPredicates,simplePredicatesGeneratorClauses,exceptionalPredGen,counterexampleMethod)
        predicatesExtractingTime=(System.currentTimeMillis-predicatesExtractingBeginTime)/1000

        if(!optimizedPredicate.isEmpty){
          //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
          val selectedPredicates= HintsSelection.transformPredicateMapToVerificationHints(optimizedPredicate)

          println("\n------------predicates selection end-------------------------")
          println("\nOptimized Hints:")
          selectedPredicates.pretyPrintHints()
          println("timeout:" + GlobalParameters.get.threadTimeout + "ms")


          val(_,_,test)=HintsSelection.checkSolvability(simplePredicatesGeneratorClauses,optimizedPredicate,exceptionalPredGen,counterexampleMethod,fileName,moveFileFolder = "test-timeout")

          val (unlabeledPredicates,labeledPredicates)=
            if(GlobalParameters.get.labelSimpleGeneratedPredicates==true) {
              val simpleGeneratedAndAbstractGeneratedPredicates=HintsSelection.mergePredicateMaps(simpHints.toInitialPredicates,simpleGeneratedPredicates).mapValues(_.map(sp(_)).filterNot(_.isTrue).filterNot(_.isFalse))
              val tempLabel=HintsSelection.conjunctTwoPredicates(simpleGeneratedAndAbstractGeneratedPredicates,optimizedPredicate)
              val labeledSimpleGeneratedPredicates = HintsSelection.transformPredicateMapToVerificationHints(tempLabel)//.filterKeys(k => !tempLabel(k).isEmpty)
              (HintsSelection.transformPredicateMapToVerificationHints(simpleGeneratedPredicates)++simpHints,labeledSimpleGeneratedPredicates)
            } else
              (initialPredicates,selectedPredicates)


          println("-"*10 + "unlabeledPredicates" + "-"*10)
          unlabeledPredicates.pretyPrintHints()
          println("-"*10 + "labeledPredicates" + "-"*10)
          labeledPredicates.pretyPrintHints()


          //simplePredicatesGeneratorClauses.map(_.toPrologString).foreach(x=>println(Console.BLUE + x))
          val drawGraphAndWriteLabelsBegin=System.currentTimeMillis
          if (!labeledPredicates.predicateHints.values.flatten.isEmpty){
            val clausesInCE= if (GlobalParameters.get.getLabelFromCounterExample ==true)
              getClausesInCounterExamples(test,simplePredicatesGeneratorClauses) else Seq()
            val clauseCollection = new ClauseInfo(simplePredicatesGeneratorClauses,clausesInCE)
            val hintsCollection=new VerificationHintsInfo(unlabeledPredicates,labeledPredicates,VerificationHints(Map()))//labeledPredicates
            //Output graphs
            val argumentList = (for (p <- HornClauses.allPredicates(simplePredicatesGeneratorClauses)) yield (p, p.arity)).toArray.sortBy(_._1.name)
            //val argumentInfo = HintsSelection.writeArgumentOccurrenceInHintsToFile(GlobalParameters.get.fileName, argumentList, simpHints,countOccurrence=false)
            val argumentInfo = HintsSelection.writeArgumentOccurrenceInHintsToFile(GlobalParameters.get.fileName, argumentList, labeledPredicates,countOccurrence=true)
            GraphTranslator.drawAllHornGraph(clauseCollection,hintsCollection,argumentInfo)

            //write predicates to files:
            HintsSelection.writePredicateDistributionToFiles(initialPredicates,selectedPredicates,labeledPredicates,unlabeledPredicates,HintsSelection.transformPredicateMapToVerificationHints(simpleGeneratedPredicates),HintsSelection.transformPredicateMapToVerificationHints(constraintPredicates),HintsSelection.transformPredicateMapToVerificationHints(argumentConstantEqualPredicate),outputAllPredicates=GlobalParameters.get.log)
            drawingGraphAndFormLabelsTime=(System.currentTimeMillis-drawGraphAndWriteLabelsBegin)/1000
          } else{
            HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/no-predicates-selected/"+fileName,"labeledPredicates is empty")
          }


        } else{
          HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/no-predicates-selected/"+fileName,"optimizedPredicate is empty")
        }

      }else{
        HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/no-predicates-selected/"+fileName,"originalPredicate is empty")
      }
      println(Console.GREEN + "time consumption before predicate extracting process: " + timeConsumptionBeforePredicateExtractingProcess + "s")
      println(Console.GREEN + "time for generating initial predicates: "+ generatingInitialPredicatesTime + "s")
      println(Console.GREEN + "predicates extracting time: "+ predicatesExtractingTime + "s")
      println(Console.GREEN + "Time for drawing graph and form labels: "+ drawingGraphAndFormLabelsTime +"s")
    }
  }
}



