/**
 * Copyright (c) 2011-2019 Philipp Ruemmer. All rights reserved.
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

import java.io.{File, PrintWriter}
import java.lang.System.currentTimeMillis

import lazabs.ast.ASTree._
import global._
import bottomup.{HornTranslator, _}
import bottomup.HornPredAbs.RelationSymbol
import abstractions.{AbsLattice, AbsReader, EmptyVerificationHints, VerificationHints}
import ap.parser._
import IExpression.{ConstantTerm, Predicate, and, _}
import ap.types.MonoSortedPredicate
import lazabs.{GlobalParameters, ParallelComputation}
import lazabs.horn.bottomup.HornClauses.{Clause, ConstraintClause, IConstraintClause, Literal}
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.preprocessor.{DefaultPreprocessor, HornPreprocessor}
import lazabs.prover.PrincessWrapper
import lazabs.prover.PrincessWrapper.{formula2Eldarica, formula2Princess, type2Sort}
import lazabs.utils.Manip.freeVars

import scala.collection.mutable.LinkedHashMap
import ap.parser._
import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.types.MonoSortedPredicate
import lazabs.GlobalParameters
import lazabs.ParallelComputation
import lazabs.Main.{StoppedException, TimeoutException}
import lazabs.horn.preprocessor.{DefaultPreprocessor, HornPreprocessor}
import HornPreprocessor.BackTranslator
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.global._
import lazabs.utils.Manip._
import lazabs.prover.PrincessWrapper
import PrincessWrapper._
import lazabs.prover.Tree
import lazabs.types.Type
import lazabs.horn.bottomup.Util._
import HornPredAbs.RelationSymbol
import lazabs.horn.abstractions._
import AbstractionRecord.AbstractionMap
import ap.terfor.conjunctions.Conjunction
import lazabs.horn.concurrency.HintsSelection.initialIDForHints
import lazabs.horn.concurrency._

import scala.collection.immutable.ListMap
import scala.collection.mutable.{LinkedHashMap, HashMap => MHashMap, HashSet => MHashSet}
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, _}
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.viewer.HornPrinter

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


      val counterexampleMethod =
        if (disjunctive)
          HornPredAbs.CounterexampleMethod.AllShortest
        else
          HornPredAbs.CounterexampleMethod.FirstBestShortest

      /////////////////////////predicates extracting begin///////////////////////////////

      val timeOut = GlobalParameters.get.threadTimeout //timeout
      val solvabilityTimeout=GlobalParameters.get.solvabilityTimeout

      println("extract original predicates")
      //check solvability
      val startTimeCEGAR = currentTimeMillis
      val toParamsCEGAR = GlobalParameters.get.clone
      toParamsCEGAR.timeoutChecker = () => {
        if ((currentTimeMillis - startTimeCEGAR) > solvabilityTimeout * 1000) //timeout milliseconds
          throw lazabs.Main.TimeoutException //Main.TimeoutException
      }
      try{
        GlobalParameters.parameters.withValue(toParamsCEGAR) {
          new HornPredAbs(simplifiedClauses,
            simpHints.toInitialPredicates, predGenerator,
            counterexampleMethod)
          }
        }
      catch {
        case lazabs.Main.TimeoutException => {
          throw TimeoutException
        }
      }

      val Cegar = new HornPredAbs(simplifiedClauses,
        simpHints.toInitialPredicates, predGenerator,
        counterexampleMethod)

      val lastPredicates = Cegar.predicates


      //predicates selection begin
      val file = GlobalParameters.get.fileName
      val fileName = file.substring(file.lastIndexOf("/") + 1)


      ////////////////////
      if (lastPredicates.isEmpty) {
        //return VerificationHints(Map())
        var originalPredicates: Map[Predicate, Seq[IFormula]] = Map()
      }
      else {
        var originalPredicates: Map[Predicate, Seq[IFormula]] = Map()

        //show original predicates
        var numberOfpredicates = 0
        println("Original predicates:")
        for ((head, preds) <- lastPredicates) {
          // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
          println("key:" + head.pred)
          val subst = (for ((c, n) <- head.arguments.head.iterator.zipWithIndex) yield (c, IVariable(n))).toMap
          //val headPredicate=new Predicate(head.name,head.arity) //class Predicate(val name : String, val arity : Int)
          val predicateSequence = for (p <- preds) yield {
            val simplifiedPredicate = (new Simplifier) (Internal2InputAbsy(p.rawPred, p.rs.sf.functionEnc.predTranslation))
            //println("value:"+simplifiedPredicate)
            val varPred = ConstantSubstVisitor(simplifiedPredicate, subst) //transform variables to _1,_2,_3...
            println("value:" + varPred)
            numberOfpredicates = numberOfpredicates + 1
            varPred
          }
          originalPredicates = originalPredicates ++ Map(head.pred -> predicateSequence.distinct)
        }


        //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
        var initialPredicates = VerificationHints(Map())
        for ((head, preds) <- originalPredicates) {
          var x: Seq[VerifHintElement] = Seq()
          for (p <- preds) {
            x = x ++ Seq(VerificationHints.VerifHintInitPred(p))
          }
          initialPredicates = initialPredicates.addPredicateHints(Map(head -> x))
        }

        val sortedHints = HintsSelection.sortHints(initialPredicates)
        if (sortedHints.isEmpty) {} else {
          //write selected hints with IDs to file
          val InitialHintsWithID =  HintsSelection.initialIDForHints(sortedHints) //ID:head->hint
          println("---initialHints-----")
          for (wrappedHint <- InitialHintsWithID) {
            println(wrappedHint.ID.toString,wrappedHint.head,wrappedHint.hint)
          }

//          println("------------test original predicates-------")
//          new HornPredAbs(simplifiedClauses,
//            originalPredicates,//need Map[Predicate, Seq[IFormula]]
//            predGenerator,predicateFlag=false).result

          //Predicate selection begin
          println("------Predicates selection begin----")
          val exceptionalPredGen: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
            Either[Seq[(Predicate, Seq[Conjunction])],
              Dag[(IAtom, HornPredAbs.NormClause)]] =
            (x: Dag[AndOrNode[HornPredAbs.NormClause, Unit]]) =>
              //throw new RuntimeException("interpolator exception")
              throw lazabs.Main.TimeoutException

          var PositiveHintsWithID:Seq[wrappedHintWithID]=Seq()
          var NegativeHintsWithID:Seq[wrappedHintWithID]=Seq()
          var optimizedPredicate: Map[Predicate, Seq[IFormula]] = Map()
          var currentPredicate: Map[Predicate, Seq[IFormula]] = originalPredicates
          for ((head, preds) <- originalPredicates) {
            // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
            var criticalPredicatesSeq: Seq[IFormula] = Seq()
            var redundantPredicatesSeq: Seq[IFormula] = Seq()

            for (p <- preds) {
              println("before delete")
              println("head", head)
              println("predicates", currentPredicate(head)) //key not found
              //delete one predicate
              println("delete predicate", p)
              val currentPredicateSeq = currentPredicate(head).filter(_ != p) //delete one predicate
              currentPredicate = currentPredicate.filterKeys(_ != head) //delete original head
              currentPredicate = currentPredicate ++ Map(head -> currentPredicateSeq) //add the head with deleted predicate
              println("after delete")
              println("head", head)
              println("predicates", currentPredicate(head))

              //try cegar
              val startTime = currentTimeMillis
              val toParams = GlobalParameters.get.clone
              toParams.timeoutChecker = () => {
                if ((currentTimeMillis - startTime) > timeOut * 1000) //timeout milliseconds
                  throw lazabs.Main.TimeoutException //Main.TimeoutException
              }
              try {
                GlobalParameters.parameters.withValue(toParams) {
                  println(
                    "----------------------------------- CEGAR --------------------------------------")

                  new HornPredAbs(simplifiedClauses, // loop
                    currentPredicate, //emptyHints
                    exceptionalPredGen).result
                  //not timeout
                  redundantPredicatesSeq = redundantPredicatesSeq ++ Seq(p)
                  //add useless hint to NegativeHintsWithID   //ID:head->hint
                  for (wrappedHint <- InitialHintsWithID) { //add useless hint to NegativeHintsWithID   //ID:head->hint
                    val pVerifHintInitPred="VerifHintInitPred("+p.toString+")"
                    if (head.name.toString == wrappedHint.head && wrappedHint.hint == pVerifHintInitPred) {
                      NegativeHintsWithID =NegativeHintsWithID++Seq(wrappedHint)
                    }
                  }
                }
              } catch {
                case lazabs.Main.TimeoutException => {
                  //catch timeout
                  criticalPredicatesSeq = criticalPredicatesSeq ++ Seq(p)
                  //add deleted predicate back to curren predicate
                  currentPredicate = currentPredicate.filterKeys(_ != head) //delete original head
                  currentPredicate = currentPredicate ++ Map(head -> (currentPredicateSeq ++ Seq(p))) //add the head with deleted predicate
                  //add useful hint to PositiveHintsWithID
                  for(wrappedHint<-InitialHintsWithID){
                    val pVerifHintInitPred="VerifHintInitPred("+p.toString+")"
                    if(head.name.toString()==wrappedHint.head && wrappedHint.hint==pVerifHintInitPred){
                      PositiveHintsWithID=PositiveHintsWithID++Seq(wrappedHint)
                    }
                  }
                }
              }
            }
            //store selected predicate
            if (!criticalPredicatesSeq.isEmpty) {
              optimizedPredicate = optimizedPredicate ++ Map(head -> criticalPredicatesSeq)
            }
            println("current head:", head.toString())
            println("critical predicates:", criticalPredicatesSeq.toString())
            println("redundant predicates", redundantPredicatesSeq.toString())
          }
          //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
          var selectedPredicates = VerificationHints(Map())
          for ((head, preds) <- optimizedPredicate) {
            var x: Seq[VerifHintElement] = Seq()
            for (p <- preds) {
              x = x ++ Seq(VerificationHints.VerifHintInitPred(p))
            }
            selectedPredicates = selectedPredicates.addPredicateHints(Map(head -> x))
          }

          println("\n------------predicates selection end-------------------------")
          //println("\nsimpHints Hints:")
          //simpHints.pretyPrintHints()
          println("\nOptimized Hints:")
          println("!@@@@")
          selectedPredicates.pretyPrintHints()
          println("@@@@!")
          println("timeout:" + GlobalParameters.get.threadTimeout)

          println("\n------------test selected predicates-------------------------")
          val test = new HornPredAbs(simplifiedClauses, // loop
            selectedPredicates.toInitialPredicates, //emptyHints
            exceptionalPredGen).result
          println("-----------------test finished-----------------------")

          if (selectedPredicates.isEmpty) {

          } else {
            //only write to file when optimized hint is not empty
            HintsSelection.writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial") //write hints and their ID to file

            val writerPositive = new PrintWriter(new File("../trainData/"+fileName+".positiveHints")) //python path
            for(wrappedHint<-PositiveHintsWithID){
              writerPositive.write(wrappedHint.ID.toString+":"+wrappedHint.head+":"+wrappedHint.hint+"\n")
            }
            writerPositive.close()

            val writerNegative = new PrintWriter(new File("../trainData/"+fileName+".negativeHints")) //python path
            for(wrappedHint<-NegativeHintsWithID){
              writerNegative.write(wrappedHint.ID.toString+":"+wrappedHint.head+":"+wrappedHint.hint+"\n")
            }
            writerNegative.close()
//            HintsSelection.writeHintsWithIDToFile(PositiveHintsWithID, fileName, "positive")
//            HintsSelection.writeHintsWithIDToFile(NegativeHintsWithID, fileName, "negative")
          }

          //clauses:Seq[HornClauses.Clause],clauseSet: Seq[HornClause]

          //HintsSelection.writeHornAndGraphToFiles(selectedPredicates,sortedHints,simplifiedClauses,clauseSet)

          if(selectedPredicates.isEmpty){ //when no hint available
            println("No hints selected (no need for hints)")
            //not write horn clauses to file
          }else{

            //Output graphs
            //val hornGraph = new GraphTranslator(simplifiedClauses, GlobalParameters.get.fileName)
            DrawHornGraph.writeHornClausesGraphToFile(GlobalParameters.get.fileName,simplifiedClauses,sortedHints)
            val hintGraph= new GraphTranslator_hint(simplifiedClauses, GlobalParameters.get.fileName, sortedHints,InitialHintsWithID)
            val argumentList=(for (p <- HornClauses.allPredicates(simplifiedClauses)) yield (p, p.arity)).toList
            HintsSelection.writeArgumentScoreToFile(GlobalParameters.get.fileName,argumentList,selectedPredicates)

            //write horn clauses to file
            val fileName=GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/")+1)
            val writer = new PrintWriter(new File("../trainData/"+fileName+".horn")) //python path
            writer.write(HornPrinter(clauseSet))
            writer.close()
            //HintsSelection.writeHornClausesToFile(system,GlobalParameters.get.fileName)
            //write smt2 format to file
            if(GlobalParameters.get.fileName.endsWith(".c")){ //if it is a c file
              HintsSelection.writeSMTFormatToFile(simplifiedClauses,"../trainData/")  //write smt2 format to file
            }
            if(GlobalParameters.get.fileName.endsWith(".smt2")){ //if it is a smt2 file
              //copy smt2 file
              val fileName=GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/")+1)
              HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../trainData/"+fileName)
            }

          }


        }

      }







    }
  }
}



