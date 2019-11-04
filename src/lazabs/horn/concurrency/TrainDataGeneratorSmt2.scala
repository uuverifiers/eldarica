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
import lazabs.horn.abstractions.{AbsLattice, AbsReader, AbstractionRecord, EmptyVerificationHints, LoopDetector, StaticAbstractionBuilder,
  StaticAbstractionBuilderSmtHintsSelection,VerificationHints}
import AbstractionRecord.AbstractionMap
import lazabs.horn.concurrency.HintsSelection.initialIDForHints
import lazabs.horn.concurrency.{GraphTranslator, GraphTranslator_hint, HintsSelection, ReaderMain}

import scala.collection.immutable.ListMap
import scala.collection.mutable.{LinkedHashMap, HashMap => MHashMap, HashSet => MHashSet}


object TrainDataGeneratorSmt2{
  def apply(clauseSet: Seq[HornClause],
            uppaalAbsMap: Option[Map[String, AbsLattice]],
            global: Boolean,
            disjunctive : Boolean,
            drawRTree: Boolean,
            lbe: Boolean) = {



    //////////solve-begin/////////


    val log = lazabs.GlobalParameters.get.log

    /*    if(clauseSet.size == 0) {
          println("No Horn clause")
          sys.exit(0)
        }       */

    val arities = clauseSet.map(cl => Horn.getRelVarArities(cl)).reduceLeft(_++_)
    val timeStart = System.currentTimeMillis

    def printTime =
      if (lazabs.GlobalParameters.get.logStat)
        Console.err.println(
          "Total elapsed time (ms): " + (System.currentTimeMillis - timeStart))

    if(global) {
      val cegar = new HornCegar(clauseSet,log)
      val arg = cegar.apply

      printTime

      if(log && cegar.status == Status.SAFE) {
        for((i,sol) <- arg.reportSolution) {
          val cl = HornClause(
            RelVar(i,(0 until arities(i)).map(p => Parameter("_" + p,lazabs.types.IntegerType())).toList),
            List(Interp(sol))
          )
          println(lazabs.viewer.HornPrinter.print(cl))
        }
      }
      if(drawRTree) lazabs.viewer.DrawGraph(arg)
    } else {

      val result = try {
        //(new HornWrapper(clauseSet, uppaalAbsMap, lbe, disjunctive)).result

        //////////solve-end/////////

        /////////HornWrapper-begin////////////
        val constraints: Seq[HornClause]=clauseSet
        //val uppaalAbsMap: Option[Map[String, AbsLattice]]=uppaalAbsMap
        //lbe: Boolean,
        //disjunctive : Boolean

        def printClauses(cs : Seq[Clause]) = {
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

        val originalClauses = constraints
        val unsimplifiedClauses = originalClauses map (transform(_))

        //    if (GlobalParameters.get.printHornSimplified)
        //      printMonolithic(unsimplifiedClauses)

        val name2Pred =
        (for (Clause(head, body, _) <- unsimplifiedClauses.iterator;
              IAtom(p, _) <- (head :: body).iterator)
          yield (p.name -> p)).toMap

        //////////////////////////////////////////////////////////////////////////////

        val hints : VerificationHints =
        GlobalParameters.get.cegarHintsFile match {
          case "" =>
            EmptyVerificationHints
          case hintsFile => {
            val reader = new AbsReader (
              new java.io.BufferedReader (
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


        /////////HornWrapper-end////////////


        /////////InnerHornWrapper-begin///////


        //inputs
        //val unsimplifiedClauses : Seq[Clause]=unsimplifiedClauses
        //val simplifiedClauses : Seq[Clause]=simplifiedClauses
        //val simpHints : VerificationHints=simpHints
        //val preprocBackTranslator : BackTranslator=preprocBackTranslator
        //val disjunctive : Boolean=disjunctive
        //val outStream : java.io.OutputStream=outStream



        /** Automatically computed interpolation abstraction hints */
        val abstractionType =
        lazabs.GlobalParameters.get.templateBasedInterpolationType

        val counterexampleMethod =
          if (disjunctive)
            HornPredAbs.CounterexampleMethod.AllShortest
          else
            HornPredAbs.CounterexampleMethod.FirstBestShortest

        ///hints selection begin

        lazy val absBuilder =
        new StaticAbstractionBuilderSmtHintsSelection(simplifiedClauses, abstractionType,counterexampleMethod,simpHints,clauseSet)


        lazy val autoAbstraction : AbstractionMap =
        absBuilder.abstractionRecords

        /** Manually provided interpolation abstraction hints */
        lazy val hintsAbstraction : AbstractionMap =
        if (simpHints.isEmpty)
          Map()
        else
          absBuilder.loopDetector hints2AbstractionRecord simpHints

        //////////////////////////////////////////////////////////////////////////////

        val predGenerator = Console.withErr(outStream) {
          if (lazabs.GlobalParameters.get.templateBasedInterpolation) {
            val fullAbstractionMap =
              AbstractionRecord.mergeMaps(hintsAbstraction, autoAbstraction)//hintsAbstraction,autoAbstraction are replaced by Map()

            if (fullAbstractionMap.isEmpty){
              DagInterpolator.interpolatingPredicateGenCEXAndOr _
            }
            else{
              TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
                fullAbstractionMap,
                lazabs.GlobalParameters.get.templateBasedInterpolationTimeout)
            }
          } else {
            DagInterpolator.interpolatingPredicateGenCEXAndOr _
          }
        }


//        if (GlobalParameters.get.templateBasedInterpolationPrint &&
//          !simpHints.isEmpty){
//          ReaderMain.printHints(simpHints, name = "Manual verification hints:")
//        }

        //////////////////////////////////////////////////////////////////////////////






        val result : Either[Map[Predicate, IFormula], Dag[IAtom]] = {
          val counterexampleMethod =
            if (disjunctive)
              HornPredAbs.CounterexampleMethod.AllShortest
            else
              HornPredAbs.CounterexampleMethod.FirstBestShortest

          val result = Console.withOut(outStream) {
//
//            println("--------Hints selection begin-----------")
//            var optimizedHints=absBuilder.abstractionHints
//            val SimplifiedHints=absBuilder.abstractionHints
//            if(SimplifiedHints.isEmpty){
//              println("No hints generated")
//            }else{
//              //write selected hints with IDs to file
//              val InitialHintsWithID=initialIDForHints(SimplifiedHints) //ID:head->hint
//              println("---initialHints-----")
//              for ((key,value)<-ListMap(InitialHintsWithID.toSeq.sortBy(_._1):_*)){
//                println(key,value)
//              }
//
//              val selectedHint=HintsSelection.tryAndTestSelectonSmt(SimplifiedHints,
//                simplifiedClauses,GlobalParameters.get.fileName,InitialHintsWithID,counterexampleMethod,hintsAbstraction,autoAbstraction)
//              optimizedHints=selectedHint
//              if(selectedHint.isEmpty){ //when no hint available
//                println("No hints selected (no need for hints)")
//                //not write horn clauses to file
//              }else{
//                //write horn clauses to file
//                //HintsSelection.writeHornClausesToFile(system,GlobalParameters.get.fileName)
//                //write smt2 format to file
//                if(GlobalParameters.get.fileName.endsWith(".c")){ //if it is a c file
//                  HintsSelection.writeSMTFormatToFile(simplifiedClauses)  //write smt2 format to file
//                }
//                if(GlobalParameters.get.fileName.endsWith(".smt2")){ //if it is a smt2 file
//                  //copy smt2 file
//                }
//
//
//
//                //Output graphs
//                val hornGraph = new GraphTranslator(simplifiedClauses, GlobalParameters.get.fileName)
//                val hintGraph= new GraphTranslator_hint(simplifiedClauses, GlobalParameters.get.fileName, SimplifiedHints)
//              }
//
//            }


            /////////////test/////////////
            println
            println(
              "----------------------------------- CEGAR --------------------------------------")
            (new HornPredAbs(simplifiedClauses,
              simpHints.toInitialPredicates, predGenerator,
              counterexampleMethod)).result
          }

          result match {
            case Left(res) =>
              if (lazabs.GlobalParameters.get.needFullSolution) {
                val fullSol = preprocBackTranslator translate res
                HornWrapper.verifySolution(fullSol, unsimplifiedClauses)
                Left(fullSol)
              } else {
                // only keep relation symbols that were also part of the orginal problem
                Left(res filterKeys allPredicates(unsimplifiedClauses))
              }

            case Right(cex) =>
              if (lazabs.GlobalParameters.get.needFullCEX) {
                val fullCEX = preprocBackTranslator translate cex
                HornWrapper.verifyCEX(fullCEX, unsimplifiedClauses)
                Right(for (p <- fullCEX) yield p._1)
              } else {
                Right(for (p <- cex) yield p._1)
              }
          }
        }



        /////////InnerHornWrapper-end///////

        println("--------finished-----------")








      } catch {
        case t@(lazabs.Main.TimeoutException |
                lazabs.Main.StoppedException) => {
          println("unknown")
          printTime
          throw t
        }
      }
    }





  }

}




