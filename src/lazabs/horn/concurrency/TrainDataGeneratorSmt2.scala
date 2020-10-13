/**
 * Copyright (c) 2011-2020 Philipp Ruemmer, Chencheng Liang. All rights reserved.
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

package lazabs.horn
import java.io.{File, PrintWriter}

import lazabs.ast.ASTree._
import bottomup.{HornTranslator, _}
import ap.parser._
import IExpression.{ConstantTerm, Predicate, and, _}
import lazabs.horn.bottomup.HornClauses.{Clause, ConstraintClause, IConstraintClause, Literal}
import lazabs.horn.bottomup.Util.Dag
import ap.parser._
import lazabs.GlobalParameters
import lazabs.horn.preprocessor.{DefaultPreprocessor, HornPreprocessor}
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.global._
import lazabs.horn.abstractions.{AbsLattice, AbsReader, AbstractionRecord, EmptyVerificationHints, LoopDetector, StaticAbstractionBuilder, VerificationHints}
import AbstractionRecord.AbstractionMap
import lazabs.horn.concurrency.HintsSelection.initialIDForHints
import lazabs.horn.concurrency.{DrawHornGraph, DrawHyperEdgeHornGraph, DrawLayerHornGraph, GraphTranslator, GraphTranslator_hint, HintsSelection, ReaderMain}
import lazabs.viewer.HornPrinter




object TrainDataGeneratorSmt2 {
  def apply(clauseSet: Seq[HornClause],
            uppaalAbsMap: Option[Map[String, AbsLattice]],
            global: Boolean,
            disjunctive: Boolean,
            drawRTree: Boolean,
            lbe: Boolean) = {


    //////////solve-begin/////////


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
    } else {

      val result = try {
        //(new HornWrapper(clauseSet, uppaalAbsMap, lbe, disjunctive)).result

        //////////solve-end/////////

        /////////HornWrapper-begin////////////
        val constraints: Seq[HornClause] = clauseSet
        //val uppaalAbsMap: Option[Map[String, AbsLattice]]=uppaalAbsMap
        //lbe: Boolean,
        //disjunctive : Boolean

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

        val originalClauses = constraints
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

        /////////HornWrapper-end////////////

        /////////InnerHornWrapper-begin///////
        /** Automatically computed interpolation abstraction hints */
        val abstractionType =
          lazabs.GlobalParameters.get.templateBasedInterpolationType

        val counterexampleMethod =
          if (disjunctive)
            HornPredAbs.CounterexampleMethod.AllShortest
          else
            HornPredAbs.CounterexampleMethod.FirstBestShortest

        lazy val absBuilder =
          new StaticAbstractionBuilder(simplifiedClauses, abstractionType)

        //hints selection begin
        val hintsAbstraction: AbstractionMap =
          if (simpHints.isEmpty) Map()
          else absBuilder.loopDetector hints2AbstractionRecord simpHints

        val sortedHints = HintsSelection.sortHints(absBuilder.abstractionHints)
        var optimizedHints = sortedHints
        if (sortedHints.isEmpty) {
          println("No hints generated")
        } else {
          //write selected hints with IDs to file
          val InitialHintsWithID = initialIDForHints(sortedHints) //ID:head->hint
          println("---initialHints-----")
          for (wrappedHint <- InitialHintsWithID) {
            println(wrappedHint.ID.toString, wrappedHint.head, wrappedHint.hint)
          }

          val selectedHint = HintsSelection.tryAndTestSelectionTemplatesSmt(sortedHints,
            simplifiedClauses, GlobalParameters.get.fileName, InitialHintsWithID, counterexampleMethod, hintsAbstraction)
          optimizedHints = selectedHint
          if (selectedHint.isEmpty) { //when no hint available
            println("No hints selected (no need for hints)")
            //not write horn clauses to file
          } else {
            val fileName = GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/") + 1)
            val filePath=GlobalParameters.get.fileName.substring(0,GlobalParameters.get.fileName.lastIndexOf("/")+1)

            //write argument score to file
            val argumentList = (for (p <- HornClauses.allPredicates(simplifiedClauses)) yield (p, p.arity)).toList
            val argumentInfo= HintsSelection.writeArgumentScoreToFile(GlobalParameters.get.fileName, argumentList, selectedHint)

            //Output graphs
            //val hornGraph = new GraphTranslator(clauses, GlobalParameters.get.fileName)
            val hornGraph = new DrawHyperEdgeHornGraph(GlobalParameters.get.fileName, simplifiedClauses, sortedHints,argumentInfo)
            val hintGraph = new GraphTranslator_hint(simplifiedClauses, GlobalParameters.get.fileName, sortedHints, InitialHintsWithID)
            val layerHornGraph= new DrawLayerHornGraph(GlobalParameters.get.fileName, simplifiedClauses, sortedHints,argumentInfo)
            //write horn clauses to file
            val writer = new PrintWriter(new File(filePath + fileName + ".horn")) //python path
            writer.write(HornPrinter(clauseSet))
            writer.close()
            //HintsSelection.writeHornClausesToFile(system,GlobalParameters.get.fileName)
            //write smt2 format to file
            if (GlobalParameters.get.fileName.endsWith(".c")) { //if it is a c file
              HintsSelection.writeSMTFormatToFile(simplifiedClauses, filePath) //write smt2 format to file
            }
            if (GlobalParameters.get.fileName.endsWith(".smt2")) { //if it is a smt2 file
              //copy smt2 file
              val fileName = GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/") + 1)
              HintsSelection.moveRenameFile(GlobalParameters.get.fileName, filePath + fileName)
            }
          }
        }
        ///hints selection end

        lazy val autoAbstraction: AbstractionMap =
          absBuilder.abstractionRecords

//        /** Manually provided interpolation abstraction hints */
//        lazy val hintsAbstraction: AbstractionMap =
//          if (simpHints.isEmpty)
//            Map()
//          else
//            absBuilder.loopDetector hints2AbstractionRecord simpHints

        //////////////////////////////////////////////////////////////////////////////

        val predGenerator = Console.withErr(outStream) {
            if (lazabs.GlobalParameters.get.templateBasedInterpolation) {

              val fullAbstractionMap =
                AbstractionRecord.mergeMaps(hintsAbstraction, autoAbstraction) //hintsAbstraction,autoAbstraction are replaced by Map()

              if (fullAbstractionMap.isEmpty) {
                DagInterpolator.interpolatingPredicateGenCEXAndOr _
              }
              else {
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

          val result: Either[Map[Predicate, IFormula], Dag[IAtom]] = {
            val counterexampleMethod =
              if (disjunctive)
                HornPredAbs.CounterexampleMethod.AllShortest
              else
                HornPredAbs.CounterexampleMethod.FirstBestShortest

            val result = Console.withOut(outStream) {
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
        }
        catch
        {
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




