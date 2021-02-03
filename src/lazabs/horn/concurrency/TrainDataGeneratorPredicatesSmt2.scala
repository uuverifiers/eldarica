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
import java.lang.System.currentTimeMillis
import lazabs.ast.ASTree._
import bottomup.{HornTranslator, _}
import abstractions.{AbsLattice, AbsReader, EmptyVerificationHints, VerificationHints}
import ap.parser._
import IExpression.{ConstantTerm, Eq, Geq, Predicate, Quantifier}
import bottomup.HornClauses.Clause
import bottomup.Util.Dag
import ap.parser._
import lazabs.GlobalParameters
import lazabs.Main.TimeoutException
import preprocessor.{ConstraintSimplifier, DefaultPreprocessor, HornPreprocessor}
import bottomup.HornClauses._
import global._
import abstractions._
import AbstractionRecord.AbstractionMap
import ap.SimpleAPI
import ap.terfor.conjunctions.Conjunction
import concurrency.HintsSelection.{getClausesInCounterExamples, initialIDForHints}
import concurrency._
import ap.basetypes.IdealInt
import ap.terfor.{ConstantTerm, Formula}
import ap.theories.TheoryCollector
import ap.types.TypeTheory
import ap.util.Timeout
import bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.HornPredAbs.{RelationSymbol, RelationSymbolPred, SymbolFactory}
import lazabs.horn.bottomup.PrincessFlataWrappers.MHashMap

import scala.collection.mutable.ArrayBuffer


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

      //simplify clauses. get rid of some redundancy
      val spAPI = ap.SimpleAPI.spawn
      val sp=new Simplifier
      val cs=new ConstraintSimplifier
      val (csSimplifiedClauses,_,_)=cs.process(simplifiedClauses,hints)
      val simplePredicatesGeneratorClauses = GlobalParameters.get.hornGraphType match {
        case DrawHornGraph.HornGraphType.hyperEdgeGraph | DrawHornGraph.HornGraphType.equivalentHyperedgeGraph | DrawHornGraph.HornGraphType.concretizedHyperedgeGraph => for(clause<-csSimplifiedClauses) yield clause.normalize()
        case _ => csSimplifiedClauses
      }
      //read hint from file
      if (GlobalParameters.get.readHints==true){
        println("-"*10 + "read predicate from .tpl" + "-"*10)
        //read initial predicates from .tpl
        val initialPredicates =VerificationHints(HintsSelection.wrappedReadHints(simplePredicatesGeneratorClauses).toInitialPredicates.mapValues(_.map(sp(_)).map(VerificationHints.VerifHintInitPred(_))))
        initialPredicates.pretyPrintHints()
        //todo:vary selected predicates but not change its logic
        val initialHintsCollection=new VerificationHintsInfo(initialPredicates,VerificationHints(Map()),VerificationHints(Map()))
        //read label from JSON
        val positiveHints= HintsSelection.readPredicateLabelFromJSON(initialHintsCollection,"templateRelevanceLabel")
        val hintsCollection=new VerificationHintsInfo(initialPredicates,positiveHints,initialPredicates.filterPredicates(positiveHints.predicateHints.keySet))

        val clauseCollection = new ClauseInfo(simplePredicatesGeneratorClauses,Seq())
        //Output graphs
        val argumentList = (for (p <- HornClauses.allPredicates(simplePredicatesGeneratorClauses)) yield (p, p.arity)).toArray
        val argumentInfo = HintsSelection.writeArgumentOccurrenceInHintsToFile(GlobalParameters.get.fileName, argumentList, positiveHints,countOccurrence=true)
        GraphTranslator.drawAllHornGraph(clauseCollection,hintsCollection,argumentInfo)

        sys.exit()
      }

      /////////////////////////predicates extracting begin///////////////////////////////
      val timeConsumptionBeforePredicateExtractingProcess=(System.currentTimeMillis-timeStart)/1000
      var generatingInitialPredicatesTime:Long=0
      var drawingGraphAndFormLabelsTime:Long=0
      var predicatesExtractingTime:Long=0
      val predicatesExtractingBeginTime=System.currentTimeMillis

      val startTimePredicateGenerator = currentTimeMillis
      val toParamsPredicateGenerator= GlobalParameters.get.clone
      toParamsPredicateGenerator.timeoutChecker = () => {
        if ((currentTimeMillis - startTimePredicateGenerator) > (GlobalParameters.get.solvabilityTimeout * 5) ) //timeout seconds
          throw lazabs.Main.TimeoutException //Main.TimeoutException
      }
      val simpleGeneratedPredicates =  HintsSelection.getSimplePredicates(simplePredicatesGeneratorClauses)

      val lastPredicates= {
        if(GlobalParameters.get.onlySimplePredicates==true)
          Map()
        else {
          try //GlobalParameters.parameters.withValue(toParamsPredicateGenerator)
          {Timeout.withChecker(toParamsPredicateGenerator.timeoutChecker)
            {
              val Cegar = new HornPredAbs(simplePredicatesGeneratorClauses,
                simpleGeneratedPredicates,
                //simpHints.toInitialPredicates, //use simple generated predicates as initial predicates
                predGenerator,
                counterexampleMethod)
              Cegar.predicates
            }


          }
          catch {
            case _ =>{
              val sourceFilename=GlobalParameters.get.fileName
              val destinationFilename="../benchmarks/solvability-timeout/" + GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/"),GlobalParameters.get.fileName.length)
              HintsSelection.moveRenameFile(sourceFilename,destinationFilename)
              sys.exit()
            }
          }
        }
      }

      var numberOfpredicates = 0
      val predicateFromCEGAR = for ((head, preds) <- lastPredicates) yield{
        // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
        val subst = (for ((c, n) <- head.arguments.head.iterator.zipWithIndex) yield (c, IVariable(n))).toMap
        //val headPredicate=new Predicate(head.name,head.arity) //class Predicate(val name : String, val arity : Int)
        val predicateSequence = for (p <- preds) yield {
          val simplifiedPredicate = sp(Internal2InputAbsy(p.rawPred, p.rs.sf.getFunctionEnc().predTranslation))
          val varPred = ConstantSubstVisitor(simplifiedPredicate, subst) //transform variables to _1,_2,_3...
          numberOfpredicates = numberOfpredicates + 1
          varPred
        }
        head.pred -> predicateSequence.distinct
      }
//      println(Console.BLUE + "predicateFromCEGAR")
//      for ((k,v)<-predicateFromCEGAR)
//        println(k,v)
      val originalPredicates =
        if(GlobalParameters.get.onlySimplePredicates==true)
          simpleGeneratedPredicates.mapValues(_.map(sp(_)))
        else if (GlobalParameters.get.generateSimplePredicates==true)
          predicateFromCEGAR.mapValues(_.map(sp(_)))
          //(simpleGeneratedPredicates.toSeq ++ predicateFromCEGAR.toSeq).groupBy(_._1).mapValues(_.flatMap(_._2).distinct).mapValues(_.map(sp(_)))
        else
          predicateFromCEGAR.mapValues(_.map(sp(_)))

      //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
      val initialPredicates = HintsSelection.transformPredicateMapToVerificationHints(originalPredicates)

      generatingInitialPredicatesTime=(System.currentTimeMillis-predicatesExtractingBeginTime)/1000

      val exceptionalPredGen: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>  //not generate new predicates
        Either[Seq[(Predicate, Seq[Conjunction])],
          Dag[(IAtom, HornPredAbs.NormClause)]] =
        (x: Dag[AndOrNode[HornPredAbs.NormClause, Unit]]) =>
          //throw new RuntimeException("interpolator exception")
          throw lazabs.Main.TimeoutException //if catch Counterexample and generate predicates, throw timeout exception

      println("check solvability using current predicates")
      val predicateGeneratorForSolvability =
        if(GlobalParameters.get.onlySimplePredicates==true)
          predGenerator
        else
          exceptionalPredGen
      val startTimeCEGAR = currentTimeMillis
      val toParamsCEGAR = GlobalParameters.get.clone
      toParamsCEGAR.timeoutChecker = () => {
        if ((currentTimeMillis - startTimeCEGAR) > GlobalParameters.get.solvabilityTimeout ) //timeout seconds
          throw lazabs.Main.TimeoutException //Main.TimeoutException
      }
      try{
        Timeout.withChecker(toParamsCEGAR.timeoutChecker) {
          new HornPredAbs(simplePredicatesGeneratorClauses,
            originalPredicates, predicateGeneratorForSolvability,
            counterexampleMethod)
        }
      }
      catch {
        case lazabs.Main.TimeoutException => {
          val sourceFilename=GlobalParameters.get.fileName
          val destinationFilename= "../benchmarks/solvability-timeout/" + GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/"),GlobalParameters.get.fileName.length)
          HintsSelection.moveRenameFile(sourceFilename,destinationFilename)
          sys.exit()//throw TimeoutException
        }
        case _ =>{println(Console.RED + "-----------solvability-debug------")}
      }

      //predicates selection begin
      if (!originalPredicates.isEmpty) {
//        val sortedHints = HintsSelection.sortHints(initialPredicates)
//        //write selected hints with IDs to file
//        val InitialHintsWithID =  HintsSelection.initialIDForHints(sortedHints) //ID:head->hint
//        println("---initialHints-----")
//        for (wrappedHint <- InitialHintsWithID) {
//          println(wrappedHint.ID.toString,wrappedHint.head,wrappedHint.hint)
//        }

//          println("------------test original predicates-------")
//          new HornPredAbs(simplePredicatesGeneratorClauses,
//            originalPredicates,//need Map[Predicate, Seq[IFormula]]
//            predGenerator,predicateFlag=false).result

        println("---initialHints-----")
        for((k,v)<-originalPredicates;p<-v)
          println(k,p)
        //Predicate selection begin
        println("------Predicates selection begin----")
        var PositiveHintsWithID:Seq[wrappedHintWithID]=Seq()
        var NegativeHintsWithID:Seq[wrappedHintWithID]=Seq()
        var optimizedPredicate: Map[Predicate, Seq[IFormula]] = Map()
        var currentPredicate: Map[Predicate, Seq[IFormula]] = originalPredicates
        val startTimeForExtraction = System.currentTimeMillis()
        for ((head, preds) <- originalPredicates) {
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
            println("currentPredicate",currentPredicate)

            //try cegar
            val startTime = System.currentTimeMillis()
            val toParams = GlobalParameters.get.clone
            toParams.timeoutChecker = () => {
              if ((currentTimeMillis - startTime) > GlobalParameters.get.threadTimeout)
                throw lazabs.Main.TimeoutException //Main.TimeoutException
            }
            try {
              //GlobalParameters.parameters.withValue(toParams)
              Timeout.withChecker(toParams.timeoutChecker){
                println("----------------------------------- CEGAR --------------------------------------")
                new HornPredAbs(simplePredicatesGeneratorClauses,
                  currentPredicate,
                  exceptionalPredGen,counterexampleMethod).result
                //not timeout
                redundantPredicatesSeq = redundantPredicatesSeq ++ Seq(p)
                //add useless hint to NegativeHintsWithID   //ID:head->hint
//                for (wrappedHint <- InitialHintsWithID) { //add useless hint to NegativeHintsWithID   //ID:head->hint
//                  val pVerifHintInitPred="VerifHintInitPred("+p.toString+")"
//                  if (head.name == wrappedHint.head && wrappedHint.hint == pVerifHintInitPred) {
//                    NegativeHintsWithID =NegativeHintsWithID++Seq(wrappedHint)
//                  }
//                }
                if(currentTimeMillis-startTimeForExtraction>GlobalParameters.get.mainTimeout)
                  throw lazabs.Main.MainTimeoutException
              }
            } catch {
              case lazabs.Main.TimeoutException => { //need new predicate or timeout
                criticalPredicatesSeq = criticalPredicatesSeq ++ Seq(p)
                //add deleted predicate back to curren predicate
                currentPredicate = currentPredicate.filterKeys(_ != head) //delete original head
                currentPredicate = currentPredicate ++ Map(head -> (currentPredicateSeq ++ Seq(p))) //add the head with deleted predicate
                //add useful hint to PositiveHintsWithID
//                for(wrappedHint<-InitialHintsWithID){
//                  val pVerifHintInitPred="VerifHintInitPred("+p.toString+")"
//                  if(head.name.toString()==wrappedHint.head && wrappedHint.hint==pVerifHintInitPred){
//                    PositiveHintsWithID=PositiveHintsWithID++Seq(wrappedHint)
//                  }
//                }
              }
              case _ =>{throw lazabs.Main.MainTimeoutException }
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

        predicatesExtractingTime=(System.currentTimeMillis-predicatesExtractingBeginTime)/1000

        if(!optimizedPredicate.isEmpty){
          //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
          val selectedPredicates= HintsSelection.transformPredicateMapToVerificationHints(optimizedPredicate)

          println("\n------------predicates selection end-------------------------")
          println("\nOptimized Hints:")
          selectedPredicates.pretyPrintHints()
          println("timeout:" + GlobalParameters.get.threadTimeout + "ms")

          val predicateGeneratorForTest =
            if(GlobalParameters.get.onlySimplePredicates==true)
              predGenerator
            else
              exceptionalPredGen

          try{
            println("\n------------test selected predicates-------------------------")
            val test = new HornPredAbs(simplePredicatesGeneratorClauses,
              optimizedPredicate,
              //selectedPredicates.toInitialPredicates,
              predicateGeneratorForTest,counterexampleMethod).result
            println("-"*10 + "test finished" + "-"*10)
            //simplePredicatesGeneratorClauses.map(_.toPrologString).foreach(x=>println(Console.BLUE + x))
            val drawGraphAndWriteLabelsBegin=System.currentTimeMillis
            if (!selectedPredicates.isEmpty){
              //todo:vary selected predicates but not change its logic
              selectedPredicates.pretyPrintHints()
              //optimizedPredicate.foreach(k=>{println(k._1);k._2.foreach(println)})
              val transformedPredicates=optimizedPredicate.mapValues(_.map(HintsSelection.varyPredicateWithOutLogicChanges(_)).map(sp(_)))
              HintsSelection.transformPredicateMapToVerificationHints(transformedPredicates).pretyPrintHints()
              //transformedPredicates.foreach(k=>{println(k._1);k._2.foreach(println)})

              val mergedPredicates=for ((cpKey, cpPredicates) <- transformedPredicates; (apKey, apPredicates) <- optimizedPredicate; if cpKey.equals(apKey)) yield cpKey -> (cpPredicates ++ apPredicates).distinct
              HintsSelection.transformPredicateMapToVerificationHints(mergedPredicates).pretyPrintHints()
              //mergedPredicates.foreach(k=>{println(k._1);k._2.foreach(println)})

              val hintsCollection=new VerificationHintsInfo(initialPredicates,selectedPredicates,initialPredicates.filterPredicates(selectedPredicates.predicateHints.keySet))
              val clausesInCE=getClausesInCounterExamples(test,simplePredicatesGeneratorClauses)
              val clauseCollection = new ClauseInfo(simplePredicatesGeneratorClauses,clausesInCE)
              //Output graphs
              val argumentList = (for (p <- HornClauses.allPredicates(simplePredicatesGeneratorClauses)) yield (p, p.arity)).toArray
              val argumentInfo = HintsSelection.writeArgumentOccurrenceInHintsToFile(GlobalParameters.get.fileName, argumentList, selectedPredicates,countOccurrence=true)
              GraphTranslator.drawAllHornGraph(clauseCollection,hintsCollection,argumentInfo)
              //Output selected predicates:
              val output = new java.io.FileOutputStream(GlobalParameters.get.fileName+".tpl")
              Console.withOut(output) {
                AbsReader.printHints(initialPredicates)
              }
              Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".selected.tpl")) {
                AbsReader.printHints(selectedPredicates)
              }
            }
            drawingGraphAndFormLabelsTime=(System.currentTimeMillis-drawGraphAndWriteLabelsBegin)/1000
          }catch{
            case lazabs.Main.TimeoutException =>{
              println(Console.RED + "--test timeout--")
              //todo: not include this to training example? because it can only provide negative training data
              val sourceFilename=GlobalParameters.get.fileName
              val destinationFilename= "../benchmarks/test-timeout/" + GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/"),GlobalParameters.get.fileName.length)
              HintsSelection.moveRenameFile(sourceFilename,destinationFilename)
            }
          }
        }
        else{
          println(Console.RED + "--optimizedPredicate is empty--")
          val sourceFilename=GlobalParameters.get.fileName
          val destinationFilename= "../benchmarks/no-predicates-selected/" + GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/"),GlobalParameters.get.fileName.length)
          HintsSelection.moveRenameFile(sourceFilename,destinationFilename)
        }




      }else{
        println(Console.RED + "--originalPredicate is empty--")
        val sourceFilename=GlobalParameters.get.fileName
        val destinationFilename= "../benchmarks/no-predicates-selected/" + GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/"),GlobalParameters.get.fileName.length)
        HintsSelection.moveRenameFile(sourceFilename,destinationFilename)
      }
      println(Console.GREEN + "time consumption before predicate extracting process: " + timeConsumptionBeforePredicateExtractingProcess + "s")
      println(Console.GREEN + "time for generating initial predicates: "+ generatingInitialPredicatesTime + "s")
      println(Console.GREEN + "predicates extracting time: "+ predicatesExtractingTime + "s")
      println(Console.GREEN + "Time for drawing graph and form labels: "+ drawingGraphAndFormLabelsTime +"s")
    }
  }
}



