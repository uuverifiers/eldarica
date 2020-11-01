/**
 * Copyright (c) 2011-2020 Philipp Ruemmer, CHencheng Liang. All rights reserved.
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
import ap.terfor.preds.Predicate
import ap.parser.{IExpression, _}
import lazabs.GlobalParameters
import lazabs.horn.abstractions.{AbstractionRecord, LoopDetector, StaticAbstractionBuilder, VerificationHints}
import lazabs.horn.bottomup._

import scala.io.Source
import scala.collection.mutable.{LinkedHashMap, ListBuffer, HashMap => MHashMap, HashSet => MHashSet}
import java.io.{File, FileWriter, PrintWriter}

import ap.terfor.conjunctions.Conjunction
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, _}
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import java.nio.file.{Files, Paths, StandardCopyOption}

import ap.parser._
import IExpression._
import lazabs.horn.bottomup.HornClauses
import java.lang.System.currentTimeMillis

import ap.PresburgerTools
import ap.theories.TheoryCollector
import ap.types.TypeTheory
import lazabs.horn.bottomup.HornPredAbs.{NormClause, RelationSymbol, SymbolFactory}

class wrappedHintWithID {
  var ID: Int = 0
  var head: String = ""
  var hint: String = ""

  def this(ID: Int, head: String, hint: String) = {
    this();
    this.ID = ID;
    this.head = head;
    this.hint = hint;
  }
}

object HintsSelection {
  def sortHints(hints: VerificationHints): VerificationHints = {
    var tempHints = VerificationHints(Map()) //sort the hints
    for ((oneHintKey, oneHintValue) <- hints.getPredicateHints()) {
      val tempSeq = oneHintValue.sortBy(oneHintValue => (oneHintValue.toString, oneHintValue.toString))
      tempHints = tempHints.addPredicateHints(Map(oneHintKey -> tempSeq))
    }
    //    println("tempHints")
    //    tempHints.pretyPrintHints()
    return tempHints
  }


  def getInitialPredicates(encoder: ParametricEncoder, simpHints: VerificationHints, simpClauses: Clauses): VerificationHints = {
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
              loopDetector hints2AbstractionRecord simpHints //emptyHints
            //DEBUG

            println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

            AbstractionRecord.mergeMaps(autoAbstractionMap, hintsAbstractionMap) //autoAbstractionMap=Map()
          }

        TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
          abstractionMap,
          GlobalParameters.get.templateBasedInterpolationTimeout)
      } else {
      DagInterpolator.interpolatingPredicateGenCEXAndOr _
    }

    println("extract original predicates")
    val cegar = new HornPredAbs(simpClauses,
      simpHints.toInitialPredicates,
      interpolator)

    val LastPredicate = cegar.predicates //Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]]

    var originalPredicates: Map[Predicate, Seq[IFormula]] = Map()
    //show original predicates
    var numberOfpredicates = 0
    println("Original predicates:")
    for ((head, preds) <- LastPredicate) {
      // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
      println("key:" + head.pred)
      val subst = (for ((c, n) <- head.arguments.head.iterator.zipWithIndex) yield (c, IVariable(n))).toMap
      //val headPredicate=new Predicate(head.name,head.arity) //class Predicate(val name : String, val arity : Int)
      val predicateSequence = for (p <- preds) yield {
        val simplifiedPredicate = (new Simplifier) (Internal2InputAbsy(p.rawPred, p.rs.sf.getFunctionEnc().predTranslation))
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
    //    var initialPredicates:VerificationHints=VerificationHints(Map())
    //    for((head,preds)<-originalPredicates){
    //      val predicateSeq=
    //      for (p<-preds)yield {
    //        VerificationHints.VerifHintInitPred(p)
    //      }
    //      initialPredicates=initialPredicates.addPredicateHints(Map(head->predicateSeq))
    //    }
    return initialPredicates
  }


  def tryAndTestSelectionPredicate(encoder: ParametricEncoder, simpHints: VerificationHints,
                                   simpClauses: Clauses, file: String, InitialHintsWithID: Seq[wrappedHintWithID]): VerificationHints = {

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
              loopDetector hints2AbstractionRecord simpHints //emptyHints currentTemplates
            //DEBUG

            println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

            AbstractionRecord.mergeMaps(autoAbstractionMap, hintsAbstractionMap) //autoAbstractionMap=Map()
          }

        TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
          abstractionMap,
          GlobalParameters.get.templateBasedInterpolationTimeout)
      } else {
      DagInterpolator.interpolatingPredicateGenCEXAndOr _
    }
    val fileName = file.substring(file.lastIndexOf("/") + 1)
    val timeOut = GlobalParameters.get.threadTimeout //timeout

    val exceptionalPredGen: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
      Either[Seq[(Predicate, Seq[Conjunction])],
        Dag[(IAtom, HornPredAbs.NormClause)]] =
      (x: Dag[AndOrNode[HornPredAbs.NormClause, Unit]]) =>
        //throw new RuntimeException("interpolator exception")
        throw lazabs.Main.TimeoutException

    println("extract original predicates")
    val cegar = new HornPredAbs(simpClauses,
      simpHints.toInitialPredicates,
      interpolator)

    val LastPredicate = cegar.predicates //Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]]
    if (LastPredicate.isEmpty) {
      return VerificationHints(Map())
    } else {

      var originalPredicates: Map[Predicate, Seq[IFormula]] = Map()
      //show LastPredicate
      println("Original predicates:")
      for ((head, preds) <- LastPredicate) {
        // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
        val subst = (for ((c, n) <- head.arguments.head.iterator.zipWithIndex) yield (c, IVariable(n))).toMap
        //val headPredicate=new Predicate(head.name,head.arity) //class Predicate(val name : String, val arity : Int)
        val predicateSequence = for (p <- preds) yield {
          val simplifiedPredicate = (new Simplifier) (Internal2InputAbsy(p.rawPred, p.rs.sf.getFunctionEnc().predTranslation))
          //println("value:"+simplifiedPredicate)
          val varPred = ConstantSubstVisitor(simplifiedPredicate, subst) //transform variables to _1,_2,_3...
          println("value:" + varPred)
          varPred
        }
        originalPredicates = originalPredicates ++ Map(head.pred -> predicateSequence.distinct)
      }

      //      var initialPredicates = VerificationHints(Map())
      //      for ((head, preds) <- originalPredicates) {
      //        var x: Seq[VerifHintElement] = Seq()
      //        for (p <- preds) {
      //          x = x ++ Seq(VerificationHints.VerifHintInitPred(p))
      //        }
      //        initialPredicates = initialPredicates.addPredicateHints(Map(head -> x))
      //      }
      //
      //      val sortedHints=HintsSelection.sortHints(initialPredicates)
      ////      if(sortedHints.isEmpty){}else{
      //        //write selected hints with IDs to file
      //        val InitialHintsWithID=initialIDForHints(sortedHints) //ID:head->hint
      //        println("---initialHints-----")
      //        for (wrappedHint<-InitialHintsWithID){
      //          println(wrappedHint.ID.toString,wrappedHint.head,wrappedHint.hint)
      //        }

      //Predicate selection begin
      println("------Predicates selection begin----")
      var PositiveHintsWithID: Seq[wrappedHintWithID] = Seq()
      var NegativeHintsWithID: Seq[wrappedHintWithID] = Seq()
      var optimizedPredicate: Map[Predicate, Seq[IFormula]] = Map()
      var currentPredicate: Map[Predicate, Seq[IFormula]] = originalPredicates
      for ((head, preds) <- originalPredicates) {
        // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
        var criticalPredicatesSeq: Seq[IFormula] = Seq()
        var redundantPredicatesSeq: Seq[IFormula] = Seq()
        var CurrentTemplates = VerificationHints(Map())

        for (p <- preds) {
          //println("before delete")
          //          println("head",head)
          //          println("predicates",currentPredicate(head))
          //          //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
          //          for ((head,preds)<-currentPredicate) {
          //            val x:Seq[VerifHintElement]=
          //            for (p<-preds)yield{
          //              VerificationHints.VerifHintInitPred(p)
          //            }
          //            CurrentTemplates=CurrentTemplates.addPredicateHints(Map(head->x))
          //          }
          //          CurrentTemplates=HintsSelection.sortHints(CurrentTemplates)
          //          CurrentTemplates.pretyPrintHints()

          //delete one predicate
          println("delete predicate", p)
          val currentPredicateSeq = currentPredicate(head).filter(_ != p) //delete one predicate
          currentPredicate = currentPredicate.filterKeys(_ != head) //delete original head
          if (!currentPredicateSeq.isEmpty) {
            currentPredicate = currentPredicate ++ Map(head -> currentPredicateSeq) //add the head with deleted predicate
          }

          //println("after delete")
          //          println("head",head)
          //          println("predicates",currentPredicate(head))

          //          //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
          //          for ((head,preds)<-currentPredicate) {
          //            var x:Seq[VerifHintElement]=Seq()
          //            for (p<-preds){
          //              x=x++Seq(VerificationHints.VerifHintInitPred(p))
          //            }
          //            CurrentTemplates=CurrentTemplates.addPredicateHints(Map(head->x))
          //          }
          //          CurrentTemplates=HintsSelection.sortHints(CurrentTemplates)
          //          CurrentTemplates.pretyPrintHints()


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

              new HornPredAbs(simpClauses, // loop
                currentPredicate, //emptyHints currentPredicate CurrentTemplates
                exceptionalPredGen).result
              //not timeout
              println("add redundant predicate", p.toString)
              redundantPredicatesSeq = redundantPredicatesSeq ++ Seq(p)
              //add useless hint to NegativeHintsWithID   //ID:head->hint
              for (wrappedHint <- InitialHintsWithID) {
                val pVerifHintInitPred = "VerifHintInitPred(" + p.toString + ")"
                if (wrappedHint.head == head.name.toString && wrappedHint.hint == pVerifHintInitPred) {
                  NegativeHintsWithID = NegativeHintsWithID ++ Seq(wrappedHint) //some redundancy
                }
              }
            }
          } catch {
            case lazabs.Main.TimeoutException => {
              //catch timeout
              println("add critical predicate", p.toString)
              criticalPredicatesSeq = criticalPredicatesSeq ++ Seq(p)
              //add deleted predicate back to curren predicate
              currentPredicate = currentPredicate.filterKeys(_ != head) //delete original head
              currentPredicate = currentPredicate ++ Map(head -> (currentPredicateSeq ++ Seq(p))) //add the head with deleted predicate
              //
              for (wrappedHint <- InitialHintsWithID) { //add useful hint to PositiveHintsWithID
                val pVerifHintInitPred = "VerifHintInitPred(" + p.toString + ")"
                if (head.name.toString() == wrappedHint.head && wrappedHint.hint == pVerifHintInitPred) {
                  PositiveHintsWithID = PositiveHintsWithID ++ Seq(wrappedHint)
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
      var selectedTemplates = VerificationHints(Map())
      for ((head, preds) <- optimizedPredicate) {
        var x: Seq[VerifHintElement] = Seq()
        for (p <- preds) {
          x = x ++ Seq(VerificationHints.VerifHintInitPred(p))
        }
        selectedTemplates = selectedTemplates.addPredicateHints(Map(head -> x))
      }

      println("\n------------predicates selection end-------------------------")
      //println("\nsimpHints Hints:")
      //simpHints.pretyPrintHints()
      println("\nOptimized Hints:")
      println("!@@@@")
      selectedTemplates.pretyPrintHints()
      println("@@@@!")
      println("timeout:" + GlobalParameters.get.threadTimeout)

      println("\n------------test selected predicates-------------------------")
      val test = new HornPredAbs(simpClauses, // loop
        selectedTemplates.toInitialPredicates, //emptyHints
        exceptionalPredGen).result
      println("-----------------test finished-----------------------")

      if (selectedTemplates.isEmpty) {
        //writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial") //write hints and their ID to file
      } else {
        //only write to file when optimized hint is not empty
        writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial") //write hints and their ID to file
        writeHintsWithIDToFile(PositiveHintsWithID, fileName, "positive")
        writeHintsWithIDToFile(NegativeHintsWithID, fileName, "negative")
      }

      return selectedTemplates
    }

  }


  def tryAndTestSelectionTemplates(encoder: ParametricEncoder, simpHints: VerificationHints,
                                   simpClauses: Clauses, file: String, InitialHintsWithID: Seq[wrappedHintWithID],
                                   predicateFlag: Boolean = true): VerificationHints = {


    val fileName = file.substring(file.lastIndexOf("/") + 1)
    val timeOut = GlobalParameters.get.threadTimeout //timeout
    var currentTemplates = simpHints
    var optimizedTemplates = VerificationHints(Map())
    var PositiveHintsWithID: Seq[wrappedHintWithID] = Seq()
    var NegativeHintsWithID: Seq[wrappedHintWithID] = Seq()

    println("-------------------------Hints selection begins------------------------------------------")
    if (simpHints.isEmpty) {
      return simpHints
    } else {
      for ((head, preds) <- simpHints.predicateHints) {
        var criticalTemplatesSeq: Seq[VerifHintElement] = Seq()
        var redundantTemplatesSeq: Seq[VerifHintElement] = Seq()
        for (p <- preds) {
          //delete on template in a head
          val currentTemplatesList = currentTemplates.getValue(head).filter(_ != p)
          currentTemplates = currentTemplates.filterNotPredicates(Set(head))

          currentTemplates = currentTemplates.addPredicateHints(Map(head -> currentTemplatesList))

          //try cegar

          val startTime = currentTimeMillis
          val toParams = GlobalParameters.get.clone
          toParams.timeoutChecker = () => {
            if ((currentTimeMillis - startTime) > timeOut * 1000) //timeout milliseconds
              throw lazabs.Main.TimeoutException //Main.TimeoutException
          }
          try {
            GlobalParameters.parameters.withValue(toParams) {
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
                currentTemplates.toInitialPredicates, //emptyHints
                interpolator).result

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
      //println("\nsimpHints Hints:")
      //simpHints.pretyPrintHints()
      println("\nOptimized Hints:")
      println("!@@@@")
      optimizedTemplates.pretyPrintHints()
      println("@@@@!")
      println("timeout:" + GlobalParameters.get.threadTimeout)
      //GlobalParameters.get.printHints=optimizedHints


      if (optimizedTemplates.isEmpty) {
        //writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial")//write hints and their ID to file
      } else {
        //only write to file when optimized hint is not empty
        writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial")//write hints and their ID to file
        writeHintsWithIDToFile(PositiveHintsWithID, fileName, "positive")
        writeHintsWithIDToFile(NegativeHintsWithID, fileName, "negative")
      }


      return optimizedTemplates
    }


  }


  def tryAndTestSelectionTemplatesSmt(simpHints: VerificationHints, simpClauses: Clauses, file: String, InitialHintsWithID: Seq[wrappedHintWithID],
                                      counterexampleMethod: HornPredAbs.CounterexampleMethod.Value =
                                      HornPredAbs.CounterexampleMethod.FirstBestShortest,
                                      hintsAbstraction: AbstractionMap
                                     ): VerificationHints = {

    val fileName = file.substring(file.lastIndexOf("/") + 1)
    val timeOut = GlobalParameters.get.threadTimeout //timeout
    //val timeOut=10
    var currentTemplates = simpHints
    var optimizedHints = VerificationHints(Map()) // store final selected heads and hints
    //val InitialHintsWithID=initialIDForHints(simpHints)
    var PositiveHintsWithID: Seq[wrappedHintWithID] = Seq()
    var NegativeHintsWithID: Seq[wrappedHintWithID] = Seq()

    if (simpHints.isEmpty || lazabs.GlobalParameters.get.templateBasedInterpolation == false) {
      println("simpHints is empty or abstract:off")
      return simpHints
    }
    else {
      println("-------------------------Hints selection begins------------------------------------------")
      for ((head, oneHintValue) <- simpHints.getPredicateHints()) { //loop for head
        println("Head:" + head)
        println(oneHintValue)
        var criticalHintsList: Seq[VerifHintElement] = Seq()
        var redundantHintsList: Seq[VerifHintElement] = Seq()
        var currentHintsList = simpHints.getValue(head) //extract hints in this head

        for (oneHint <- simpHints.getValue(head)) { //loop for every hint in one head
          println("Current hints:")
          currentTemplates.pretyPrintHints()

          println("delete: \n" + head + " \n" + oneHint)
          currentHintsList = currentHintsList.filter(_ != oneHint) //delete one hint from hint list
          currentTemplates = currentTemplates.filterNotPredicates(Set(head)) //delete the head

          currentTemplates = currentTemplates.addPredicateHints(Map(head -> currentHintsList)) //add head with one hint back

          println("After delete:\n")
          currentTemplates.pretyPrintHints()

          val startTime = currentTimeMillis
          val toParams = GlobalParameters.get.clone
          toParams.timeoutChecker = () => {
            if ((currentTimeMillis - startTime) > timeOut * 1000) //timeout milliseconds
              throw lazabs.Main.TimeoutException //Main.TimeoutException
          }

          try {
            GlobalParameters.parameters.withValue(toParams) {
              val outStream =
                if (GlobalParameters.get.logStat)
                  Console.err
                else
                  HornWrapper.NullStream
              val loopDetector = new LoopDetector(simpClauses)
              val autoAbstraction = loopDetector.hints2AbstractionRecord(currentTemplates)
              val predGenerator = Console.withErr(outStream) {
                if (lazabs.GlobalParameters.get.templateBasedInterpolation) {
                  val fullAbstractionMap =
                    AbstractionRecord.mergeMaps(Map(), autoAbstraction) //hintsAbstraction,autoAbstraction replaced by Map()

                  if (fullAbstractionMap.isEmpty) {
                    DagInterpolator.interpolatingPredicateGenCEXAndOr _
                  }

                  else {
                    TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
                      fullAbstractionMap,
                      lazabs.GlobalParameters.get.templateBasedInterpolationTimeout)
                  }

                } else {
                  DagInterpolator.interpolatingPredicateGenCEXAndOr _ //if abstract:off
                }
              }
              println(
                "----------------------------------- CEGAR --------------------------------------")

              (new HornPredAbs(simpClauses, //simplifiedClauses
                currentTemplates.toInitialPredicates, predGenerator,
                counterexampleMethod)).result

              // not timeout ...
              println("Delete a redundant hint:\n" + head + "\n" + oneHint)
              redundantHintsList = redundantHintsList ++ Seq(oneHint)
              //add useless hint to NegativeHintsWithID   //ID:head->hint
              for (wrappedHint <- InitialHintsWithID) {
                if (head.name.toString == wrappedHint.head && wrappedHint.hint == oneHint.toString) {
                  NegativeHintsWithID = NegativeHintsWithID ++ Seq(wrappedHint)
                }
              }

            }

          } catch {
            // ,... Main.TimeoutException
            //time out
            case lazabs.Main.TimeoutException =>
              println("Add a critical hint\n" + head + "\n" + oneHint)
              criticalHintsList = criticalHintsList ++ Seq(oneHint)
              currentHintsList = currentHintsList ++ Seq(oneHint)
              currentTemplates = currentTemplates.filterNotPredicates(Set(head))
              currentTemplates = currentTemplates.addPredicateHints(Map(head -> currentHintsList))
              //add useful hint to PositiveHintsWithID
              for (wrappedHint <- InitialHintsWithID) {
                if (head.name.toString() == wrappedHint.head && wrappedHint.hint == oneHint.toString) {
                  PositiveHintsWithID = PositiveHintsWithID ++ Seq(wrappedHint)
                }
              }
          }

          println("Current head:" + head)
          println
          println("criticalHintsList" + criticalHintsList)
          println
          println("redundantHintsList" + redundantHintsList)
          println("---------------------------------------------------------------")
          //optimizedHints=optimizedHints.addPredicateHints(Map(oneHintKey->criticalHintsList))

        } //second for end
        if (!criticalHintsList.isEmpty) { //add critical hints in one head to optimizedHints map
          optimizedHints = optimizedHints.addPredicateHints(Map(head -> criticalHintsList))
        }
      } //first for end

      println("\n------------DEBUG-Select critical hints end-------------------------")
      println("\noriginal Hints:")
      simpHints.pretyPrintHints()
      println("\nOptimized Hints:")
      println("!@@@@")
      optimizedHints.pretyPrintHints()
      println("@@@@!")
      println("timeout:" + GlobalParameters.get.threadTimeout)
      //GlobalParameters.get.printHints=optimizedHints

      if (optimizedHints.isEmpty) {
        //writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial") //write hints and their ID to file
      } else {
        //only write to file when optimized hint is not empty
        writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial") //write hints and their ID to file
        writeHintsWithIDToFile(PositiveHintsWithID, fileName, "positive")
        writeHintsWithIDToFile(NegativeHintsWithID, fileName, "negative")
      }


      return optimizedHints

    }

  }


  def writeHintsWithIDToFile(wrappedHintList: Seq[wrappedHintWithID], fileName: String, hintType: String) {
    val distinctWrappedHintList = wrappedHintList.distinct
    val filePath=GlobalParameters.get.fileName.substring(0,GlobalParameters.get.fileName.lastIndexOf("/")+1)
    if (hintType == "initial") {
      val writer = new PrintWriter(new File(filePath + fileName + ".initialHints")) //python path
      for (wrappedHint <- wrappedHintList) {
        writer.write(wrappedHint.ID.toString + ":" + wrappedHint.head + ":" + wrappedHint.hint + "\n")
      }
      writer.close()
    }
    if (hintType == "positive") {
      val writer = new PrintWriter(new File(filePath + fileName + ".positiveHints")) //python path
      for (wrappedHint <- wrappedHintList) {
        writer.write(wrappedHint.ID.toString + ":" + wrappedHint.head + ":" + wrappedHint.hint + "\n")
      }
      writer.close()
    }
    if (hintType == "negative") {
      val writer = new PrintWriter(new File(filePath+ fileName + ".negativeHints")) //python path
      for (wrappedHint <- wrappedHintList) {
        writer.write(wrappedHint.ID.toString + ":" + wrappedHint.head + ":" + wrappedHint.hint + "\n")
      }
      writer.close()
    }

  }


  def neuralNetworkSelection(encoder: ParametricEncoder, simpHints: VerificationHints, simpClauses: Clauses): VerificationHints = {
    //write redundant hints to JSON

    //call NNs

    //read predicted hints from JSON

    //write to optimized Hints

    val optimizedHints = simpHints
    return optimizedHints
  }

  def readHintsFromJSON(fileName: String): VerificationHints = {

    //Read JSON
    import scala.io.Source
    import scala.util.parsing.json._
    val fname = "JSON/" + fileName + ".json"

    // Read the JSON file into json variable.
    var json: String = ""
    for (line <- Source.fromFile(fname).getLines) json += line

    // Get parse result Option object back from try/catch block.
    val option = try {
      JSON.parseFull(json)
    } catch {
      case ex: Exception => ex.printStackTrace()
    }

    // Print parsed JSON
    option match {
      case None => println("observations JSON invalid")
      case Some(elements: Map[String, List[String]]) => {
        //println(elements)
        for ((key, list) <- elements) {
          println(key + "/" + list.length)
          for (value <- list) {
            println(" " + value)
          }

        }


      }
    }

    //JSON to Map[IExpression.Predicate, Seq[VerifHintElement]
    //VerifHintInitPred
    //VerifHintTplPred
    //VerifHintTplEqTerm
    var optimizedHints = VerificationHints(Map())
    val head = "main1"
    val arity = 1
    val h = new IExpression.Predicate(head, arity)
    val h1 = new IExpression.Predicate("main2", 2)


    val Term = "_0,10000"
    val predicate = "_3 + -1 * _4) >= 0"
    val element = VerifHintTplEqTerm(new IConstant(new ConstantTerm("sss")), 10000)
    //    val element1=VerifHintInitPred(IFomula())
    var hintList: Seq[VerifHintElement] = Seq()
    hintList = hintList ++ Seq(element)
    hintList = hintList ++ Seq(element)


    optimizedHints = optimizedHints.addPredicateHints(Map(h -> hintList))
    optimizedHints = optimizedHints.addPredicateHints(Map(h1 -> hintList))
    println("input template:")
    optimizedHints.pretyPrintHints()


    return optimizedHints
  }

  def readHintsIDFromJSON(fileName: String, originalHints: VerificationHints): VerificationHints = {
    //    for((key,value)<-originalHints){
    //      for(v<-value){
    //      }
    //    }


    var readHints = VerificationHints(Map())

    return readHints
  }

  def storeHintsToVerificationHints_binary(parsedHintslist: Seq[Seq[String]], readInitialHintsWithID: Map[String, String], originalHints: VerificationHints) = {
    //store read hints to VerificationHints
    println("---selected hints--")
    var readHints = VerificationHints(Map())
    var readHintsTemp: Map[IExpression.Predicate, VerifHintElement] = Map()
    var readHintsTempList: Seq[Map[IExpression.Predicate, VerifHintElement]] = Seq()
    var parsedHintsCount = 0

    for (element <- parsedHintslist) {
      //println(element)
      if (element(3).toFloat.toInt == 1) { //element(3)==1 means useful, element(4) is score
        val head = element(1).toString
        //element(1) is head
        val hint = readInitialHintsWithID(element(0).toString + ":" + element(1)).toString //InitialHintsWithID ID:head->hint
        for ((key, value) <- originalHints.getPredicateHints()) {
          val keyTemp = key.toString().substring(0, key.toString().indexOf("/"))
          if (head == keyTemp) {
            var usfulHintsList: Seq[VerifHintElement] = Seq()
            for (oneHint <- originalHints.getValue(key)) {
              if (keyTemp == head && oneHint.toString() == hint) { //match initial hints and hints from file to tell usefulness
                usfulHintsList = usfulHintsList ++ Seq(oneHint) //add this hint to usfulHintsList
                //println(element(0),usfulHintsList)
                readHintsTempList = readHintsTempList :+ Map(key -> oneHint)
                parsedHintsCount = parsedHintsCount + 1
              }
            }
            //readHints=readHints.addPredicateHints(Map(key->usfulHintsList)) //add this haed->hint:Seq() to readHints
          }
        }
      } else {} //useless hint

    }

    println("selected hint count=" + parsedHintsCount)
    (readHints, readHintsTempList)

  }

  def storeHintsToVerificationHints_score(parsedHintslist: Seq[Seq[String]], readInitialHintsWithID: Map[String, String], originalHints: VerificationHints, rankTreshold: Float) = {
    //store read hints to VerificationHints
    println("---selected hints--")
    var readHints = VerificationHints(Map())
    var readHintsTemp: Map[IExpression.Predicate, VerifHintElement] = Map()
    var readHintsTempList: Seq[Map[IExpression.Predicate, VerifHintElement]] = Seq()
    var parsedHintsCount = 0

    for (element <- parsedHintslist) {
      //println(element)
      if (element(4).toFloat > rankTreshold) { //element(3)==1 means useful, element(4) is score
        val head = element(1).toString
        //element(1) is head
        val hint = readInitialHintsWithID(element(0).toString + ":" + element(1)).toString //InitialHintsWithID ID:head->hint
        for ((key, value) <- originalHints.getPredicateHints()) {
          val keyTemp = key.toString().substring(0, key.toString().indexOf("/"))
          if (head == keyTemp) {
            var usfulHintsList: Seq[VerifHintElement] = Seq()
            for (oneHint <- value) {
              if (keyTemp == head && oneHint.toString() == hint) { //match initial hints and hints from file to tell usefulness
                usfulHintsList = usfulHintsList ++ Seq(oneHint) //add this hint to usfulHintsList
                //println(element(0),usfulHintsList)
                readHintsTempList = readHintsTempList :+ Map(key -> oneHint)
                parsedHintsCount = parsedHintsCount + 1
              }
            }
            //readHints=readHints.addPredicateHints(Map(key->usfulHintsList)) //add this haed->hint:Seq() to readHints
          }
        }
      } else {} //useless hint

    }

    println("selected hint count=" + parsedHintsCount)
    (readHints, readHintsTempList)

  }

  def storeHintsToVerificationHints_topN(parsedHintslist: Seq[Seq[String]], readInitialHintsWithID: Map[String, String], originalHints: VerificationHints, N: Int) = {
    //store read hints to VerificationHints
    println("---selected hints--")
    var readHints = VerificationHints(Map())
    var readHintsTemp: Map[IExpression.Predicate, VerifHintElement] = Map()
    var readHintsTempList: Seq[Map[IExpression.Predicate, VerifHintElement]] = Seq()
    var parsedHintsCount = 0
    for (element <- parsedHintslist.take(N)) {
      //take first N element
      //println(element)
      val head = element(1).toString
      //element(1) is head
      val hint = readInitialHintsWithID(element(0).toString + ":" + element(1)).toString //InitialHintsWithID ID:head->hint
      for ((key, value) <- originalHints.getPredicateHints()) {
        val keyTemp = key.toString().substring(0, key.toString().indexOf("/"))
        if (head == keyTemp) {
          var usfulHintsList: Seq[VerifHintElement] = Seq()
          for (oneHint <- value) {
            if (oneHint.toString() == hint) { //match initial hints and hints from file to tell usefulness
              usfulHintsList = usfulHintsList ++ Seq(oneHint) //add this hint to usfulHintsList
              //println(element(0),usfulHintsList)
              readHintsTempList = readHintsTempList :+ Map(key -> oneHint)
              parsedHintsCount = parsedHintsCount + 1
            }
          }
          //readHints=readHints.addPredicateHints(Map(key->usfulHintsList)) //add this haed->hint:Seq() to readHints
        }
      }


    }

    println("selected hint count=" + parsedHintsCount)
    (readHints, readHintsTempList)

  }

  def readHintsIDFromFile(fileName: String, originalHints: VerificationHints, rank: String = ""): VerificationHints = {
    var parsedHintslist = Seq[Seq[String]]() //store parsed hints
    val f = fileName + ".optimizedHints" //python file
    for (line <- Source.fromFile(f).getLines) {
      var parsedHints = Seq[String]() //store parsed hints
      //parse read file
      var lineTemp = line.toString
      val ID = lineTemp.substring(0, lineTemp.indexOf(":"))
      lineTemp = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length)
      val head = lineTemp.substring(0, lineTemp.indexOf(":"))
      lineTemp = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length)
      val hint = lineTemp.substring(0, lineTemp.indexOf(":"))
      lineTemp = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length)
      val usefulness = lineTemp.substring(0, lineTemp.indexOf(":")) //1=useful,0=useless
      val score = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length) //1=useful,0=useless
      parsedHints = parsedHints :+ ID :+ head :+ hint :+ usefulness :+ score //ID,head,hint,usefulness,score
      //println(parsedHints)
      parsedHintslist = parsedHintslist :+ parsedHints
    }
    println("parsed hints count=" + parsedHintslist.size)

    println("---readInitialHints-----")
    var readInitialHintsWithID: Map[String, String] = Map()
    //val fInitial = "predictedHints/"+fileNameShorter+".initialHints" //read file
    val fInitial =  fileName + ".initialHints" //python file
    for (line <- Source.fromFile(fInitial).getLines) {
      var parsedHints = Seq[String]() //store parsed hints
      //parse read file
      var lineTemp = line.toString
      val ID = lineTemp.substring(0, lineTemp.indexOf(":"))
      lineTemp = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length)
      val head = lineTemp.substring(0, lineTemp.indexOf(":"))
      lineTemp = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length)
      val hint = lineTemp
      readInitialHintsWithID = readInitialHintsWithID + (ID + ":" + head -> hint)
    }
    for ((key, value) <- readInitialHintsWithID) { //print initial hints
      println(key, value)
    }
    println("readInitialHints count=" + readInitialHintsWithID.size)

    //store read hints to VerificationHints
    var readHints = VerificationHints(Map())
    var readHintsTempList: Seq[Map[IExpression.Predicate, VerifHintElement]] = Seq()
    if (rank.isEmpty) { //read rank option, no need for rank
      val (readHints_temp, readHintsTempList_temp) = storeHintsToVerificationHints_binary(parsedHintslist, readInitialHintsWithID, originalHints)
      readHints = readHints_temp
      readHintsTempList = readHintsTempList_temp
    } else { //need rank
      //parse rank information
      var lineTemp = rank.toString
      val rankThreshold = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length).toFloat

      if (rankThreshold > 1) {
        //rank by top n
        println("use top " + rankThreshold.toInt + " hints")
        val (readHints_temp, readHintsTempList_temp) = storeHintsToVerificationHints_topN(parsedHintslist, readInitialHintsWithID, originalHints, rankThreshold.toInt)
        readHints = readHints_temp
        readHintsTempList = readHintsTempList_temp
      }
      if (rankThreshold < 1) {
        //rank by score
        println("use score threshold " + rankThreshold)
        val (readHints_temp, readHintsTempList_temp) = storeHintsToVerificationHints_score(parsedHintslist, readInitialHintsWithID, originalHints, rankThreshold)
        readHints = readHints_temp
        readHintsTempList = readHintsTempList_temp
      }

    }

    //store heads to set
    var heads: Set[IExpression.Predicate] = Set()
    for (value <- readHintsTempList) {
      println(value)
      val tempValue = value.toSeq
      //tempValue.to
      heads = heads + tempValue(0)._1
    }


    for (head <- heads) {
      var hintList: Seq[VerifHintElement] = Seq()
      for (value <- readHintsTempList) {
        //value=Map(head->hint)
        val tempValue = value.toSeq
        if (tempValue(0)._1 == head) {
          //println(hintList)
          hintList = hintList :+ tempValue(0)._2
        }
      }
      readHints = readHints.addPredicateHints(Map(head -> hintList))
    }

    println("----readHints-----")
    for ((key, value) <- readHints.getPredicateHints()) {
      println(key)
      for (v <- value) {
        println(v)
      }
    }

    return readHints
  }


  def initialIDForHints(simpHints: VerificationHints): Seq[wrappedHintWithID] = {
    //var HintsIDMap=Map("initialKey"->"")
    var wrappedHintsList: Seq[wrappedHintWithID] = Seq()
    var HintsIDMap: Map[String, String] = Map()
    var counter = 0

    for ((head) <- simpHints.getPredicateHints().keys.toList) { //loop for head
      for (oneHint <- simpHints.getValue(head)) { //loop for every template in the head
        HintsIDMap ++= Map(counter.toString + ":" + head.name.toString() -> oneHint.toString) //map(ID:head->hint)
        counter = counter + 1
        val oneWrappedHint = new wrappedHintWithID(counter, head.name.toString, oneHint.toString)
        wrappedHintsList = wrappedHintsList ++ Seq(oneWrappedHint)
      }
    }
    //HintsIDMap=HintsIDMap-"initialKey"

    return wrappedHintsList

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

  def moveRenameFile(source: String, destination: String): Unit = {
    val path = Files.copy(
      Paths.get(source),
      Paths.get(destination),
      StandardCopyOption.REPLACE_EXISTING
    )
    // could return `path`
  }
  def getArgumentInfo(argumentList:List[(IExpression.Predicate,Int)]):ListBuffer[argumentInfo]= {
    var argID=0
    var arguments:ListBuffer[argumentInfo]=ListBuffer[argumentInfo]()
    for((arg,i)<-argumentList.zipWithIndex){
      for((a,j) <- (0 to arg._2-1).zipWithIndex){
        arguments+=new argumentInfo(argID,arg._1,a)
        argID=argID+1
      }
    }
    arguments
  }

  def getArgumentInfoFromFile(argumentList:List[(IExpression.Predicate,Int)]):ListBuffer[argumentInfo]= {
    val arguments=getArgumentInfo(argumentList)
    val argumentFileName=GlobalParameters.get.fileName+".arguments"
    if(scala.reflect.io.File(argumentFileName).exists){
      //read score from .argument file
      for (arg<-arguments;line <- Source.fromFile(argumentFileName).getLines){
        val parsedLine=line.split(":")
        if(arg.head==parsedLine(1) && ("argument"+arg.index.toString)==parsedLine(2))
          arg.score=parsedLine(3).toInt
      }
    }

    arguments
  }
  def getArgumentBound(argumentList:List[(IExpression.Predicate,Int)],argumentBounds: scala.collection.mutable.Map[Predicate, List[(String, String)]]): ListBuffer[argumentInfo]  ={
    val arguments=getArgumentInfo(argumentList)
    for ((k,v) <-argumentBounds;arg<-arguments)if(arg.location.toString()==k.toString()){
      println(arg.location,k)
        arg.bound=v(arg.index)
    }
    arguments
  }
  def writeArgumentScoreToFile(file:String,
                               argumentList:List[(IExpression.Predicate,Int)],
                               positiveHints:VerificationHints,
                               countOccurrence:Boolean=true): ListBuffer[argumentInfo] ={
    println("Write arguments to file")
    val fileName = file.substring(file.lastIndexOf("/") + 1)
    val arguments=getArgumentInfoFromFile(argumentList)
    val writer = new PrintWriter(new File(file + ".arguments")) //python path

    if (countOccurrence==true){
      //get hint info list
      var positiveHintInfoList:ListBuffer[hintInfo]=ListBuffer[hintInfo]()
      for((head,hintList)<-positiveHints.getPredicateHints()){
        for(h<-hintList) h match{
          case VerifHintInitPred(p) => {positiveHintInfoList+=new hintInfo(p,"VerifHintInitPred",head)}
          case VerifHintTplPred(p,_) => {positiveHintInfoList+=new hintInfo(p,"VerifHintTplPred",head)}
          case VerifHintTplPredPosNeg(p,_) => {positiveHintInfoList+=new hintInfo(p,"VerifHintTplPredPosNeg",head)}
          case VerifHintTplEqTerm(t,_) => {positiveHintInfoList+=new hintInfo(t,"VerifHintTplEqTerm",head)}
          case VerifHintTplInEqTerm(t,_) => {positiveHintInfoList+= new hintInfo(t,"VerifHintTplInEqTerm",head)}
          case VerifHintTplInEqTermPosNeg(t,_) => {positiveHintInfoList+=new hintInfo(t,"VerifHintTplInEqTermPosNeg",head)}
          case _=>{}
        }
      }

      //go through all predicates and arguments count occurrence
      for(arg<-arguments){
        for(hint<-positiveHintInfoList){
          if(arg.location.equals(hint.head))
            if(ContainsSymbol(hint.expression, IVariable(arg.index)))
              arg.score=arg.score+1
        }
      }

    }
    //normalize score
    //write arguments with score to file
    for(arg<-arguments){
      writer.write(arg.ID+":"+arg.location.toString()+":"+"argument"+arg.index+":"+arg.score+"\n")
    }
    writer.close()
//    val argumentIDList=for(arg<-arguments) yield arg.ID
//    val argumentNameList=for(arg<-arguments) yield arg.location.toString()+":"+"argument"+arg.index
//    val argumentOccurrence=for(arg<-arguments) yield arg.score
  (arguments)
  }
}
class hintInfo(e:IExpression,t:String,h:IExpression.Predicate){
  val head=h
  val expression=e
  val hintType=t
}
class argumentInfo(id:Int,loc: IExpression.Predicate,ind:Int)
{
  val ID=id
  val location=loc
  val index=ind
  var score=0
  val head=location.toString()
  val headName=location.name
  var bound:Pair[String,String] = ("","")
}

class simplifiedHornPredAbsForArgumentBounds[CC <% HornClauses.ConstraintClause](iClauses: Iterable[CC],
                                                                                 initialPredicates: Map[Predicate, Seq[IFormula]],
                                                                                 predicateGenerator: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
                                                                                   Either[Seq[(Predicate, Seq[Conjunction])],
                                                                                     Dag[(IAtom, HornPredAbs.NormClause)]], counterexampleMethod: HornPredAbs.CounterexampleMethod.Value = HornPredAbs.CounterexampleMethod.FirstBestShortest)  {
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
        new IntervalPropagator (rawNormClauses.keys.toIndexedSeq,
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
  var argumentBounds: scala.collection.mutable.Map[Predicate, List[Pair[String, String]]] = scala.collection.mutable.Map()
  for ((rs, bounds) <- relationSymbolBounds; if (rs.pred.name != "FALSE")) { //don't learn from FALSE predicate
    //println(rs.pred.name + ":")
    var argumentBoundList: List[Pair[String, String]] = List()
    if (bounds.isTrue) { //FALSE's bounds is true
      for (s <- rs.arguments(0))
        argumentBoundList :+= Pair("\"None\"", "\"None\"")
    } else if (bounds.isFalse) {
      for (s <- rs.arguments(0))
        argumentBoundList :+= Pair("\"False\"", "\"False\"")
    } else {
      for (s <- rs.arguments(0)) {
        //print("  " + s + ": ")
        val lc = ap.terfor.linearcombination.LinearCombination(s, bounds.order)
        var lowerBound: String = ""
        var upperBound: String = ""
        PresburgerTools.lowerBound(lc, bounds) match {
          case Some(x) => lowerBound = x.toString()
          case _ => lowerBound = "\"None\""
        }
        //print(", ")
        (for (b <- PresburgerTools.lowerBound(-lc, bounds)) yield -b) match {
          case Some(x) => upperBound = x.toString()
          case _ => upperBound = "\"None\""
        }
        argumentBoundList :+= Pair(lowerBound, upperBound)
        //println()
      }
    }
    argumentBounds(rs.pred) = argumentBoundList
  }
}