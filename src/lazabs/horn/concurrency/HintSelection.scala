package lazabs.horn.concurrency

import ap.terfor.preds.Predicate
import ap.terfor._
import ap.parser.{IExpression, _}
import lazabs.GlobalParameters
import lazabs.horn.abstractions.{AbstractionRecord, LoopDetector, StaticAbstractionBuilder, VerificationHints}
import lazabs.horn.bottomup._
import lazabs.horn.concurrency.ParametricEncoder.{Infinite, Singleton}

import scala.collection.immutable.ListMap
import scala.io.Source
import scala.collection.mutable.{ArrayBuffer, LinkedHashSet, ListBuffer, Seq, HashMap => MHashMap, HashSet => MHashSet}
import java.io.{File, FileWriter, PrintWriter}
import java.lang.System.currentTimeMillis

import ap.parser._
import ap.terfor.conjunctions.Conjunction
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, _}
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.preprocessor.HornPreprocessor.Clauses
import java.nio.file.{Files, Paths, StandardCopyOption}

import lazabs.horn.bottomup.HornPredAbs.RelationSymbolPred
import lazabs.horn.global.HornClause
import lazabs.horn.preprocessor.HornPreprocessor
import lazabs.viewer.HornPrinter
import ap.parser._
import IExpression._

import scala.collection.{Set => GSet}
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.global._

import scala.concurrent.duration._
import scala.concurrent.{Await, Future}
import scala.util.control.Breaks._
import scala.concurrent.ExecutionContext.Implicits.global
import java.lang.System.currentTimeMillis

import ap.basetypes.IdealInt
import lazabs.Main
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.concurrency.GraphTranslator

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

  def writeHornAndGraphToFiles(selectedHints: VerificationHints,
                               sortedHints: VerificationHints,
                               clauses: HornPreprocessor.Clauses,
                               clauseSet: Seq[HornClause], wrappedHintList: Seq[wrappedHintWithID]) = {
    if (selectedHints.isEmpty) { //when no hint available
      println("No hints selected (no need for hints)")
      //not write horn clauses to file
    } else {

      //Output graphs
      //val hornGraph = new GraphTranslator(clauses, GlobalParameters.get.fileName)
      writeHornClausesGraphToFile(GlobalParameters.get.fileName,clauses)
      val hintGraph = new GraphTranslator_hint(clauses, GlobalParameters.get.fileName, sortedHints, wrappedHintList)

      //write horn clauses to file
      val fileName = GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/") + 1)
      val writer = new PrintWriter(new File("../trainData/" + fileName + ".horn")) //python path
      writer.write(HornPrinter(clauseSet))
      writer.close()
      //HintsSelection.writeHornClausesToFile(system,GlobalParameters.get.fileName)
      //write smt2 format to file
      if (GlobalParameters.get.fileName.endsWith(".c")) { //if it is a c file
        HintsSelection.writeSMTFormatToFile(clauses, "../trainData/") //write smt2 format to file
      }
      if (GlobalParameters.get.fileName.endsWith(".smt2")) { //if it is a smt2 file
        //copy smt2 file
        val fileName = GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/") + 1)
        HintsSelection.moveRenameFile(GlobalParameters.get.fileName, "../trainData/" + fileName)
      }


    }
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
          val simplifiedPredicate = (new Simplifier) (Internal2InputAbsy(p.rawPred, p.rs.sf.functionEnc.predTranslation))
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

      } else {
        //only write to file when optimized hint is not empty
        writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial") //write hints and their ID to file
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
    if (hintType == "initial") {
      //val writer = new PrintWriter(new File("trainData/"+fileName+".initialHints"))
      val writer = new PrintWriter(new File("../trainData/" + fileName + ".initialHints")) //python path
      for (wrappedHint <- wrappedHintList) {
        writer.write(wrappedHint.ID.toString + ":" + wrappedHint.head + ":" + wrappedHint.hint + "\n")
      }
      writer.close()
    }
    if (hintType == "positive") {
      //val writer = new PrintWriter(new File("trainData/"+fileName+".positiveHints"))
      val writer = new PrintWriter(new File("../trainData/" + fileName + ".positiveHints")) //python path
      for (wrappedHint <- wrappedHintList) {
        writer.write(wrappedHint.ID.toString + ":" + wrappedHint.head + ":" + wrappedHint.hint + "\n")
      }
      writer.close()
    }
    if (hintType == "negative") {
      //val writer = new PrintWriter(new File("trainData/"+fileName+".negativeHints"))
      val writer = new PrintWriter(new File("../trainData/" + fileName + ".negativeHints")) //python path
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
    val fileNameShorter = fileName.substring(fileName.lastIndexOf("/"), fileName.length) //get file name
    var parsedHintslist = Seq[Seq[String]]() //store parsed hints

    //val f = "predictedHints/"+fileNameShorter+".optimizedHints" //read file
    val f = "../predictedHints/" + fileNameShorter + ".optimizedHints" //python file
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
    val fInitial = "../predictedHints/" + fileNameShorter + ".initialHints" //python file
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
    val fileName = file.substring(file.lastIndexOf("/") + 1)
    //val writer = new PrintWriter(new File("trainData/"+fileName+".horn"))
    val writer = new PrintWriter(new File("../trainData/" + fileName + ".horn")) //python path
    for (clause <- simpClauses) {
      writer.write(clause.toPrologString + "\n")
    }
    writer.close()

  }

  //import lazabs.horn.preprocessor.HornPreprocessor.Clauses
  def writeHornClausesGraphToFile(file: String, simpClauses: Clauses): Unit = {
    println("Write horn to file")
    var edgeNameMap: Map[String, String] = Map()
    edgeNameMap += ("controlFlowIn" -> "control flow in")
    edgeNameMap += ("controlFlowOut" -> "control flow out")
    edgeNameMap += ("dataFlowIn" -> "data flow in")
    edgeNameMap += ("dataFlowOut" -> "data flow out")
    edgeNameMap += ("argument" -> "argument")
    edgeNameMap += ("dataFlowIn" -> "data flow in")
    edgeNameMap += ("dataFlowOut" -> "data flow out")
    edgeNameMap += ("astAnd" -> "AST &")
    edgeNameMap += ("condition" -> "condition")
    edgeNameMap += ("constantDataFlow" -> "constant data flow")
    edgeNameMap += ("dataFlow" -> "data flow")

    //turn on/off edge's label
    var edgeNameSwitch = false
    if (edgeNameSwitch == false) {
      for (key <- edgeNameMap.keys) {
        edgeNameMap += (key -> "")
        //edgeNameMap updated (key, " ")
      }
    }
    //println(file.substring(file.lastIndexOf("/")+1))
    val fileName = file.substring(file.lastIndexOf("/") + 1)
    //val writer = new PrintWriter(new File("trainData/"+fileName+".horn"))
    val writer = new PrintWriter(new File("../trainData/" + fileName + ".HornGraph")) //python path

    //write dataflow

    import IExpression._

    var controlFLowNodeList = ListBuffer[ControlFlowNode]()
    var clauseList = ListBuffer[ClauseTransitionInformation]()
    var clauseID = 0

    for (clause <- simpClauses) {
      writer.write("-------------" + "\n")
      writer.write(clause.toPrologString + "\n")

      //args in head
      var argsInHead = ListBuffer[Pair[String,ITerm]]()
      if (!clause.head.args.isEmpty) {
        for (arg <- clause.head.args) {
          argsInHead += Pair(arg.toString,arg)
        }
      }

      //args in body
      var argsInBody = ListBuffer[Pair[String,ITerm]]()
      if (!clause.body.isEmpty) {
        for (arg <- clause.body.head.args) {
          argsInBody += Pair(arg.toString,arg)
        }
      }



      //store head and body to controlFLowNodeList data structure
      var bodyName = "Initial"
      var currentControlFlowNodeArgumentListBody = new ListBuffer[ArgumentNode]()
      if (!clause.body.isEmpty) {
        bodyName = clause.body.head.pred.name
        for ((arg, index) <- clause.body.head.args.zipWithIndex) {
          currentControlFlowNodeArgumentListBody += new ArgumentNode(clause.head.pred.name,
            clause.body.head.pred.name, clause.body.head.pred.name, clauseID, arg, index)
        }
      }

      val currentControlFlowNodeBody = new ControlFlowNode(bodyName, currentControlFlowNodeArgumentListBody)
      if (!controlFLowNodeList.exists(_.name == bodyName)) { //if body is not in controlFLowNodeList
        controlFLowNodeList += currentControlFlowNodeBody
      }

      var currentControlFlowNodeArgumentListHead = new ListBuffer[ArgumentNode]()
      if (!clause.head.args.isEmpty) {
        for ((arg, index) <- clause.head.args.zipWithIndex) {
          currentControlFlowNodeArgumentListHead += new ArgumentNode(clause.head.pred.name,
            bodyName, clause.head.pred.name, clauseID, arg, index)
          //ArgumentNode(headName:String,bodyName:String,location:String,clauseID:Int,arg:String,argIndex:Int)
        }
      }
      val currentControlFlowNodeHead = new ControlFlowNode(clause.head.pred.name, currentControlFlowNodeArgumentListHead)
      if (!controlFLowNodeList.exists(_.name == clause.head.pred.name)) { //if head is not in controlFLowNodeList
        controlFLowNodeList += currentControlFlowNodeHead
      }

      val currentClause = new ClauseTransitionInformation(currentControlFlowNodeHead, currentControlFlowNodeBody, clauseID)
      clauseID = clauseID + 1

      //add head argument to node list
      for(arg<-currentClause.head.argumentList if !currentClause.head.argumentList.isEmpty){
        if(!currentClause.nodeList.exists(x=>x._1==arg.name)){
          currentClause.nodeList+=Pair(arg.name,arg.originalContent)
        }
      }
      //add body argument to node list
      for(arg<-currentClause.body.argumentList if !currentClause.body.argumentList.isEmpty){
        if(!currentClause.nodeList.exists(x=>x._1==arg.name)){
          currentClause.nodeList+=Pair(arg.name,arg.originalContent)
        }
      }


      writer.write("Head arguments: " + argsInHead.toString() + "\n")
      writer.write("Body arguments: " + argsInBody.toString() + "\n")
      val commonArg = argsInHead.filter(arg => argsInBody.contains(arg))
      currentClause.commonArg=commonArg
      //val x =argsInHead.toList.filterNot(arg=>argsInBody.toString().contains(arg.toString))
      writer.write("Common Arguments:" + commonArg.toString() + "\n")


      //head argument -common argument
      val relativeComplimentOfHeadArg = argsInHead.filterNot(arg => commonArg.contains(arg))
      // store relativeComplimentOfHeadArg to clause
      currentClause.relativeComplimentOfHeadArg=relativeComplimentOfHeadArg
      writer.write("relativeComplimentOfHeadArg:" + relativeComplimentOfHeadArg.toString() + "\n")


      //separate guard and data flow conjunct
      //if the expression is not a equation, then it is a guard
      //if the expression is a equation and head's argument -common argument not in the formula,then it is a guard
      //if the expression is a equation and there are element in the head's argument - common argument set, then it is a data flow
      var guardConjunct=ListBuffer[IFormula]()
      var dataFlowConjunct=ListBuffer[IFormula]()
      for (conjunct <- LineariseVisitor(
        clause.constraint, IBinJunctor.And)) conjunct match {
        case Eq(t1,t2)=>{
          if (!relativeComplimentOfHeadArg.exists(a => ContainsSymbol.apply(conjunct,a._2))) { //if the conjunct has no head arguments -common argument set
            guardConjunct+=conjunct
          }else{// if the equation has one or more head argument -common argument elements
            dataFlowConjunct+=conjunct
          }
        }
        case _=>{guardConjunct+=conjunct} //not a equation
      }


      def getElementsFromIFomula(e: IExpression, elementList: ListBuffer[String]): Unit = {

        e match {
          case IAtom(pred, args) => {
            elementList += pred.toString();
            for (a <- args if !args.isEmpty) {
              getElementsFromIFomula(a, elementList);
            }
          }
          case IBinFormula(j, f1, f2) => {
            getElementsFromIFomula(f1, elementList)
            getElementsFromIFomula(f2, elementList)
          }
          case IBoolLit(v) => {
            elementList += v.toString();
          }
          case IFormulaITE(cond, left, right) => {
            getElementsFromIFomula(cond, elementList)
            getElementsFromIFomula(left, elementList)
            getElementsFromIFomula(right, elementList)
          }
          case IIntFormula(rel, term) => {
            //elementList+=rel.toString();
            getElementsFromIFomula(term, elementList)
          }
          case INamedPart(pname, subformula) => {
            elementList += pname.toString;
            getElementsFromIFomula(subformula, elementList)
          }
          case INot(subformula) => {
            getElementsFromIFomula(subformula, elementList)
          }
          case IQuantified(quan, subformula) => {
            getElementsFromIFomula(subformula, elementList)
          }
          case ITrigger(patterns, subformula) => {
            for (p <- patterns if !patterns.isEmpty) {
              getElementsFromIFomula(p, elementList);
            }
            getElementsFromIFomula(subformula, elementList)
          }
          case IConstant(c) => {
            elementList += c.toString();
          }
          case IEpsilon(cond) => {
            getElementsFromIFomula(cond, elementList)
          }
          case IFunApp(fun, args) => {
            elementList += fun.toString();
            for (a <- args if !args.isEmpty) {
              getElementsFromIFomula(a, elementList);
            }
          }
          case IIntLit(v) => {
            elementList += v.toString();
          }
          case IPlus(t1, t2) => {
            getElementsFromIFomula(t1, elementList);
            getElementsFromIFomula(t2, elementList);
          }
          case ITermITE(cond, left, right) => {
            getElementsFromIFomula(cond, elementList);
            getElementsFromIFomula(left, elementList);
            getElementsFromIFomula(right, elementList);
          }
          case ITimes(coeff, subterm) => {
            elementList += coeff.toString();
            getElementsFromIFomula(subterm, elementList);
          }
          case IVariable(index) => {
            elementList += index.toString();
          }
          case _ => {}
        }
        //IFormula:IAtom, IBinFormula, IBoolLit, IFormulaITE, IIntFormula, INamedPart, INot, IQuantified, ITrigger
        //ITerm:IConstant, IEpsilon, IFunApp, IIntLit, IPlus, ITermITE, ITimes, IVariable
      }
      //extract all variable from guard
      var elementsInGuard=ListBuffer[String]()
      for(conjunct<-guardConjunct){
        getElementsFromIFomula(conjunct,elementsInGuard)
      }
      elementsInGuard=elementsInGuard.distinct //delete reapeatative element
      for(e<-elementsInGuard){ //delete integers
        try {
          e.toInt
          elementsInGuard-=e
        } catch {
          case e: Exception => {}
        }
      }
      writer.write("variables in guard: " + elementsInGuard.toString() + "\n")
      //todo:identify free variable
//      var freeVariables=ListBuffer[String]()
//      for(e<-elementsInGuard;headArg<-currentClause.head.argumentList if e==headArg.originalContent){
//        freeVariables+=e
//      }
//      writer.write("free variables: " + freeVariables.toString() + "\n")



      //preprocessing: parse conjuncts onece to replace guard or data flow with new guard and data flow
      def replaceArgument(args:ListBuffer[Pair[String,ITerm]],targetConjunct:IFormula,
                          guardConjunct:ListBuffer[IFormula],daraFlowConjunct:ListBuffer[IFormula],flowType:String) ={
        var tempGuardConjunct=for (gc<-guardConjunct) yield gc
        var tempDataFlowConjunct=for (gc<-daraFlowConjunct) yield gc
        var modifiedConjunct=targetConjunct
        val sp=new Simplifier()
        for((arg,argITerm)<-args if !args.isEmpty){
          if(ContainsSymbol(targetConjunct,argITerm)){
            println("targetConjunct:"+targetConjunct)
            println("args:"+args)
            var oldArg=new ConstantTerm("_")
            argITerm match{
              case IConstant(c)=>{
                println("IConstant:"+argITerm)
                oldArg=c
              }
              case _=>{}
            }
            val newArg=new IConstant(new ConstantTerm(("_"+arg)))
            modifiedConjunct= sp(SimplifyingConstantSubstVisitor(modifiedConjunct,Map(oldArg->newArg)))  //replace arg to _arg
            println("arg:"+arg)
            println("modifiedConjunct:"+modifiedConjunct)
            if(!tempDataFlowConjunct.iterator.exists(p=>p.toString==sp(Eq(argITerm,newArg)).toString)){
              tempDataFlowConjunct+=sp(Eq(argITerm,newArg))
            }
            println("new data flow conjunct:"+sp(Eq(argITerm,newArg)))
            //val Eq(a,b) = sp(Eq(argITerm,newArg))
          }
        }
        if(flowType=="guard"){
          tempGuardConjunct-=targetConjunct
          tempGuardConjunct+=modifiedConjunct //update guard
          //tempDataFlowConjunct+=sp(Eq(argITerm,newArg))
          //println("new data flow conjunct:"+sp(Eq(argITerm,newArg)))
        }else{
          tempGuardConjunct+=modifiedConjunct
          tempDataFlowConjunct-=targetConjunct
          //tempDataFlowConjunct+=sp(Eq(argITerm,newArg))
        }
        (tempGuardConjunct,tempDataFlowConjunct)
      }

      //preprocessing:if guard has headArgument-BodyArgument elements, replace element in the conjunct, add data flow
      for(gc<-guardConjunct){
        val (guardConjunctTemp,dataFlowConjunctTemp)=replaceArgument(currentClause.relativeComplimentOfHeadArg,
          gc,guardConjunct,dataFlowConjunct,"guard")
        guardConjunct=guardConjunctTemp
        dataFlowConjunct=dataFlowConjunctTemp
      }

      //preprocessing:if data flow has more than one head elements, replace element in conjunct to be a guard, add data flow
      writer.write("Data flow:\n")
      var dataFlowMap = Map[String, IExpression]() //argument->dataflow
      for (conjunct <- dataFlowConjunct) conjunct match {
        case Eq(lhs,rhs)=>{
          var dataFlowInfo=new EqConjunctInfo(conjunct,lhs,rhs,currentClause.relativeComplimentOfHeadArg)
          if(dataFlowInfo.moreThanOneHeadElement()){

            val (guardConjunctTemp,dataFlowConjunctTemp)=replaceArgument(currentClause.relativeComplimentOfHeadArg,
              conjunct,guardConjunct,dataFlowConjunct,"dataFlow")
            guardConjunct=guardConjunctTemp
            dataFlowConjunct=dataFlowConjunctTemp

            //writer.write("debug:"+lhs + "<-" + rhs+ "\n")
          }
        }
        case _=>{}
      }
//      //After preprocessing, the left dataflow conjuncts only has one head argument
//      for(conjunct<-dataFlowConjunct){
//        //val Eq(a,b)=conjunct
//        //writer.write(a+"="+b + "\n")
//        PrincessLineariser.printExpression(conjunct)
//      }

      // parse preprocessed data flow (move head to lhs and store it in dataFlowMap)
      for (headArg <- currentClause.relativeComplimentOfHeadArg) {
        //val Iconstant = IConstant(constant)
        val SumExtract = SymbolSum(headArg._2)
        for (conjunct <- dataFlowConjunct) conjunct match {
          case Eq(SumExtract(IdealInt.ONE | IdealInt.MINUS_ONE,
          otherTerms),
          rhs) => {
            if (!relativeComplimentOfHeadArg.exists(arg => rhs.toString.concat(otherTerms.toString).contains(arg))) {
              writer.write(headArg._2 + "<-" + (rhs --- otherTerms).toString + "\n")
              // eq: c = rhs - otherTerms
              val df = rhs --- otherTerms //record data flow IExpression
              dataFlowMap = dataFlowMap ++ Map(currentClause.head.getArgNameByContent(headArg._1) -> df)
            }
            //writer.write(headArg+"="+rhs+"-"+otherTerms+"\n")// eq: c = rhs - otherTerms
          }
          // data flow: rhs - otherTerms -> c
          case Eq(lhs,
          SumExtract(IdealInt.ONE | IdealInt.MINUS_ONE,
          otherTerms)) => {
            if (!relativeComplimentOfHeadArg.exists(arg => lhs.toString.contains(arg))) {
              writer.write(headArg._2 + "<-" + (lhs --- otherTerms).toString + "\n")
              // eq: c = rhs - otherTerms
              val df = lhs --- otherTerms
              //val sp=new ap.parser.Simplifier
              //sp.apply(lhs)
              dataFlowMap = dataFlowMap ++ Map(currentClause.head.getArgNameByContent(headArg._1) -> df)
            }
            //writer.write(headArg+"="+lhs+"-"+otherTerms+"\n")// data flow: lhs - otherTerms -> c
          }
          //          case EqLit(lhs,rhs)=>{writer.write(conjunct.getClass.getName+":"+conjunct+"\n")}
          //          case GeqZ(lhs)=>{writer.write(conjunct.getClass.getName+":"+conjunct+"\n")}
          //          case Geq(lhs,rhs)=>{writer.write(conjunct.getClass.getName+":"+conjunct+"\n")}
          case _ => {} //writer.write(conjunct.getClass.getName+":"+conjunct+"\n")
        }

      }

      var dataFlowList = ListBuffer[IExpression]()
      for ((arg, df) <- dataFlowMap) {
        dataFlowList += df
      }
      var dataFlowElementList = ListBuffer[String]() //get elements from data flow formula
      for (dataFlow <- dataFlowList) { //get dataflow's element list
        getElementsFromIFomula(dataFlow, dataFlowElementList)
      }

      //parse normal dataflow
      val (dataFLowAST,dataFlowNodeHashMap) = drawAST(currentClause, "dataFlow", dataFlowMap,MHashMap.empty[String,ITerm])
      currentClause.dataFlowASTGraph=dataFLowAST
      //draw simple data flow
      for (comArg <- commonArg) {
        if (!dataFlowElementList.contains(comArg._1)) {
          writer.write(comArg._1 + "<-" + comArg._1 + "\n")

          for (bodyArg <- currentClause.body.argumentList; headArg <- currentClause.head.argumentList
               if headArg.originalContent == comArg._1 && bodyArg.originalContent == comArg._1) {
            currentClause.simpleDataFlowConnection = currentClause.simpleDataFlowConnection ++
              Map(headArg.dataFLowHyperEdge.name ->
                (bodyArg.name + " -> " + headArg.dataFLowHyperEdge.name +
                  "[label=\"" + edgeNameMap("dataFlowIn") + "\"]" + "\n"))
            //                  + //data flow hyper edge already been drew when create this hyperedge
            //                  headArg.dataFLowHyperEdge.name + " -> " + headArg.name +
            //                  "[label=\""+edgeNameMap("dataFlowOut")+"\"]"+"\n"))
          }
        }
      }

      //draw constant data flow
      //if arguments in head are constant, add data flow constant ->arguments
      //head constan dataflow
      if (!argsInHead.isEmpty) {
        for ((arg, i) <- argsInHead.zipWithIndex) {
          try {
            arg._1.toInt
            //determine if argument is a constant number
            for (argument <- currentControlFlowNodeHead.argumentList)
              if (argument.originalContent == arg._1) {
                writer.write(argument.name + "<-" + arg._1 + "\n")
                //add constant data flow in to clause data structure
                argument.constantFlowInNode = "\""+"xxx"+currentClause.name + "_" + currentClause.clauseID +  "xxx" +
                  argument.name + "_constant_" + "\""+arg._1+"\""
                //println(argument.constantFlowInNode)
              }
          }
          catch {
            case ex: Exception => {}
          }
        }
      }

      //if arguments in body are constant, add guard constant == arguments
      //body constant dataflow
      if (!argsInBody.isEmpty) {
        for ((arg, i) <- argsInBody.zipWithIndex) {
          try {
            arg._1.toInt
            //determine if argument is a constant number
            for (argument <- currentControlFlowNodeBody.argumentList)
              if (argument.originalContent == arg._1) {
                writer.write(argument.name + "<-" + arg._1 + "\n")
                //add constant data flow in to clause data structure
                argument.constantFlowInNode = "\""+"xxx"+currentClause.name + "_" + currentClause.clauseID  + "xxx" +
                  argument.name + "_constant_" +arg._1+"\""
                //println(argument.constantFlowInNode)
              }
          }catch {
            case ex: Exception => {}
          }
        }
      }


      //guard
      writer.write("Guard:\n")
      var guardMap = Map[String, IFormula]()
      //naming guard with index
      for ((conjunct, i) <- guardConjunct.zipWithIndex) {
        //PrincessLineariser.printExpression(conjunct)
        //println()
        writer.write(conjunct + "\n")
        guardMap=guardMap++Map(("guard_" + i.toString) -> conjunct)
      }
      //draw guard
      val (guardASTList,guardNodeHashMap) = drawAST(currentClause, "guard", guardMap,dataFlowNodeHashMap)
      for (ast <- guardASTList if !guardASTList.isEmpty) {
        currentClause.guardASTGraph = currentClause.guardASTGraph ++ Map(ast.astRootName -> ast.graphText)
      }
      //add currentClause to ClauseTransitionInformationList
      clauseList += currentClause
      writer.write("dataflow number:"+dataFlowMap.size+"\nguard number:"+guardMap.size+"\n")
    }


    writer.write("-----------\n")

    val predicates =
      (HornClauses allPredicates simpClauses).toList sortBy (_.name)
    val predIndex =
      (for ((p, n) <- predicates.iterator.zipWithIndex) yield (p -> n)).toMap


    writer.close()


    println("Write horn to graph")
    val writerGraph = new PrintWriter(new File("../trainData/" + fileName + ".gv")) //python path


    writerGraph.write("digraph dag {" + "\n")
    //control flow node
    for (p <- predicates) {
      //println("" + predIndex(p) + " [label=\"" + p.name + "\"];")
      writerGraph.write("" + p.name + " [label=\"" + p.name + "\"" + " shape=\"rect\"" + "];" + "\n")
    }
    writerGraph.write("FALSE" + " [label=\"" + "FALSE" + "\"" + " shape=\"rect\"" + "];" + "\n") //false node
    writerGraph.write("Initial" + " [label=\"" + "Initial" + "\"" + " shape=\"rect\"" + "];" + "\n") //initial node
    var ControlFowHyperEdgeList = new ListBuffer[ControlFowHyperEdge]() //build control flow hyper edge list


    //create control flow hyper edges, connections to control flow nodes, catch unique control flow node list
    var uniqueControlFLowNodeList = ListBuffer[ControlFlowNode]()
    for (clauseInfo <- clauseList) {
      //create control flow hyper edges and connections to control flow nodes
      //create control flow hyper edge nodes
      writerGraph.write(clauseInfo.controlFlowHyperEdge.name + " [label=\"Guarded ControlFlow Hyperedge\"" + " shape=\"diamond\"" + "];" + "\n")
      //create edges of control flow hyper edge
      writerGraph.write(clauseInfo.body.name + " -> " + clauseInfo.controlFlowHyperEdge.name + "[label=\"" + edgeNameMap("controlFlowIn") + "\"]" + "\n")
      writerGraph.write(clauseInfo.controlFlowHyperEdge.name + " -> " + clauseInfo.head.name + "[label=\"" + edgeNameMap("controlFlowOut") + "\"]" + "\n")


      //get unique control flow nodes
      if (!uniqueControlFLowNodeList.exists(_.name == clauseInfo.head.name)) {
        uniqueControlFLowNodeList += clauseInfo.head
      }
      if (!uniqueControlFLowNodeList.exists(_.name == clauseInfo.body.name)) {
        uniqueControlFLowNodeList += clauseInfo.body
      }


    }
    //create and connect to argument nodes
    for (controlFLowNode <- uniqueControlFLowNodeList; arg <- controlFLowNode.argumentList) {
      //create argument nodes
      writerGraph.write(arg.name + " [label=\"" + arg.name + "\"" + " shape=\"oval\"" + "];" + "\n")
      //connect arguments to location
      writerGraph.write(arg.name + " -> " + controlFLowNode.name + "[label=" + "\"" + edgeNameMap("argument") + "\"" +
        " style=\"dashed\"" + "]" + "\n")
    }



    //    for (Clause(IAtom(phead, headArgs), body, _) <- simpClauses;
    //         //if phead != HornClauses.FALSE;
    //         IAtom(pbody, _) <- body) {  //non-initial control flow iteration
    //
    //    }


    //create guarded data flow node for this clause
    writerGraph.write("\n")

    for (clauseInfo <- clauseList) {
      var andName = ""
      if (clauseInfo.guardNumber > 1) { //connect constraints by &
        andName = "xxx" + clauseInfo.name + "_" + clauseInfo.clauseID + "xxx" + "_and"
        writerGraph.write(andName + " [label=\"" + "&" + "\"" + " shape=\"rect\"" + "];" + "\n")
        clauseInfo.guardASTRootName = andName //store this node to clauses's guardASTRootName
      }
      //draw guard ast
      for ((rootName, ast) <- clauseInfo.guardASTGraph) { //draw guard ast
        writerGraph.write(ast + "\n")
        if (clauseInfo.guardNumber > 1) { //connect constraints by &
          //writerGraph.write(clauseInfo.name + "_and"+"->"+rootName//ast.substring(0,ast.indexOf("[label")-1)
          writerGraph.write(rootName + "->" + andName //ast.substring(0,ast.indexOf("[label")-1)
            + " [label=\"" + edgeNameMap("astAnd") + "\"" + "];" + "\n")
        } else {
          clauseInfo.guardASTRootName = rootName
        }

      }
      //guard AST root point to control flow hyperedge
      if (!clauseInfo.guardASTRootName.isEmpty) {
        writerGraph.write(clauseInfo.guardASTRootName + "->" + clauseInfo.controlFlowHyperEdge.name
          + " [label=\"" + edgeNameMap("condition") + "\"" + "];" + "\n")
      }
      //if there is no guard add true condition
      if (clauseInfo.guardASTGraph.isEmpty) {
        writerGraph.write(clauseInfo.trueCondition + " [label=\"" + "true" + "\"" + " shape=\"rect\"" + "];" + "\n") //add true node
        writerGraph.write(clauseInfo.trueCondition + "->" + clauseInfo.controlFlowHyperEdge.name //add edge to control flow hyper edges
          + " [label=\"" + edgeNameMap("condition") + "\"" + "];" + "\n")

      }
      //draw data flow ast

      for (graphInfo <- clauseInfo.dataFlowASTGraph; argNode <- clauseInfo.head.argumentList if (graphInfo.argumentName == argNode.name)) {
        //writerGraph.write("// graphtext begin \n") //draw AST
        writerGraph.write(graphInfo.graphText + "\n") //draw AST
        //writerGraph.write("// graphtext end \n") //draw AST
        writerGraph.write(graphInfo.astRootName + "->" + argNode.dataFLowHyperEdge.name //connect to data flow hyper edge
          + " [label=\"" + edgeNameMap("dataFlow") + "\"" + "];" + "\n")

      }


    }

    //draw data flow

    //draw guarded data flow hyperedge for head
    for (clauseInfo <- clauseList; headArg <- clauseInfo.head.argumentList; if !clauseInfo.head.argumentList.isEmpty) {
      //create data flow hyperedge node
      writerGraph.write(headArg.dataFLowHyperEdge.name +
        " [label=\"Guarded DataFlow Hyperedge\"" + " shape=\"diamond\"" + "];" + "\n")
      //create data flow hyperedge node coonections
      writerGraph.write(headArg.dataFLowHyperEdge.name + " -> " + headArg.name +
        "[label=\"" + edgeNameMap("dataFlowOut") + "\"]" + "\n")
      //guard AST root point to data flow hyperedge
      if (!clauseInfo.guardASTRootName.isEmpty) {
        writerGraph.write(clauseInfo.guardASTRootName + " -> " + headArg.dataFLowHyperEdge.name +
          "[label=\"" + edgeNameMap("dataFlowIn") + "\"]" + "\n")
      }
      //if there is no guard add true condition to data flow hyperedge
      if (clauseInfo.guardASTGraph.isEmpty) {
        writerGraph.write(clauseInfo.trueCondition + "->" + headArg.dataFLowHyperEdge.name //add edge to data flow hyper edges
          + " [label=\"" + edgeNameMap("condition") + "\"" + "];" + "\n")
        //todo:add true condition to data flow hyperedge (check)
      }
      //data flow AST root point to data flow hyperedge


    }
    //draw constant data flow for head
    for (clauseInfo <- clauseList) {
      for (headArg <- clauseInfo.head.argumentList; if !clauseInfo.head.argumentList.isEmpty) {
        if (headArg.constantFlowInNode != "") {
          writerGraph.write(headArg.constantFlowInNode
            + " [label=\"" + headArg.originalContent + "\"" + "];" + "\n") //create constant node
          writerGraph.write(headArg.constantFlowInNode + "->" + headArg.dataFLowHyperEdge.name //add edge to argument
            + " [label=\"" + edgeNameMap("constantDataFlow") + "\"" + "];" + "\n")
        }
      }
      //draw constant data flow for body
      for (bodyArg <- clauseInfo.body.argumentList; if !clauseInfo.body.argumentList.isEmpty) {
        if (!bodyArg.constantFlowInNode.isEmpty) {
          writerGraph.write(bodyArg.constantFlowInNode
            + " [label=\"" + bodyArg.originalContent + "\"" + "];" + "\n") //create constant node
          //todo: find where this body be head, and find that dataflow hyper edge
          writerGraph.write(bodyArg.constantFlowInNode + "->" + bodyArg.name //add edge to argument
            + " [label=\"" + edgeNameMap("constantDataFlow") + "\"" + "];" + "\n")
        }
      }
    }



    //draw simple data flow connection
    for (clauseInfo <- clauseList) {

      if (!clauseInfo.simpleDataFlowConnection.isEmpty) {
        for ((hyperedge, connection) <- clauseInfo.simpleDataFlowConnection) {
          writerGraph.write(connection)
        }

      }
    }


    writerGraph.write("}" + "\n")

    writerGraph.close()
  }

  def drawAST(clause: ClauseTransitionInformation, ASTType: String,
              conatraintMap: Map[String, IExpression],
              freeVariableMap:MHashMap[String,ITerm]) = {
    var ASTGraph = ListBuffer[DataFlowASTGraphInfo]()
    var nodeCount: Int = 0
    var dataFlowCount: Int = 0
    var astNodeNamePrefix = "xxx" + clause.name + "_" + clause.clauseID + "xxx" + ASTType +"_"+ dataFlowCount + "_node_"
    var root = new TreeNodeForGraph(Map((astNodeNamePrefix + nodeCount) -> "root"))
    var logString: String = "" //store node information
    var rootMark = root
    var rootName = ""
    var nodeHashMap:MHashMap[String,ITerm]=freeVariableMap

    def translateConstraint(e: IExpression, root: TreeNodeForGraph): Unit = {

      e match {
        case INot(subformula) => {
          //println("INOT")
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "!"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "!" + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "!"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "!" + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.rchild)
          }
        }
        case IAtom(pred, args) => {
          val p = pred.name
          //println("IAtom")
          if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == p)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(p) -> (p)))
              logString = logString + (clause.body.getArgNameByContent(p) +
                " [label=\"" + clause.body.getArgNameByContent(p) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(p)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == p)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(p) -> (p)))
              logString = logString + (clause.head.getArgNameByContent(p) +
                " [label=\"" + clause.head.getArgNameByContent(p) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(p)
              }
            } else {
              root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (p)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + p + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->p))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ p +"\"];"+"\n")
            //            if(nodeCount==0){
            //              rootName=astNodeNamePrefix+nodeCount
            //            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.lchild)
            }

          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == p)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(p) -> (p)))
              logString = logString + (clause.body.getArgNameByContent(p) +
                " [label=\"" + clause.body.getArgNameByContent(p) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(p)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == p)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(p) -> (p)))
              logString = logString + (clause.head.getArgNameByContent(p) +
                " [label=\"" + clause.head.getArgNameByContent(p) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(p)
              }
            } else {
              root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (p)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + p + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->p))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ p +"\"];"+"\n")
            //            if(nodeCount==0){
            //              rootName=astNodeNamePrefix+nodeCount
            //            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.rchild)
            }
          }

        }
        case IBinFormula(junctor, f1, f2) => {
          //println("IBinFormula")
          //println(j.toString)
          val j = junctor.toString
          if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == j)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(j) -> (j)))
              logString = logString + (clause.body.getArgNameByContent(j) +
                " [label=\"" + clause.body.getArgNameByContent(j) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(j)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == j)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(j) -> (j)))
              logString = logString + (clause.head.getArgNameByContent(j) +
                " [label=\"" + clause.head.getArgNameByContent(j) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(j)
              }
            } else {
              root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (j)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + j + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->j))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ j +"\"];"+"\n")
            //            if(nodeCount==0){
            //              rootName=astNodeNamePrefix+nodeCount
            //            }
            nodeCount = nodeCount + 1
            translateConstraint(f1, root.lchild)
            translateConstraint(f2, root.lchild)

          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == j)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(j) -> (j)))
              logString = logString + (clause.body.getArgNameByContent(j) +
                " [label=\"" + j + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(j)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == j)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(j) -> (j)))
              logString = logString + (clause.head.getArgNameByContent(j) +
                " [label=\"" + clause.head.getArgNameByContent(j) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(j)
              }
            } else {
              root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (j)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + j + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->j))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ j +"\"];"+"\n")
            //            if(nodeCount==0){
            //              rootName=astNodeNamePrefix+nodeCount
            //            }
            nodeCount = nodeCount + 1
            translateConstraint(f1, root.rchild)
            translateConstraint(f2, root.rchild)
          }


        }
        case IBoolLit(value) => {
          //println("IBoolLit")
          //println(value)
          val v = value.toString
          if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.body.getArgNameByContent(v) +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.head.getArgNameByContent(v) + " [label=\"" + clause.head.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (v)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + v + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->(v)))
            //root=root.lchild
          } else if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.body.getArgNameByContent(v) +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.head.getArgNameByContent(v) + " [label=\"" + clause.head.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (v)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + v + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->(v)))
            //root=root.rchild
          }
          //println(nodeCount + " [label=\""+ "_"+index +"\"];")
          //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+v +"\"];"+"\n")
          //          if(nodeCount==0){
          //            rootName=astNodeNamePrefix+nodeCount
          //          }
          nodeCount = nodeCount + 1
        }
        case IConstant(constantTerm) => {
          val c = constantTerm.toString()
          //println("IConstant")
          //println(c)
          if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == c)) {
              //              println(clause.body.getArgNameByContent(c))
              //              println(c)
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(c) -> (c)))
              if(!clause.nodeList.exists(x=>x._1==clause.body.getArgNameByContent(c))){
                logString = logString + (clause.body.getArgNameByContent(c) +
                  " [label=\"" + clause.body.getArgNameByContent(c) + "\"];" + "\n")
                clause.nodeList+=Pair(clause.body.getArgNameByContent(c),clause.body.getArgNameByContent(c))
              }
//              logString = logString + (clause.body.getArgNameByContent(c) +
//                " [label=\"" + clause.body.getArgNameByContent(c) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(c)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == c)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(c) -> (c)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(c))){
                logString = logString + (clause.head.getArgNameByContent(c) +
                  " [label=\"" + clause.head.getArgNameByContent(c) + "\"];" + "\n")
                clause.nodeList+=Pair(clause.head.getArgNameByContent(c),clause.head.getArgNameByContent(c))
              }
//              logString = logString + (clause.head.getArgNameByContent(c) +
//                " [label=\"" + clause.head.getArgNameByContent(c) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(c)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,c,nodeHashMap, constantTerm)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (c)))
              if(!clause.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + (nodeName + " [label=\"" + c + "\"];" + "\n")
                clause.nodeList+=Pair(nodeName,c)
              }
              //logString = logString + (nodeName + " [label=\"" + c + "\"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
            //root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->(c.toString)))
            //root=root.lchild
          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == c)) {
              //              println(clause.body.getArgNameByContent(c))
              //              println(c)
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(c) -> (c)))
              if(!clause.nodeList.exists(x=>x._1==clause.body.getArgNameByContent(c))){
                logString = logString + (clause.body.getArgNameByContent(c) +
                  " [label=\"" + clause.body.getArgNameByContent(c) + "\"];" + "\n")
                clause.nodeList+=Pair(clause.body.getArgNameByContent(c),clause.body.getArgNameByContent(c))
              }
//              logString = logString + (clause.body.getArgNameByContent(c) +
//                " [label=\"" + clause.body.getArgNameByContent(c) + "\"];" + "\n")
              rootName = checkASTRoot(nodeCount,clause.body.getArgNameByContent(c),rootName)
            } else if (clause.head.argumentList.exists(_.originalContent == c)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(c) -> (c)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(c))){
                logString = logString + (clause.head.getArgNameByContent(c) +
                  " [label=\"" + clause.head.getArgNameByContent(c) + "\"];" + "\n")
                clause.nodeList+=Pair(clause.head.getArgNameByContent(c),clause.head.getArgNameByContent(c))
              }
//              logString = logString + (clause.head.getArgNameByContent(c) +
//                " [label=\"" + clause.head.getArgNameByContent(c) + "\"];" + "\n")
              rootName = checkASTRoot(nodeCount,clause.head.getArgNameByContent(c),rootName)
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,c,nodeHashMap, constantTerm)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (c)))
              if(!clause.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + (nodeName + " [label=\"" + c + "\"];" + "\n")
                clause.nodeList+=Pair(nodeName,c)
              }
              //logString = logString + (nodeName + " [label=\"" + c + "\"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)

            }
            //root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->(c.toString)))
            //root=root.rchild
          }
          //println(nodeCount + " [label=\""+ "_"+index +"\"];")
          //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+c.toString() +"\"];"+"\n")
          //          if(nodeCount==0){
          //            rootName=astNodeNamePrefix+nodeCount
          //          }
          nodeCount = nodeCount + 1
        }
        case IEpsilon(cond) => {
          //println("IEpsilon")
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "IEpsilon"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "IEpsilon" + "\"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.lchild)

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "IEpsilon"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "IEpsilon" + "\"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.rchild)
          }
        }
        //case IFormula()=>println("IFormula")
        case IFormulaITE(cond, left, right) => {
          //println("IFormulaITE")
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "IFormulaITE"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "IFormulaITE" + "\"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.lchild)
            translateConstraint(left, root.lchild)
            translateConstraint(right, root.lchild)

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "IFormulaITE"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "IFormulaITE" + "\"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.rchild)
            translateConstraint(left, root.rchild)
            translateConstraint(right, root.rchild)

          }
        }
        case IFunApp(fun, args) => {
          //println("IFunApp");
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "IFunApp"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "IFunApp" + "\"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.lchild)
            }

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "IFunApp"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "IFunApp" + "\"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.rchild)
            }

          }
        }
        case Eq(t1, t2) => {
          val eq = "="
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> eq))
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + eq + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> eq))
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + eq + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)

          }
        }
        case Geq(t1, t2) => {
          val geq = ">="
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> geq))
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + geq + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> geq))
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + geq + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)

          }
        }
        case EqLit(term, lit) => {
          val v = lit.toString()
          val eq = "="
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> eq))
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + eq + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.lchild.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.body.getArgNameByContent(v) +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\"];" + "\n")
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.head.getArgNameByContent(v) + " [label=\"" + clause.head.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, lit)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + (nodeName + " [label=\"" + v + "\"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)

//              root.lchild.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (v)))
//              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + v + "\"];" + "\n")
            }
            //root.lchild.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->v))
            //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ v +"\"];"+"\n")
            nodeCount = nodeCount + 1
            translateConstraint(term, root.lchild)


          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> eq))
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + eq + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.rchild.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.body.getArgNameByContent(v) +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\"];" + "\n")
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.head.getArgNameByContent(v) + " [label=\"" + clause.head.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, lit)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild.rchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + (nodeName + " [label=\"" + v + "\"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
//              root.rchild.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (v)))
//              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + v + "\"];" + "\n")
            }
            //root.rchild.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->v))
            //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ v +"\"];"+"\n")
            nodeCount = nodeCount + 1
            translateConstraint(term, root.rchild)

          }
        }
        case GeqZ(t) => {
          val geq = ">="
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> geq))
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + geq + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1


            val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,"0",nodeHashMap, 0)
            nodeHashMap=nodeHashMapOut
            val nodeName:String=nodeNameOut
            root.lchild.lchild = new TreeNodeForGraph(Map(nodeName -> ("0")))
            logString = logString + (nodeName + " [label=\"" + "0" + "\"];" + "\n")
            rootName = checkASTRoot(nodeCount,nodeName,rootName)

            //            root.lchild.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "constant_0"))
            //            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "0" + "\"];" + "\n")
            nodeCount = nodeCount + 1
            translateConstraint(t, root.lchild)

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> geq))
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + geq + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,"0",nodeHashMap, 0)
            nodeHashMap=nodeHashMapOut
            val nodeName:String=nodeNameOut
            root.rchild.rchild = new TreeNodeForGraph(Map(nodeName -> ("0")))
            logString = logString + (nodeName + " [label=\"" + "0" + "\"];" + "\n")
            rootName = checkASTRoot(nodeCount,nodeName,rootName)

            //            root.rchild.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "constant_0"))
            //            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "0" + "\"];" + "\n")
            nodeCount = nodeCount + 1
            translateConstraint(t, root.rchild)
          }
        }
        case IIntLit(value) => {
          val v = value.toString()
          //println("IIntLit")
          //println(v)
          if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              if(!clause.nodeList.exists(x=>x._1==clause.body.getArgNameByContent(v))){
                logString = logString + (clause.body.getArgNameByContent(v) +
                  " [label=\"" + clause.body.getArgNameByContent(v) + "\"];" + "\n")
                clause.nodeList+=Pair(clause.body.getArgNameByContent(v),clause.body.getArgNameByContent(v))
              }
//              logString = logString + (clause.body.getArgNameByContent(v) +
//                " [label=\"" + clause.body.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(v))){
                logString = logString + (clause.head.getArgNameByContent(v) +
                  " [label=\"" + clause.head.getArgNameByContent(v) + "\"];" + "\n")
                clause.nodeList+=Pair(clause.head.getArgNameByContent(v),clause.head.getArgNameByContent(v))
              }
//              logString = logString + (clause.head.getArgNameByContent(v) +
//                " [label=\"" + clause.head.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, value)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              //todo: remove node declare redundancy
              if(!clause.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + (nodeName + " [label=\"" + v + "\"];" + "\n")
                clause.nodeList+=Pair(nodeName,v)
              }
              //logString = logString + (nodeName + " [label=\"" + v + "\"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
//              root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (v)))
//              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + v + "\"];" + "\n")
//              if (nodeCount == 0) {
//                rootName = astNodeNamePrefix + nodeCount
//              }
            }
            //root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->(v)))
          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              if(!clause.nodeList.exists(x=>x._1==clause.body.getArgNameByContent(v))){
                logString = logString + (clause.body.getArgNameByContent(v) +
                  " [label=\"" + clause.body.getArgNameByContent(v) + "\"];" + "\n")
                clause.nodeList+=Pair(clause.body.getArgNameByContent(v),clause.body.getArgNameByContent(v))
              }
//              logString = logString + (clause.body.getArgNameByContent(v) +
//                " [label=\"" + clause.body.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(v))){
                logString = logString + (clause.head.getArgNameByContent(v) +
                  " [label=\"" + clause.head.getArgNameByContent(v) + "\"];" + "\n")
                clause.nodeList+=Pair(clause.head.getArgNameByContent(v),clause.head.getArgNameByContent(v))
              }
//              logString = logString + (clause.head.getArgNameByContent(v) +
//                " [label=\"" + clause.head.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, value)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              if(!clause.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + (nodeName + " [label=\"" + v + "\"];" + "\n")
                clause.nodeList+=Pair(nodeName,v)
              }
              //logString = logString + (nodeName + " [label=\"" + v + "\"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)

//              root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (v)))
//              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + v + "\"];" + "\n")
//              if (nodeCount == 0) {
//                rootName = astNodeNamePrefix + nodeCount
//              }
            }
            //root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->(v)))
          }
          //println(nodeCount + " [label=\""+ "_"+index +"\"];")
          //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+v +"\"];"+"\n")
          nodeCount = nodeCount + 1
        }
        case INamedPart(name, subformula) => {
          //println("INamedPart")
          val n = name.toString
          if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == n)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(n) -> (n)))
              logString = logString + (clause.body.getArgNameByContent(n) +
                " [label=\"" + clause.body.getArgNameByContent(n) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(n)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == n)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(n) -> (n)))
              logString = logString + (clause.head.getArgNameByContent(n) +
                " [label=\"" + clause.head.getArgNameByContent(n) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(n)
              }
            } else {
              root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (n)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + n + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->n))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ n +"\"];"+"\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)


          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == n)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(n) -> (n)))
              logString = logString + (clause.body.getArgNameByContent(n) +
                " [label=\"" + clause.body.getArgNameByContent(n) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(n)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == n)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(n) -> (n)))
              logString = logString + (clause.head.getArgNameByContent(n) +
                " [label=\"" + clause.head.getArgNameByContent(n) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(n)
              }
            } else {
              root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (n)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + n + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->n))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ n +"\"];"+"\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)
          }
        }
        case Difference(t1, t2) => {
          val d = "-"
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> d))
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + d + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> d))
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + d + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)

          }
        }
        case IPlus(t1, t2) => {
          val p = "+"
          //println("IPLUS")
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> p))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + p + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> p))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + p + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)

          }

        }
        case IQuantified(quan, subformula) => {
          val q = quan.toString
          //println("IQuantified")
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> q))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + q + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> q))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + q + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.rchild)
          }
        }
        //case ITerm()=>println("ITerm")
        case ITermITE(cond, left, right) => {
          //println("ITermITE")
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "ITermITE"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "ITermITE" + "\"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.lchild)
            translateConstraint(left, root.lchild)
            translateConstraint(right, root.lchild)

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "ITermITE"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "ITermITE" + "\"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.rchild)
            translateConstraint(left, root.rchild)
            translateConstraint(right, root.rchild)

          }
        }
        case ITimes(coeff, t) => {
          val v = coeff.toString()
          //println("ITimes")
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "*"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "*" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"*\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.body.getArgNameByContent(v) +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.head.getArgNameByContent(v) +
                " [label=\"" + clause.head.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, coeff)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (v)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + v + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //            root.lchild.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->v))
            //            //println(nodeCount + " [label=\""+ coeff +"\"];")
            //            logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ v +"\"];"+"\n")
            //            if(nodeCount==0){
            //              rootName=astNodeNamePrefix+nodeCount
            //            }
            nodeCount = nodeCount + 1
            translateConstraint(t, root.lchild)
          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "*"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "*" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"*\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.body.getArgNameByContent(v) +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + (clause.head.getArgNameByContent(v) +
                " [label=\"" + clause.head.getArgNameByContent(v) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, coeff)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (v)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + v + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //root.rchild.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->coeff.toString()))
            //println(nodeCount + " [label=\""+ coeff +"\"];")
            //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ coeff +"\"];"+"\n")
            //            if(nodeCount==0){
            //              rootName=astNodeNamePrefix+nodeCount
            //            }
            nodeCount = nodeCount + 1
            translateConstraint(t, root.rchild)
          }

        }
        case ITrigger(patterns, subformula) => {
          //println("ITrigger");
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "ITrigger"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "ITrigger" + "\"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)
            for (p <- patterns) {
              translateConstraint(p, root.lchild)
            }

          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "ITrigger"))
            //root=root.lchild
            //println(nodeCount + " [label=\""+ "+" +"\"];")
            logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + "ITrigger" + "\"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.rchild)
            for (p <- patterns) {
              translateConstraint(p, root.rchild)
            }

          }
        }
        case IVariable(index) => {
          println("IVariable")
          val i = index.toString
          println(i)
          if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == i)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(i) -> (i)))
              logString = logString + (clause.body.getArgNameByContent(i) +
                " [label=\"" + clause.body.getArgNameByContent(i) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(i)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == i)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(i) -> (i)))
              logString = logString + (clause.head.getArgNameByContent(i) + " [label=\"" + clause.head.getArgNameByContent(i) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(i)
              }
            } else {
              root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (i)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + i + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->(i)))
            //root=root.lchild
            //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ i +"\"];"+"\n")

            nodeCount = nodeCount + 1
          } else if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == i)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(i) -> (i)))
              logString = logString + (clause.body.getArgNameByContent(i) +
                " [label=\"" + clause.body.getArgNameByContent(i) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(i)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == i)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(i) -> (i)))
              logString = logString + (clause.head.getArgNameByContent(i) + " [label=\"" + clause.head.getArgNameByContent(i) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(i)
              }
            } else {
              root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (i)))
              logString = logString + (astNodeNamePrefix + nodeCount + " [label=\"" + i + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            //root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->(i)))
            //root=root.rchild
            //logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ i +"\"];"+"\n")
            nodeCount = nodeCount + 1
          }

        }
        case IIntFormula(rel, t) => {
          println("IIntFormula")
          //          if(root.lchild==null){
          //            if(rel.toString=="GeqZero"){
          //              root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->">="))
          //              logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ ">=" +"\"];"+"\n")
          //              if(nodeCount==0){
          //                rootName=astNodeNamePrefix+nodeCount
          //              }
          //              nodeCount=nodeCount+1
          //              root.lchild.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->"constant_0"))
          //              //println(nodeCount + " [label=\""+ "0" +"\"];")
          //              logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ "0" +"\"];"+"\n")
          //              if(nodeCount==0){
          //                rootName=astNodeNamePrefix+nodeCount
          //              }
          //              nodeCount=nodeCount+1
          //              //root=root.lchild
          //              translateConstraint(t,root.lchild)
          //              //println(nodeCount + " [label=\""+ ">=" +"\"];")
          //
          //            }
          //          }else if(root.rchild==null){
          //            if(rel.toString=="GeqZero"){
          //              root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->">="))
          //              logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ ">=" +"\"];"+"\n")
          //              if(nodeCount==0){
          //                rootName=astNodeNamePrefix+nodeCount
          //              }
          //              nodeCount=nodeCount+1
          //              root.rchild.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->"constant_0"))
          //              //println(nodeCount + " [label=\""+ "0" +"\"];")
          //              logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ "0" +"\"];"+"\n")
          //              if(nodeCount==0){
          //                rootName=astNodeNamePrefix+nodeCount
          //              }
          //              nodeCount=nodeCount+1
          //              //root=root.lchild
          //              translateConstraint(t,root.rchild)
          //              //println(nodeCount + " [label=\""+ ">=" +"\"];")
          //
          //            }
          //          }
        }
        case _ => println("?")
      }
    }

    for ((argumentName, conatraint) <- conatraintMap) { //get dataflow or guard element list and parse data flow to AST
      if (ASTType == "guard") {
        clause.guardNumber = clause.guardNumber + 1
      } else {
        clause.dataFlowNumber = clause.dataFlowNumber + 1
      }
      translateConstraint(conatraint, root) //define nodes in graph, information is stored in logString
      BinarySearchTreeForGraph.ASTtype = ASTType
      BinarySearchTreeForGraph.nodeString = logString
      BinarySearchTreeForGraph.preOrder(rootMark) //connect nodes in graph, information is stored in relationString
      logString = BinarySearchTreeForGraph.nodeString + BinarySearchTreeForGraph.relationString
      BinarySearchTreeForGraph.relationString = ""
      BinarySearchTreeForGraph.nodeString = ""


      val currentASTGraph = new DataFlowASTGraphInfo(rootName, argumentName, logString)
      ASTGraph += currentASTGraph //record graph as string
      //writer.write("}"+"\n")
      logString = ""
      nodeCount = 0
      dataFlowCount = dataFlowCount + 1
      astNodeNamePrefix = "xxx" + clause.name + "_" + clause.clauseID + "xxx" + ASTType + dataFlowCount + "_node_"
      root = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "root"))
      rootMark = root
    }
    (ASTGraph,nodeHashMap)
  }

  def checkASTRoot(nodeCount:Int,nodeName:String,currentRoot:String): String ={
    if(nodeCount==0){
      nodeName
    }else{
      currentRoot
    }
  }
  def mergeFreeVariables(astNodeNamePrefix:String,nodeCount:Int,v:String,nodeHashMapIn:MHashMap[String,ITerm],
                         value:IdealInt) ={
    var nodeHashMap:MHashMap[String,ITerm]=nodeHashMapIn
    var nodeName:String=astNodeNamePrefix + nodeCount
    var forFlag=false
    if(nodeHashMap.exists(node=>node._2.toString==v)){
      for((nName,nContent)<-nodeHashMap if !nodeHashMap.isEmpty && forFlag==false){
        if(nContent.toString==v){ //if the node existed in hash map, use it name
          nodeName=nName
          forFlag=true
        }
      }
    }else{
      nodeHashMap+=(nodeName->new IIntLit(value))
    }
//    for((nName,nContent)<-nodeHashMap if !nodeHashMap.isEmpty && forFlag==false){
//      if(nContent.toString!=v){ //if the node existed in hash map
//        println(nContent.toString+"!="+v)
//        nodeHashMap+=(nodeName->new IIntLit(value))
//      }else{
//        println(nContent.toString+"=="+v)
//        nodeName=nName
//        println(nodeName)
//        forFlag=true
//      }
//    }
    if(nodeHashMap.isEmpty){
      nodeHashMap+=(nodeName->new IIntLit(value))
    }
    (nodeHashMap,nodeName)
  }

  //rewrite to deal with IConstant
  def mergeFreeVariables(astNodeNamePrefix:String,nodeCount:Int,v:String,nodeHashMapIn:MHashMap[String,ITerm],
                         value:ConstantTerm) ={
    var nodeHashMap:MHashMap[String,ITerm]=nodeHashMapIn
    var nodeName:String=astNodeNamePrefix + nodeCount
    var forFlag=false
    if(nodeHashMap.exists(node=>node._2.toString==v)){
      for((nName,nContent)<-nodeHashMap if !nodeHashMap.isEmpty && forFlag==false){
        if(nContent.toString==v){ //if the node existed in hash map, use it name
          nodeName=nName
          forFlag=true
        }
      }
    }else{
      nodeHashMap+=(nodeName->new IConstant(value))
    }
    //    for((nName,nContent)<-nodeHashMap if !nodeHashMap.isEmpty && forFlag==false){
    //      if(nContent.toString!=v){ //if the node existed in hash map
    //        println(nContent.toString+"!="+v)
    //        nodeHashMap+=(nodeName->new IIntLit(value))
    //      }else{
    //        println(nContent.toString+"=="+v)
    //        nodeName=nName
    //        println(nodeName)
    //        forFlag=true
    //      }
    //    }
    if(nodeHashMap.isEmpty){
      nodeHashMap+=(nodeName->new IConstant(value))
    }
    (nodeHashMap,nodeName)
  }


  def writeSMTFormatToFile(simpClauses: Clauses, path: String): Unit = {

    val basename = GlobalParameters.get.fileName
    //      val suffix =
    //        (for (inv <- invariants) yield (inv mkString "_")) mkString "--"
    //      val filename = basename + "-" + suffix + ".smt2"
    //println(basename.substring(basename.lastIndexOf("/")+1))
    val fileName = basename.substring(basename.lastIndexOf("/") + 1)
    //val filename = basename + ".smt2"
    println("write " + fileName + " to smt format file")
    //val out = new java.io.FileOutputStream("trainData/"+fileName+".smt2")
    val out = new java.io.FileOutputStream(path + fileName + ".smt2") //python path
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


}

