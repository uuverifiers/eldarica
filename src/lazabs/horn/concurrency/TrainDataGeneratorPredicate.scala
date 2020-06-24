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

package lazabs.horn.concurrency

import java.io.{File, PrintWriter}
import java.lang.System.currentTimeMillis

import ap.parser._
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import lazabs.GlobalParameters
import lazabs.Main.TimeoutException
import lazabs.horn.abstractions.VerificationHints.VerifHintElement
import lazabs.horn.abstractions.{AbstractionRecord, StaticAbstractionBuilder, VerificationHints}
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{DagInterpolator, HornClauses, HornPredAbs, TemplateInterpolator}
import lazabs.horn.preprocessor.DefaultPreprocessor

import scala.collection.immutable.ListMap
//import scala.collection.mutable.Seq
/////debug/////
class TrainDataGeneratorPredicate(smallSystem : ParametricEncoder.System, system : ParametricEncoder.System){
  import VerificationLoop._
  val processNum = smallSystem.processes.size
  var invariants: Seq[Seq[Int]] =
    for (i <- 0 until processNum)
      yield ((List tabulate processNum) { j => if (i == j) 1 else 0 })

  var res: Either[Unit, Counterexample] = null

  println
  println("Using invariants " + (invariants mkString ", "))
  println


  val encoder: ParametricEncoder = new ParametricEncoder(smallSystem, invariants)


  val preprocessor = new DefaultPreprocessor
  val (simpClauses, simpHints, backTranslator) =
    Console.withErr(Console.out) {
      preprocessor.process(encoder.allClauses, encoder.globalHints)
    }

  //test JSON reading
  //  println("---debug---")
  //  HintsSelection.readHintsFromJSON("test")
  //  println("---debug---")


  //output all training data
  if(GlobalParameters.get.getSMT2==true){
    HintsSelection.writeSMTFormatToFile(encoder.allClauses,"regression-tests/smt-graph/")  //write smt2 format to file
    println(encoder.allClauses)
  }
  //transform initial predicates from CEGAR to initial templates
//  val initialPredicates=HintsSelection.getInitialPredicates(encoder,simpHints,simpClauses)
//
//  val sortedHints=HintsSelection.sortHints(initialPredicates)
//  if(sortedHints.isEmpty){}else{
//    //write selected hints with IDs to file
//    val InitialHintsWithID=initialIDForHints(sortedHints) //ID:head->hint
//    println("---initialHints-----")
//    for (wrappedHint<-InitialHintsWithID){
//      println(wrappedHint.ID.toString,wrappedHint.head,wrappedHint.hint)
//    }
    //select predicates directly
    //val selectedHint=HintsSelection.tryAndTestSelectionPredicate(encoder,simpHints,simpClauses,GlobalParameters.get.fileName)

    //transform to templates and select the templates
    //val selectedHint=HintsSelection.tryAndTestSelecton(encoder,sortedHints,simpClauses,GlobalParameters.get.fileName,InitialHintsWithID,false)
    //val selectedHint=HintsSelection.tryAndTestSelectionTemplates(encoder,sortedHints,simpClauses,GlobalParameters.get.fileName,InitialHintsWithID,false)


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
  val file = GlobalParameters.get.fileName
  val fileName=file.substring(file.lastIndexOf("/")+1)
  val timeOut = GlobalParameters.get.threadTimeout //timeout
  val solvabilityTimeout=GlobalParameters.get.solvabilityTimeout

  val exceptionalPredGen: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
    Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom, HornPredAbs.NormClause)]] =
    (x: Dag[AndOrNode[HornPredAbs.NormClause, Unit]]) =>
      //throw new RuntimeException("interpolator exception")
      throw lazabs.Main.TimeoutException

  println("extract original predicates")
  val startTimeCEGAR = currentTimeMillis
  val toParamsCEGAR = GlobalParameters.get.clone
  toParamsCEGAR.timeoutChecker = () => {
    if ((currentTimeMillis - startTimeCEGAR) > solvabilityTimeout * 1000) //timeout milliseconds
      throw lazabs.Main.TimeoutException //Main.TimeoutException
  }
  try{
    GlobalParameters.parameters.withValue(toParamsCEGAR) {
      new HornPredAbs(simpClauses, simpHints.toInitialPredicates, interpolator)
    }
  }
  catch {
    case lazabs.Main.TimeoutException => {
      throw TimeoutException
    }
  }

  val cegar = new HornPredAbs(simpClauses,
    simpHints.toInitialPredicates,
    interpolator)

  val LastPredicate = cegar.predicates //Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]]


  if(LastPredicate.isEmpty){
    println("No predicates needed")
  }else{


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


    var initialPredicates = VerificationHints(Map())
    for ((head, preds) <- originalPredicates) {
      var x: Seq[VerifHintElement] = Seq()
      for (p <- preds) {
        x = x ++ Seq(VerificationHints.VerifHintInitPred(p))
      }
      initialPredicates = initialPredicates.addPredicateHints(Map(head -> x))
    }

    val sortedHints=HintsSelection.sortHints(initialPredicates)
    //      if(sortedHints.isEmpty){}else{
    //write selected hints with IDs to file
    val InitialHintsWithID=initialIDForHints(sortedHints) //ID:head->hint
    println("---initialHints-----")
    for (wrappedHint<-InitialHintsWithID){
      println(wrappedHint.ID.toString,wrappedHint.head,wrappedHint.hint)
    }


    //Predicate selection begin
    println("------Predicates selection begin----")
    var PositiveHintsWithID:Seq[wrappedHintWithID]=Seq()
    var NegativeHintsWithID:Seq[wrappedHintWithID]=Seq()
    var optimizedPredicate:Map[Predicate, Seq[IFormula]]=Map()
    var currentPredicate: Map[Predicate, Seq[IFormula]] = originalPredicates
    for ((head, preds) <- originalPredicates) {
      // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
      var criticalPredicatesSeq:  Seq[IFormula] = Seq()
      var redundantPredicatesSeq: Seq[IFormula] = Seq()
      var CurrentTemplates=VerificationHints(Map())

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
        println("delete predicate",p)
        val currentPredicateSeq = currentPredicate(head).filter(_ != p) //delete one predicate
        currentPredicate = currentPredicate.filterKeys(_!=head) //delete original head
        if(!currentPredicateSeq.isEmpty){
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
            println("add redundant predicate",p.toString)
            redundantPredicatesSeq = redundantPredicatesSeq ++ Seq(p)
            //add useless hint to NegativeHintsWithID   //ID:head->hint
            for (wrappedHint <- InitialHintsWithID) {
              val pVerifHintInitPred="VerifHintInitPred("+p.toString+")"
              if (wrappedHint.head==head.name.toString && wrappedHint.hint==pVerifHintInitPred) {
                NegativeHintsWithID =NegativeHintsWithID++Seq(wrappedHint) //some redundancy
              }
            }
          }
        } catch {
          case lazabs.Main.TimeoutException => {
            //catch timeout
            println("add critical predicate",p.toString)
            criticalPredicatesSeq = criticalPredicatesSeq ++ Seq(p)
            //add deleted predicate back to curren predicate
            currentPredicate = currentPredicate.filterKeys(_!=head) //delete original head
            currentPredicate = currentPredicate ++ Map(head -> (currentPredicateSeq++Seq(p))) //add the head with deleted predicate
            //
            for(wrappedHint<-InitialHintsWithID){ //add useful hint to PositiveHintsWithID
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
        optimizedPredicate = optimizedPredicate++Map(head->criticalPredicatesSeq)
      }
      println("current head:", head.toString())
      println("critical predicates:", criticalPredicatesSeq.toString())
      println("redundant predicates", redundantPredicatesSeq.toString())
    }


    //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
    var selectedTemplates=VerificationHints(Map())
    for ((head,preds)<-optimizedPredicate) {
      var x:Seq[VerifHintElement]=Seq()
      for (p<-preds){
        x=x++Seq(VerificationHints.VerifHintInitPred(p))
      }
      selectedTemplates=selectedTemplates.addPredicateHints(Map(head->x))
    }

    println("\n------------predicates selection end-------------------------")
    //println("\nsimpHints Hints:")
    //simpHints.pretyPrintHints()
    println("\nOptimized Hints:")
    println("!@@@@")
    selectedTemplates.pretyPrintHints()
    println("@@@@!")
    println("timeout:"+GlobalParameters.get.threadTimeout)

    println("\n------------test selected predicates-------------------------")
    val test=new HornPredAbs(simpClauses, // loop
      selectedTemplates.toInitialPredicates, //emptyHints
      exceptionalPredGen).result
    println("-----------------test finished-----------------------")

    if(selectedTemplates.isEmpty){
      writeHintsWithIDToFile(InitialHintsWithID,fileName,"initial")//write hints and their ID to file
    }else{//only write to file when optimized hint is not empty
      writeHintsWithIDToFile(InitialHintsWithID,fileName,"initial")//write hints and their ID to file
      writeHintsWithIDToFile(PositiveHintsWithID,fileName,"positive")
      writeHintsWithIDToFile(NegativeHintsWithID,fileName,"negative")
    }





    if(selectedTemplates.isEmpty){ //when no hint available
      //not write horn clauses to file
    }else{
      //write horn clauses to file
      HintsSelection.writeHornClausesToFile(GlobalParameters.get.fileName,simpClauses)
      //write smt2 format to file
      if(GlobalParameters.get.fileName.endsWith(".c")){ //if it is a c file
        HintsSelection.writeSMTFormatToFile(simpClauses,"../trainData/")  //write smt2 format to file
      }
      if(GlobalParameters.get.fileName.endsWith(".smt2")){ //if it is a smt2 file
        //copy smt2 file
      }
      val argumentList=(for (p <- HornClauses.allPredicates(simpClauses)) yield (p, p.arity)).toList
      HintsSelection.writeArgumentScoreToFile(GlobalParameters.get.fileName,argumentList,selectedTemplates)
      //Output graphs
      //val hornGraph = new GraphTranslator(simpClauses, GlobalParameters.get.fileName)
      DrawHornGraph.writeHornClausesGraphToFile(GlobalParameters.get.fileName,simpClauses,sortedHints)
      val hintGraph= new GraphTranslator_hint(simpClauses, GlobalParameters.get.fileName, sortedHints,InitialHintsWithID)
    }


  }






  //}

  //read hints back from file selected by NNs
  //val optimizedHintsByNNs=HintsSelection.readHintsIDFromFile(GlobalParameters.get.fileName,encoder.globalHints,InitialHintsWithID)





  def writeHintsWithIDToFile(wrappedHintList:Seq[wrappedHintWithID],fileName:String,hintType:String){
    val distinctWrappedHintList=wrappedHintList.distinct
    if(hintType=="initial"){
      //val writer = new PrintWriter(new File("trainData/"+fileName+".initialHints"))
      val writer = new PrintWriter(new File("../trainData/"+fileName+".initialHints")) //python path
      for(wrappedHint<-wrappedHintList){
        writer.write(wrappedHint.ID.toString+":"+wrappedHint.head+":"+wrappedHint.hint+"\n")
      }
      writer.close()
    }
    if(hintType=="positive"){
      //val writer = new PrintWriter(new File("trainData/"+fileName+".positiveHints"))
      val writer = new PrintWriter(new File("../trainData/"+fileName+".positiveHints")) //python path
      for(wrappedHint<-wrappedHintList){
        writer.write(wrappedHint.ID.toString+":"+wrappedHint.head+":"+wrappedHint.hint+"\n")
      }
      writer.close()
    }
    if(hintType=="negative"){
      //val writer = new PrintWriter(new File("trainData/"+fileName+".negativeHints"))
      val writer = new PrintWriter(new File("../trainData/"+fileName+".negativeHints")) //python path
      for(wrappedHint<-wrappedHintList){
        writer.write(wrappedHint.ID.toString+":"+wrappedHint.head+":"+wrappedHint.hint+"\n")
      }
      writer.close()
    }

  }







  def initialIDForHints(simpHints:VerificationHints): Seq[wrappedHintWithID] ={
    //var HintsIDMap=Map("initialKey"->"")
    var wrappedHintsList:Seq[wrappedHintWithID]=Seq()
    var HintsIDMap:Map[String,String]=Map()
    var counter=0

    for((head)<-simpHints.getPredicateHints().keys.toList) { //loop for head
      for(oneHint <- simpHints.getValue(head)) { //loop for every template in the head
        HintsIDMap ++= Map(counter.toString+":"+head.name.toString()->oneHint.toString) //map(ID:head->hint)
        counter=counter+1
        val oneWrappedHint=new wrappedHintWithID(counter,head.name.toString,oneHint.toString)
        wrappedHintsList=wrappedHintsList++Seq(oneWrappedHint)
      }
    }
    //HintsIDMap=HintsIDMap-"initialKey"

    return wrappedHintsList

  }






}

/////debug/////
