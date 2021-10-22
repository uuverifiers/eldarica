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

import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.parser._
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType
import lazabs.horn.abstractions.{AbstractionRecord, StaticAbstractionBuilder}
import lazabs.horn.bottomup._
import lazabs.horn.concurrency.DrawHornGraph.HornGraphType
import lazabs.horn.concurrency.HintsSelection.{getClausesInCounterExamples, initialIDForHints}
import lazabs.horn.preprocessor.{DefaultPreprocessor, HornPreprocessor}
import lazabs.{GlobalParameters, ParallelComputation}

import scala.collection.mutable.ArrayBuffer



class TrainDataGenerator(smallSystem : ParametricEncoder.System,system : ParametricEncoder.System){
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

  val filePath=GlobalParameters.get.fileName.substring(0,GlobalParameters.get.fileName.lastIndexOf("/")+1)
  //output all training data
  if(GlobalParameters.get.getSMT2==true){
    HintsSelection.writeSMTFormatToFile(encoder.allClauses,filePath)  //write smt2 format to file
    println(encoder.allClauses)
  }
  val simplifiedClausesForGraph = GlobalParameters.get.hornGraphType match {
    case DrawHornGraph.HornGraphType.hyperEdgeGraph | DrawHornGraph.HornGraphType.equivalentHyperedgeGraph | DrawHornGraph.HornGraphType.concretizedHyperedgeGraph => (for(clause<-simpClauses) yield clause.normalize()).asInstanceOf[HornPreprocessor.Clauses]
    case _ => simpClauses
  }

  val sortedHints=HintsSelection.sortHints(simpHints)
  if(sortedHints.isEmpty){}else{
    //write selected hints with IDs to file
    val InitialHintsWithID=initialIDForHints(sortedHints) //ID:head->hint
    println("---initialHints-----")
    for (wrappedHint<-InitialHintsWithID){
      println(wrappedHint.ID.toString,wrappedHint.head,wrappedHint.hint)
    }

    //val selectedHint=HintsSelection.tryAndTestSelecton(encoder,sortedHints,simplifiedClausesForGraph,GlobalParameters.get.fileName,InitialHintsWithID)
    val outStream =
      if (GlobalParameters.get.logStat)
        Console.err
      else
        HornWrapper.NullStream
    val absBuilder = new StaticAbstractionBuilder(simplifiedClausesForGraph, GlobalParameters.get.templateBasedInterpolationType)
    val autoAbstraction: AbstractionMap = absBuilder.abstractionRecords
    val emptyAbsBuilder=new StaticAbstractionBuilder(simplifiedClausesForGraph, AbstractionType.Empty)//could read from coomand line
    val hintsAbstraction=emptyAbsBuilder.loopDetector.hints2AbstractionRecord(simpHints)
    val predGenerator = HintsSelection.getPredGenerator(Seq(hintsAbstraction, autoAbstraction), outStream)
    val (selectedHint,result)=HintsSelection.tryAndTestSelectionTemplates(encoder,sortedHints,simplifiedClausesForGraph,GlobalParameters.get.fileName,InitialHintsWithID,predGenerator,true)
    if(selectedHint.isEmpty){ //when no hint available
      //not write horn clauses to file
    }else{
      //write horn clauses to file
      HintsSelection.writeHornClausesToFile(GlobalParameters.get.fileName,simplifiedClausesForGraph)
      //write smt2 format to file
      if(GlobalParameters.get.fileName.endsWith(".c")){ //if it is a c file
        HintsSelection.writeSMTFormatToFile(simplifiedClausesForGraph,filePath)  //write smt2 format to file
      }
      if(GlobalParameters.get.fileName.endsWith(".smt2")){ //if it is a smt2 file
        //copy smt2 file
      }

      //write argument score to file
      val argumentInfo = HintsSelection.getArgumentLabel(simplifiedClausesForGraph,simpHints,predGenerator,GlobalParameters.get.disjunctive,
        argumentOccurrence = GlobalParameters.get.argumentOccurenceLabel,argumentBound =GlobalParameters.get.argumentBoundLabel)
      val hintsCollection=new VerificationHintsInfo(simpHints,selectedHint,simpHints.filterPredicates(selectedHint.predicateHints.keySet))
      val clausesInCE=getClausesInCounterExamples(result,simplifiedClausesForGraph)
      val clauseCollection = new ClauseInfo(simplifiedClausesForGraph,clausesInCE)

      //Output graphs
      GraphTranslator.drawAllHornGraph(clauseCollection,hintsCollection,argumentInfo)
    }

  }

  //read hints back from file selected by NNs
  //val optimizedHintsByNNs=HintsSelection.readHintsIDFromFile(GlobalParameters.get.fileName,encoder.globalHints,InitialHintsWithID)
}

