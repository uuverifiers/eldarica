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

import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.parser._
import lazabs.horn.abstractions.{AbstractionRecord, StaticAbstractionBuilder}
import lazabs.horn.bottomup._
import lazabs.horn.concurrency.HintsSelection.initialIDForHints
import lazabs.horn.preprocessor.DefaultPreprocessor
import lazabs.{GlobalParameters, ParallelComputation}

import scala.collection.mutable.ArrayBuffer



/////debug/////
class GraphGenerator(system : ParametricEncoder.System){
  import VerificationLoop._
  val processNum = system.processes.size
  var invariants: Seq[Seq[Int]] =
    for (i <- 0 until processNum)
      yield ((List tabulate processNum) { j => if (i == j) 1 else 0 })

  var res: Either[Unit, Counterexample] = null

  println
  println("Using invariants " + (invariants mkString ", "))
  println


  val encoder: ParametricEncoder = new ParametricEncoder(system, invariants)




  //test JSON reading
  //  println("---debug---")
  //  HintsSelection.readHintsFromJSON("test")
  //  println("---debug---")


  //output all training data

  HintsSelection.writeSMTFormatToFile(encoder)  //write smt2 format to file

  import scala.collection.immutable.ListMap

  if(encoder.globalHints.isEmpty){}else{
    //write selected hints with IDs to file
    val InitialHintsWithID=initialIDForHints(encoder.globalHints) //ID:head->hint
    println("---initialHints-----")
    for ((key,value)<-ListMap(InitialHintsWithID.toSeq.sortBy(_._1):_*)){
      println(key,value)
    }

    val selectedHint=HintsSelection.tryAndTestSelecton(encoder,encoder.globalHints,encoder.allClauses,GlobalParameters.get.fileName,InitialHintsWithID)
    if(selectedHint.isEmpty){ //when no hint available
      //not write horn clauses to file
    }else{
      //write horn clauses to file
      HintsSelection.writeHornClausesToFile(system,GlobalParameters.get.fileName)
      //write smt2 format to file
      if(GlobalParameters.get.fileName.endsWith(".c")){ //if it is a c file
        HintsSelection.writeSMTFormatToFile(encoder)  //write smt2 format to file
      }
      if(GlobalParameters.get.fileName.endsWith(".smt2")){ //if it is a smt2 file
        //copy smt2 file
      }



      //Output graphs
      val hornGraph = new GraphTranslator(encoder.allClauses, GlobalParameters.get.fileName)
      val hintGraph= new GraphTranslator_hint(encoder.allClauses, GlobalParameters.get.fileName, encoder.globalHints)
    }

  }

  //read hints back from file selected by NNs
  //val optimizedHintsByNNs=HintsSelection.readHintsIDFromFile(GlobalParameters.get.fileName,encoder.globalHints,InitialHintsWithID)
}

/////debug/////
