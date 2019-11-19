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

import lazabs.GlobalParameters
import lazabs.horn.concurrency.HintsSelection.initialIDForHints
import lazabs.horn.preprocessor.DefaultPreprocessor

import scala.collection.immutable.ListMap
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
  val initialPredicates=HintsSelection.getInitialPredicates(encoder,simpHints,simpClauses)

  val sortedHints=HintsSelection.sortHints(initialPredicates)
  if(sortedHints.isEmpty){}else{
    //write selected hints with IDs to file
    val InitialHintsWithID=initialIDForHints(sortedHints) //ID:head->hint
    println("---initialHints-----")
    for ((key,value)<-ListMap(InitialHintsWithID.toSeq.sortBy(_._1):_*)){
      println(key,value)
    }
    val selectedHint=HintsSelection.tryAndTestSelectionPredicate(encoder,simpHints,simpClauses,GlobalParameters.get.fileName,InitialHintsWithID)
//    inv_main8/4
//    VerifHintInitPred(((_1 + -1 * _0) >= 0))
//    VerifHintInitPred(((-1 * _2 + _0) >= 0))
//    VerifHintInitPred(((-1 * _2 + _1) >= 0))
//    VerifHintInitPred(((-1 * _3 + _0) >= 0))
//    VerifHintInitPred(((-1 * _3 + _1) >= 0))
//    VerifHintInitPred(((-1 * _3 + _2) >= 0))
//    VerifHintInitPred(((-1 + (2 * _2 + (4 * _1 + _0))) = 0))
//    VerifHintInitPred(((-1 + (2 * _3 + (2 * _2 + (2 * _1 + _0)))) = 0))
//    VerifHintInitPred(((-1 + (4 * _2 + (2 * _1 + _0))) = 0))
//    VerifHintInitPred(((-1 + (4 * _3 + (4 * _2 + (4 * _1 + _0)))) = 0))
//    VerifHintInitPred(((-13 + (3 * _3 + (3 * _2 + (3 * _1 + _0)))) = 0))
//    VerifHintInitPred(((-21 + (2 * _3 + (2 * _2 + (2 * _1 + _0)))) = 0))
//    VerifHintInitPred(((-25 + (_3 + (_2 + (_1 + _0)))) = 0))
//    VerifHintInitPred(((-5 + (_3 + (_2 + (_1 + _0)))) = 0))
//    VerifHintInitPred(((1 + (2 * _3 + (-2 * _1 + -1 * _0))) = 0))
//    VerifHintInitPred(((1 + (2 * _3 + (-2 * _2 + -1 * _0))) = 0))
//    VerifHintInitPred(((3 + (_3 + (-1 * _2 + (-3 * _1 + -1 * _0)))) = 0))
//    VerifHintInitPred(((3 + (_3 + (-3 * _2 + (-1 * _1 + -1 * _0)))) = 0))
//    VerifHintInitPred(((_2 + -1 * _0) >= 0))
//    VerifHintInitPred(((_2 + -1 * _1) >= 0))
//    VerifHintInitPred(((_3 + (-1 * _2 + -1 * _1)) = 0))
//    VerifHintInitPred(((_3 + -1 * _0) >= 0))
//    VerifHintInitPred(((_3 + -1 * _1) >= 0))
//    VerifHintInitPred(((_3 + -1 * _2) >= 0))
//    VerifHintInitPred(EX ((-3 + (4 * _0 + (3 * _4 + (-1 * _3 + (_2 + -3 * _1))))) = 0))
//    VerifHintInitPred(EX ((-3 + (4 * _0 + (3 * _4 + (_3 + (-1 * _2 + -3 * _1))))) = 0))
//    VerifHintInitPred(EX ((1 + (2 * _0 + (-1 * _4 + (_3 + (-1 * _2 + _1))))) = 0))


    //val selectedHint=HintsSelection.tryAndTestSelecton(encoder,sortedHints,simpClauses,GlobalParameters.get.fileName,InitialHintsWithID,predicateFlag =false)

//    inv_main8/4
//    VerifHintInitPred(((-1 * _1 + _0) >= 0))
//    VerifHintInitPred(((-1 * _2 + _0) >= 0))
//    VerifHintInitPred(((-1 * _2 + _1) >= 0))
//    VerifHintInitPred(((-1 * _3 + _0) >= 0))
//    VerifHintInitPred(((-1 * _3 + _1) >= 0))
//    VerifHintInitPred(((-1 * _3 + _2) >= 0))
//    VerifHintInitPred(((-1 + (2 * _2 + (4 * _1 + _0))) = 0))
//    VerifHintInitPred(((-1 + (2 * _3 + (2 * _2 + (2 * _1 + _0)))) = 0))
//    VerifHintInitPred(((-1 + (4 * _2 + (2 * _1 + _0))) = 0))
//    VerifHintInitPred(((-1 + (4 * _3 + (4 * _2 + (4 * _1 + _0)))) = 0))
//    VerifHintInitPred(((-13 + (3 * _3 + (3 * _2 + (3 * _1 + _0)))) = 0))
//    VerifHintInitPred(((-21 + (2 * _3 + (2 * _2 + (2 * _1 + _0)))) = 0))
//    VerifHintInitPred(((-25 + (_3 + (_2 + (_1 + _0)))) = 0))
//    VerifHintInitPred(((-5 + (_3 + (_2 + (_1 + _0)))) = 0))
//    VerifHintInitPred(((1 + (2 * _3 + (-2 * _1 + -1 * _0))) = 0))
//    VerifHintInitPred(((1 + (2 * _3 + (-2 * _2 + -1 * _0))) = 0))
//    VerifHintInitPred(((3 + (_3 + (-1 * _2 + (-3 * _1 + -1 * _0)))) = 0))
//    VerifHintInitPred(((3 + (_3 + (-3 * _2 + (-1 * _1 + -1 * _0)))) = 0))
//    VerifHintInitPred(((_1 + -1 * _0) >= 0))
//    VerifHintInitPred(((_2 + -1 * _0) >= 0))
//    VerifHintInitPred(((_2 + -1 * _1) >= 0))
//    VerifHintInitPred(((_3 + (-1 * _2 + -1 * _1)) = 0))
//    VerifHintInitPred(((_3 + -1 * _0) >= 0))
//    VerifHintInitPred(((_3 + -1 * _1) >= 0))
//    VerifHintInitPred(((_3 + -1 * _2) >= 0))
//    VerifHintInitPred(EX ((-3 + (4 * _0 + (3 * _4 + (-1 * _3 + (_2 + -3 * _1))))) = 0))
//    VerifHintInitPred(EX ((-3 + (4 * _0 + (3 * _4 + (_3 + (-1 * _2 + -3 * _1))))) = 0))
//    VerifHintInitPred(EX ((1 + (2 * _0 + (-1 * _4 + (_3 + (-1 * _2 + _1))))) = 0))



    if(selectedHint.isEmpty){ //when no hint available
      //not write horn clauses to file
    }else{
      //write horn clauses to file
      HintsSelection.writeHornClausesToFile(smallSystem,GlobalParameters.get.fileName)
      //write smt2 format to file
      if(GlobalParameters.get.fileName.endsWith(".c")){ //if it is a c file
        HintsSelection.writeSMTFormatToFile(simpClauses,"../trainData/")  //write smt2 format to file
      }
      if(GlobalParameters.get.fileName.endsWith(".smt2")){ //if it is a smt2 file
        //copy smt2 file
      }

      //Output graphs
      val hornGraph = new GraphTranslator(simpClauses, GlobalParameters.get.fileName)
      val hintGraph= new GraphTranslator_hint(simpClauses, GlobalParameters.get.fileName, sortedHints)
    }

  }

  //read hints back from file selected by NNs
  //val optimizedHintsByNNs=HintsSelection.readHintsIDFromFile(GlobalParameters.get.fileName,encoder.globalHints,InitialHintsWithID)
}

/////debug/////
