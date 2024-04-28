/**
 * Copyright (c) 2016-2023 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.preprocessor

import ap.parser._
import IExpression._
import ap.theories.Heap
import lazabs.GlobalParameters
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.Clause

import scala.collection.mutable.ArrayBuffer

/**
 * Default preprocessing pipeline used in Eldarica.
 */
class DefaultPreprocessor extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "default"
  val printWidth = 55
  val clauseNumWidth = 10

  val printingEnabled = GlobalParameters.get.printHornSimplified ||
    GlobalParameters.get.printHornSimplifiedSMT

  def preStages : List[HornPreprocessor] =
    (if (GlobalParameters.get.slicing)
       List(ReachabilityChecker) else List()) ++
    List(new PartialConstraintEvaluator,
         new ConstraintSimplifier,
         RationalDenomUnifier,
         new ClauseInliner)

  def extendingStages : List[HornPreprocessor] = {
    (if (GlobalParameters.get.expandHeapArguments) {
      (if (printingEnabled) List() else List(
        new HeapSizeArgumentExtender
        ))
    } else List()) ++
      (if (GlobalParameters.get.expandADTArguments) {
        List(new SizeArgumentExtender) ++
          (if (printingEnabled) List() else List(new CtorTypeExtender))
      } else List())
  }

  def postStages : List[HornPreprocessor] =
    List(new ClauseShortener) ++
    (if (GlobalParameters.get.splitClauses >= 2)
      List(new ClauseSplitter) else List()) ++
    (GlobalParameters.get.finiteDomainPredBound match {
       case n if n <= 0 => List()
       case n           => List(new FiniteDomainPredicates (n))
     })

  def process(clauses : Clauses, hints : VerificationHints,
              frozenPredicates : Set[Predicate])
             : (Clauses, VerificationHints, BackTranslator) = {
    var curClauses = clauses
    var curHints = hints

    def printStats(prefix : String) : Unit = {
      val predNum = (HornClauses allPredicates curClauses).size
      val clauseNumStr = "" + curClauses.size
      Console.err.println(prefix + (" " * (printWidth - prefix.size)) +
                          clauseNumStr +
                            (" " * (clauseNumWidth - clauseNumStr.size)) +
                          predNum)
    }

    Console.err.println
    Console.err.println(
         "------------------------------- Preprocessing ----------------------------------")
   
    Console.err.println((" " * printWidth) + "#clauses  #relation syms")
    printStats("Initially:")

    val translators = new ArrayBuffer[BackTranslator]

    def applyStage(stage : HornPreprocessor) : Boolean =
      if (!curClauses.isEmpty &&
            stage.isApplicable(curClauses, frozenPredicates)) {
        GlobalParameters.get.timeoutChecker()

        val startTime = System.currentTimeMillis

        val (newClauses, newHints, translator) =
          stage.process(curClauses, curHints, frozenPredicates)

//        println("=" * 80)
//        if(curClauses != newClauses) {
//          println("(Only showing diff)")
//          println(s"Before ${stage.name} (${curClauses.size} clauses)")
//          println(curClauses.diff(newClauses).sortBy(c => c.head.pred.name + c.body)
//                    .map(c => c.toPrologString).mkString("\n"))
//          println("-" * 80)
//          println(s"After  ${stage.name} (${newClauses.size} clauses)")
//          println(newClauses.diff(curClauses).sortBy(c => c.head.pred.name + c.body)
//                    .map(c => c.toPrologString).mkString("\n"))
//        } else {
//          println(s"${stage.name} did not change the clauses")
//        }
//        println("=" * 80)
        curClauses = newClauses
        curHints = newHints

        val time = "" + (System.currentTimeMillis - startTime) + "ms"
        printStats("After " + stage.name + " (" + time + "):")

        translators += translator

        true
      } else {
        false
      }

    def applyStages(stages : Iterable[HornPreprocessor]) : Boolean = {
      var applied = false
      for (s <- stages)
        applied = applyStage(s) || applied
      applied
    }

    // Apply clause simplification and inlining repeatedly, if necessary
    def condenseClauses(applySlicing : Boolean = true,
                        applyInlining : Boolean = false,
                        applyHeapSimp : Boolean = true) = {
      var lastSize = -1
      var curSize = curClauses.size
      while (lastSize != curSize) {
        lastSize = curSize
        applyStage(SimplePropagators.EqualityPropagator)
        applyStage(SimplePropagators.ConstantPropagator)
        applyStage(new UniqueConstructorExpander)
        applyStage(new ConstraintSimplifier)
        if (applyInlining) {
          applyStage(new ClauseInliner)
        }
        if (GlobalParameters.get.slicing && applySlicing) {
          applyStage(ReachabilityChecker)
          applyStage(Slicer)
        }
        if (applyHeapSimp) {
          var lastClauses : Set[Clause] = Set()
          while (lastClauses != curClauses.toSet) {
            lastClauses = curClauses.toSet
            applyStage(new IntraClauseReadWriteEliminator)
            applyStage(new ConstraintSimplifier)
          }
        }

        curSize = curClauses.size
      }
    }

    val startTime = System.currentTimeMillis

    // First set of processors
    applyStages(preStages)

//    println("Before analysis")
//    println(curClauses.sortBy(c => c.head.pred.name + c.body)
//              .map(c => c.toPrologString).mkString("\n"))

//    println("After analysis")
//    println(curClauses.sortBy(c => c.head.pred.name + c.body)
//              .map(c => c.toPrologString).mkString("\n"))

    //      println("After normalization")
    //      println(curClauses.sortBy(c => c.head.pred.name + c.body)
    //                .map(c => c.toPrologString).mkString("\n"))
    //
    condenseClauses(true, true)
    //
    //      println("After inlining back")
    //      println(curClauses.sortBy(c => c.head.pred.name + c.body)
    //                .map(c => c.toPrologString).mkString("\n"))

    //      System.exit(0)

    if(GlobalParameters.get.heapInvariantEncoding) {

      condenseClauses(!GlobalParameters.get.heapInvariantEncoding)

      if (lazabs.GlobalParameters.get.heapInvariantEncoding ||
        lazabs.GlobalParameters.get.eliminateHeaps) {

        val updateSiteTagger = new HeapUpdateSiteTagger
        applyStage(updateSiteTagger)

        val heapTheories1         = curClauses.flatMap(
          _.theories.filter(_.isInstanceOf[Heap]).map(_.asInstanceOf[Heap]))
          .toSet
        val heapFunctionSplitters = for (heap <- heapTheories1) yield {
          val funs        = Set(heap.allocHeap, heap.write, heap.read)
          val funOrdering = new Ordering[IFunction] {
            def compare(a : IFunction, b : IFunction) : Int = {
              // Assign each function a priority
              def priority(fun : IFunction) : Int = fun match {
                case heap.emptyHeap => 1
                case heap.read => 2
                case heap.allocHeap => 3
                case heap.allocAddr => 3
                case heap.write => 4
                case _ => 0 // Any other function gets highest priority
              }

              // Use the priorities to compare two functions
              priority(a) compare priority(b)
            }
          }
          new ClauseSplitterFuncsAndUnboundTerms(funs.toSet,
                                                 heap.functions.toSet,
                                                 Set(heap.HeapSort),
                                                 "glue1",
                                                 Some(funOrdering))
        }
        applyStages(List(new EquationUninliner) ++ heapFunctionSplitters)

        // todo: note that HeapAddressUpdateSitePropagator is currently unsound!
        //  its static analysis should be fixed, see the one in IntraClauseReadWriteEliminator
//        applyStage(SimplePropagators.HeapAddressUpdateSitePropagator(updateSiteTagger.getUpdateSiteIds))
        applyStage(new HeapUpdateSitesTagSetAnalysis)

        condenseClauses(applyHeapSimp = false)
//
//              println("After condensing")
//              println(curClauses.sortBy(c => c.head.pred.name + c.body)
//                        .map(c => c.toPrologString).mkString("\n"))

//        val heapTheories2 = curClauses.flatMap(
//          _.theories.filter(_.isInstanceOf[Heap]).map(_.asInstanceOf[Heap]))
//          .toSet
//
//        val heapFunctionSplitters2 = for (heap <- heapTheories2) yield {
//          val funs        = Set(heap.allocHeap, heap.write, heap.read)
//          val funOrdering = new Ordering[IFunction] {
//            def compare(a : IFunction, b : IFunction) : Int = {
//              // Assign each function a priority
//              def priority(fun : IFunction) : Int = fun match {
//                case heap.emptyHeap => 1
//                case heap.read => 2
//                case heap.allocHeap => 3
//                case heap.allocAddr => 3
//                case heap.write => 4
//                case _ => 0 // Any other function gets highest priority
//              }
//
//              // Use the priorities to compare two functions
//              priority(a) compare priority(b)
//            }
//          }
//          new ClauseSplitterFuncsAndUnboundTerms(funs.toSet, Set(heap.HeapSort),
//                                                 "_glue1",
//                                                 Some(funOrdering))
//        }
//        applyStages(List(new EquationUninliner) ++ heapFunctionSplitters2)

        applyStage(new HeapInvariantEncoding)
          //        println("After adding heap invariants")
          //        println(curClauses.sortBy(c => c.head.pred.name + c.body)
//                  .map(c => c.toPrologString).mkString("\n"))

        condenseClauses(true, true)

        if(lazabs.GlobalParameters.get.eliminateHeaps) {
          applyStage(new HeapEliminator)
        }
        //        println
        //        println(curClauses.sortBy(c => c.head.pred.name + c.body)
        //                  .map(c => c.toPrologString).mkString("\n"))
//        println("After analysis1")
//        println(curClauses.sortBy(c => c.head.pred.name + c.body)
//                  .map(c => c.toPrologString).mkString("\n"))
        condenseClauses(true, true)
//        println("After analysis2")
//        println(curClauses.sortBy(c => c.head.pred.name + c.body)
//                  .map(c => c.toPrologString).mkString("\n"))
      }
    }

//    println("After adding heap invariants")
//    println(curClauses.sortBy(c => c.head.pred.name + c.body).map(c => c.toPrologString).mkString("\n"))

    // check whether any ADT or Heap arguments can be extended
    if (!printingEnabled && applyStages(extendingStages))
      condenseClauses(true, true)

    // Possibly split disjunctive clause constraints, and the condense again
    if (!printingEnabled && GlobalParameters.get.splitClauses >= 1) {
      val oldClauses = curClauses
      applyStage(new BooleanClauseSplitter)
      if (curClauses != oldClauses)
        condenseClauses(true, true)
    }
    
    // Clone relation symbols with consistently concrete arguments
    {
      val oldClauses = curClauses
      applyStage(SymbolSplitter)
      if (!(curClauses eq oldClauses))
        condenseClauses(true, true)
    }

    // Clone arrays
    if (GlobalParameters.get.arrayCloning) {
      applyStage(new ArraySplitter)
    }

    // Static acceleration
    if (GlobalParameters.get.staticAccelerate) {
      if (applyStage(Accelerator)) {
        applyStage(new BooleanClauseSplitter)
        condenseClauses(true, true)
      }
    }

    // Last set of processors
    applyStages(postStages)

    Console.err.println
    Console.err.println("Total preprocessing time (ms): " +
                        (System.currentTimeMillis - startTime))
    Console.err.println

//    println("Final clauses after all preprocessing")
//    println(curClauses.sortBy(c => c.head.pred.name + c.body)
//              .map(c => c.toPrologString).mkString("\n"))

    (curClauses, curHints, new ComposedBackTranslator(translators.reverse))
  }

}
