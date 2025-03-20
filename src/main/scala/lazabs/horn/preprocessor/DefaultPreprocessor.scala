/**
 * Copyright (c) 2016-2025 Philipp Ruemmer. All rights reserved.
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

import lazabs.GlobalParameters
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.global._
import lazabs.horn.Util.Dag

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

/**
 * Default preprocessing pipeline used in Eldarica.
 */
class DefaultPreprocessor extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "default"
  val printWidth = 55
  val clauseNumWidth = 10

  def preStages : List[HornPreprocessor] =
    (if (GlobalParameters.get.slicing) List(ReachabilityChecker) else List()) ++
    List(RationalDenomUnifier,
         new PartialConstraintEvaluator,
         new ConstraintSimplifier,
         new ClauseInliner)

  def extendingStages : List[HornPreprocessor] =
    if (GlobalParameters.get.expandADTArguments)
      List(new HeapSizeArgumentExtender,
           new SizeArgumentExtender,
           new CtorTypeExtender)
    else
      List()

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
    def condenseClauses = {
      var lastSize = -1
      var curSize = curClauses.size
      while (lastSize != curSize) {
        lastSize = curSize
        applyStage(SimplePropagators.EqualityPropagator)
        applyStage(SimplePropagators.ConstantPropagator)
        applyStage(new UniqueConstructorExpander)
        applyStage(new ConstraintSimplifier)
        applyStage(new ClauseInliner)
        if (GlobalParameters.get.slicing) {
          applyStage(ReachabilityChecker)
          applyStage(Slicer)
        }
        curSize = curClauses.size
      }
    }

    val startTime = System.currentTimeMillis

    // First set of processors
    applyStages(preStages)

    condenseClauses

    // check whether any ADT or Heap arguments can be extended
    if (applyStages(extendingStages))
      condenseClauses

    // Possibly split disjunctive clause constraints, and the condense again
    if (GlobalParameters.get.splitClauses >= 1) {
      val oldClauses = curClauses
      applyStage(new BooleanClauseSplitter)
      if (curClauses != oldClauses)
        condenseClauses
    }
    
    // Clone relation symbols with consistently concrete arguments
    {
      val oldClauses = curClauses
      applyStage(SymbolSplitter)
      if (!(curClauses eq oldClauses))
        condenseClauses
    }

    // Clone arrays
    if (GlobalParameters.get.arrayCloning) {
      applyStage(new ArraySplitter)
    }

    // Static acceleration
    if (GlobalParameters.get.staticAccelerate) {
      if (applyStage(Accelerator)) {
        applyStage(new BooleanClauseSplitter)
        condenseClauses
      }
    }

    // Last set of processors
    applyStages(postStages)

    Console.err.println
    Console.err.println("Total preprocessing time (ms): " +
                        (System.currentTimeMillis - startTime))
    Console.err.println

    (curClauses, curHints, new ComposedBackTranslator(translators.reverse))
  }

}
