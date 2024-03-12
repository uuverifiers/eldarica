/**
 * Copyright (c) 2024 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
 * All rights reserved.
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

package lazabs.horn.extendedquantifiers

import ap.parser.{IAtom, IExpression, IFormula}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.util.Timeout
import lazabs.GlobalParameters
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.{AbstractionRecord, StaticAbstractionBuilder}
import lazabs.horn.abstractions.VerificationHints.VerifHintElement
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.{DagInterpolator, IncrementalHornPredAbs, PredicateStore, TemplateInterpolator}
import lazabs.horn.bottomup.Util.{Dag, DagEmpty, DagNode}
import lazabs.horn.extendedquantifiers.theories.AbstractExtendedQuantifier
import lazabs.horn.preprocessor.DefaultPreprocessor
import lazabs.horn.preprocessor.HornPreprocessor.{BackTranslator, Clauses, ComposedBackTranslator, VerificationHints}

import scala.collection.mutable.{ArrayBuffer, Buffer => MBuffer, HashMap => MHashMap, HashSet => MHashSet}
import scala.util.Random

object InstrumentationLoop {
  class Result
  case class Safe(solution : Map[Predicate, Conjunction]) extends Result
  case class Unsafe(cex : Dag[(IAtom, Clause)]) extends Result
  case object Inconclusive extends Result
}

class InstrumentationLoop (
  clauses                           : Clauses,
  hints                             : VerificationHints,
  extendedQuantifierToInstOp        : Map[AbstractExtendedQuantifier, InstrumentationOperator],
  templateBasedInterpolation        : Boolean = false,
  templateBasedInterpolationTimeout : Long = 2000,
  templateBasedInterpolationType    :
    StaticAbstractionBuilder.AbstractionType.Value =
    StaticAbstractionBuilder.AbstractionType.RelationalEqs,
  globalPredicateTemplates          :
    Map[Predicate, Seq[VerifHintElement]] = Map()) {
  import InstrumentationLoop._

  private val backTranslators = new ArrayBuffer[BackTranslator]

  private val startingTimeout : Long = 250 // milliseconds
  private val timeoutMultiplier : Int = 2
  private val timeoutDecreasemultiplier : Int = 2
  private val minNoTimeouts = 5
  private val maxConsecutiveTimeouts = 10
  private val minTimeout = 25

  private val prefixCompressionPeriod = 50
  private var prefixCompressionCounter = 0

  private val preprocessor = new DefaultPreprocessor
  private var curHints : VerificationHints = hints
  private val (simpClauses, newHints1, backTranslator1) =
    Console.withErr(Console.out) {
      val slicingPre = GlobalParameters.get.slicing
      GlobalParameters.get.slicing = false
      val res = preprocessor.process(clauses, curHints)
      GlobalParameters.get.slicing = slicingPre
      res
    }
  curHints = newHints1
  backTranslators += backTranslator1

//  println("="*80)
//  println("Clauses before instrumentation")
//  println("-"*80 )
//  clauses.foreach(clause => println(clause.toPrologString))
//  println("="*80 + "\n")

  /**
   * TODO: support ghost variable ranges > 1
   */
  private val ghostVarRanges: MBuffer[Int] = (1 to 1).toBuffer
  private var rawResult : Result = Inconclusive
  private val searchSpaceSizePerNumGhostRanges = new MHashMap[Int, Int]
  private val searchStepsPerNumGhostRanges     = new MHashMap[Int, Int]
  private var lastSolver : IncrementalHornPredAbs[Clause]       = _
  private var lastInstrumenter : InstrumentationOperatorApplier = _

  while (ghostVarRanges.nonEmpty && rawResult == Inconclusive) {
    val numRanges = ghostVarRanges.head
    ghostVarRanges -= numRanges

    println("# ghost variable ranges: " + numRanges)
    val instrumenter = new InstrumentationOperatorApplier(
      simpClauses, curHints, Set.empty, extendedQuantifierToInstOp, numRanges)
    lastInstrumenter = instrumenter

    curHints = instrumenter.newHints

//    println("="*80)
//    println("Clauses after instrumentation")
//    println("-"*80 )
//    instrumenter.instrumentedClauses.foreach(clause => println(clause.toPrologString))
//    println("="*80 + "\n")

    //val simpClauses2 = instrumenter.instrumentedClauses

//    println("="*80)
//    println("Clauses after instrumentation (simplified)")

    val outStream =
      if (lazabs.GlobalParameters.get.logStat) Console.err
      else lazabs.horn.bottomup.HornWrapper.NullStream

    val interpolator =
      if (templateBasedInterpolation)
        Console.withErr(outStream) {
          val builder =
            new StaticAbstractionBuilder(
              instrumenter.instrumentedClauses, //simpClauses2,
              templateBasedInterpolationType,
              instrumenter.branchPredicates) //remainingBranchPredicates)
          val autoAbstractionMap =
            builder.abstractionRecords

          val abstractionMap: AbstractionMap =
            if (globalPredicateTemplates.isEmpty) {
              autoAbstractionMap
            } else {
              val loopDetector = builder.loopDetector

              print("Using interpolation templates provided in program: ")

              val hintsAbstractionMap =
                loopDetector hints2AbstractionRecord curHints

              println(
                hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

              AbstractionRecord.mergeMaps(autoAbstractionMap,
                                          hintsAbstractionMap)
            }

          TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
            abstractionMap,
            templateBasedInterpolationTimeout)
        } else {
        DagInterpolator.interpolatingPredicateGenCEXAndOr _
      }

    def computeAtoms(inst : Map[Predicate, Conjunction]) : Set[IAtom] = {
      inst.map{t =>
        IAtom(t._1, Seq(IExpression.i(
          t._2.arithConj.positiveEqs.head.constant.intValue *
          (-1))))
      }.toSet
    }

    def pickInstrumentation(space : Set[Map[Predicate, Conjunction]],
                            ineligiblePrefixes : Set[Set[IAtom]]) :
    Option[Map[Predicate, Conjunction]] = {
      var candidate : Option[Map[Predicate, Conjunction]] = None
      for (inst <- space if candidate isEmpty) {
        val instAtoms = computeAtoms(inst)
        if (ineligiblePrefixes.exists(prefix => prefix subsetOf instAtoms)) {
          // nothing
        } else candidate = Some(inst)
      }
      candidate
    }

    val incSolver =
      new IncrementalHornPredAbs(
        instrumenter.instrumentedClauses,
        curHints.toInitialPredicates,
        instrumenter.branchPredicates,
        interpolator)

    lastSolver = incSolver

    Random.setSeed(42)
    val searchSpace = new MHashSet[Map[Predicate, Conjunction]]
    Random.shuffle(instrumenter.searchSpace).foreach { search =>
      searchSpace += search.toMap
    }

    val postponedSearches = new MHashSet[Map[Predicate, Conjunction]]

    val ineligiblePrefixes = new MHashSet[Set[IAtom]]

    searchSpaceSizePerNumGhostRanges += (numRanges -> searchSpace.size)
    println("Clauses instrumented, starting search for correct instrumentation.")

    var numSteps = 0
    searchStepsPerNumGhostRanges += (numRanges -> numSteps)

    var currentTimeout = startingTimeout

    var noTimeoutCount = 0
    var consecutiveTimeoutCount = 0

    var totalExplored = 0

    while(rawResult == Inconclusive && (searchSpace.nonEmpty ||
                                        postponedSearches.nonEmpty)) {

      if (searchSpace.isEmpty && postponedSearches.nonEmpty) {
        postponedSearches.foreach(searchSpace += _)
        postponedSearches.clear()
        currentTimeout *= timeoutMultiplier
        println("Retrying postponed instrumentations with new timeout: " +
                currentTimeout / 1e3)
      }

      var prevI = 0
      for ((instrumentation, i) <- searchSpace.toSeq.zipWithIndex
           if rawResult == Inconclusive && ineligiblePrefixes.forall(prefix =>
             !(prefix subsetOf computeAtoms (instrumentation)))) {
        numSteps += 1
        searchStepsPerNumGhostRanges += (numRanges -> numSteps)
//      val instrumentation = pickInstrumentation(searchSpace.toSet,
//                                                ineligiblePrefixes.toSet)

      println("\n(" + numSteps + ") Remaining search space size: " +
              (instrumenter.searchSpace.size - totalExplored - postponedSearches.size))
        println("Postponed instrumentations : " + postponedSearches.size)
        println("Selected branches: " + instrumentation.map{instr =>
          instr._1.name + "(" + (instr._2.arithConj.positiveEqs.head.constant.
                                      intValue * (-1)) + ")"}.mkString(", "))

        // assuming empty instrumentation is not in searchSpace below
        val maybeRes =
          Timeout.withTimeoutMillis[Option[Either[Map[Predicate, Conjunction],
            Dag[(IAtom, Clause)]]]](currentTimeout){
            // computation
            Some(incSolver.checkWithSubstitution(instrumentation))
          }{
            // timeout computation
            None
          }

        maybeRes match {
          case Some(res) =>
            totalExplored += i - prevI; prevI = i;
            res match { // no timeout
            case Right(cex)     => {
              // check if cex is genuine
              val cexIsGenuine =
                cex.subdagIterator.toList.head.d._2.bodyPredicates.forall(
                  pred => !(instrumenter.branchPredicates contains pred))
              if (cexIsGenuine) {
                println("\nunsafe")
                rawResult = Unsafe(cex)
              } else {
                noTimeoutCount += 1
                consecutiveTimeoutCount = 0
                println("\ninconclusive, iterating...")
                val prefix : Set[IAtom] = cex.subdagIterator.toList.flatMap(_.d
                                                                             ._2.body.filter(
                  instrumenter.branchPredicates contains _.pred)).toSet

                prefixCompressionCounter += 1
                ineligiblePrefixes += prefix

                if (prefixCompressionCounter >= prefixCompressionPeriod) {
                  prefixCompressionCounter = 0

                  val redundantPrefixes =
                    for (prefix <- ineligiblePrefixes if
                      ineligiblePrefixes.filter(_.size < prefix.size).
                                        exists(other => other subsetOf prefix))
                    yield prefix
                  val beforeSize        = ineligiblePrefixes.size
                  redundantPrefixes.foreach(ineligiblePrefixes -=)
                  println("Compressed ineligible prefixes: " + beforeSize +
                          " to " + ineligiblePrefixes.size)
                }
              }
            }
            case Left(solution) =>
              rawResult = Safe(solution)
          }
          case None => // timeout
            println("Instrumentation timed out and postponed.")
            searchSpace -= instrumentation
            postponedSearches += instrumentation
            noTimeoutCount = 0
            consecutiveTimeoutCount += 1
        }

        if (noTimeoutCount > minNoTimeouts) {
          // decrease timeout, nothing is timing out
          noTimeoutCount = 0
          currentTimeout /= timeoutDecreasemultiplier
          if (currentTimeout < minTimeout)
            currentTimeout = minTimeout
          println("Too many steps without timeouts, decreasing to " +
                  currentTimeout / 1e3)
        }
        if (consecutiveTimeoutCount > maxConsecutiveTimeouts) {
          // too many timeouts, bump it up
          consecutiveTimeoutCount = 0
          currentTimeout *= timeoutMultiplier
          println("Too many consecutive timeouts, increasing to " +
                  currentTimeout / 1e3)
        }
      }
      searchSpace.clear()
    }
  }

  private val backTranslator =
    new ComposedBackTranslator(
      Seq(lastInstrumenter.backTranslator) ++ backTranslators.reverse)

  /**
   * The result of CEGAR: either a solution of the Horn clauses, or
   * a counterexample DAG containing the predicates and clauses.
   */
  lazy val result : Either[Map[Predicate, IFormula],
    Dag[(IAtom, Clause)]] = rawResult match {
    case Safe(solution) =>
      val solF = for ((p, c) <- solution)
        yield {
          (p, (new PredicateStore(lastSolver.baseContext)).convertToInputAbsy(
            p, List(c)).head)
        }
      Left(backTranslator.translate(solF))
    case Unsafe(trace) =>
      Right(backTranslator.translate(trace))
    case Inconclusive =>
      Right(DagEmpty)
  }
  /**
   * Search space size per number of ghost ranges used, will only contain
   * the sizes for used number of ghost ranges. Must be called after result.
   */
  lazy val totalSearchSpaceSizesPerNumGhostRanges : Map[Int, Int] =
    searchSpaceSizePerNumGhostRanges.toMap
  /**
   * Total number of steps taken until reaching the result at every
   * "numGhostRange". Must be called after result.
   */
  lazy val totalSearchStepsPerNumGhostRanges      : Map[Int, Int] =
    searchStepsPerNumGhostRanges.toMap

}
