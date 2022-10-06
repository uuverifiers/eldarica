/**
 * Copyright (c) 2022 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
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
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.{AbstractionRecord, StaticAbstractionBuilder}
import lazabs.horn.abstractions.VerificationHints.VerifHintElement
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.{DagInterpolator, IncrementalHornPredAbs, NormClause, PredicateStore, TemplateInterpolator}
import lazabs.horn.bottomup.Util.{Dag, DagEmpty, DagNode}
import lazabs.horn.preprocessor.DefaultPreprocessor
import lazabs.horn.preprocessor.HornPreprocessor.{BackTranslator, Clauses, ComposedBackTranslator, VerificationHints}

import scala.collection.{immutable, mutable}
import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet}
import scala.util.Random

object InstrumentationLoop {
  class Result
  case class Safe(solution : Map[Predicate, Conjunction]) extends Result
  case class Unsafe(cex : Dag[(IAtom, Clause)]) extends Result
  case object Inconclusive extends Result
}

class InstrumentationLoop (clauses : Clauses,
                           hints : VerificationHints,
                           templateBasedInterpolation : Boolean = false,
                           templateBasedInterpolationTimeout : Long = 2000,
                           templateBasedInterpolationType :
                            StaticAbstractionBuilder.AbstractionType.Value =
                            StaticAbstractionBuilder.AbstractionType.RelationalEqs,
                           globalPredicateTemplates: Map[Predicate, Seq[VerifHintElement]] = Map()) {
  import InstrumentationLoop._

  val backTranslators = new ArrayBuffer[BackTranslator]

  val preprocessor = new DefaultPreprocessor
  var curHints : VerificationHints = hints
  val (simpClauses, newHints1, backTranslator1) =
    Console.withErr(Console.out) {
      preprocessor.process(clauses, curHints)
    }
  curHints = newHints1
  backTranslators += backTranslator1

  println("="*80)
  println("Clauses before instrumentation")
  println("-"*80 )
  clauses.foreach(clause => println(clause.toPrologString))
  println("="*80 + "\n")

  val ghostVarRanges: mutable.Buffer[Int] = (1 to 2).toBuffer

  val instrumenterBackTranslators = new ArrayBuffer[BackTranslator]

  var rawResult : Result = Inconclusive

  var lastSolver : IncrementalHornPredAbs[Clause] = _ // todo :-)
  var lastInstrumenter : SimpleExtendedQuantifierInstrumenter = _

  while (ghostVarRanges.nonEmpty && rawResult == Inconclusive) {
    val numRanges = ghostVarRanges.head
    ghostVarRanges -= numRanges
    instrumenterBackTranslators.clear()

    println("# ghost variable ranges: " + numRanges)
    val instrumenter = new SimpleExtendedQuantifierInstrumenter(
      simpClauses, curHints, Set.empty, numRanges)
    lastInstrumenter = instrumenter

    instrumenterBackTranslators += instrumenter.backTranslator
    curHints = instrumenter.newHints

    println("="*80)
    println("Clauses after instrumentation")
    println("-"*80 )
    instrumenter.instrumentedClauses.foreach(clause => println(clause.toPrologString))
    println("="*80 + "\n")

    //val simpClauses2 = instrumenter.instrumentedClauses

    println("="*80)
    println("Clauses after instrumentation (simplified)")
    val (simpClauses2, newHints2, backTranslator2) =
      Console.withErr(Console.out) {
        preprocessor.process(instrumenter.instrumentedClauses, curHints, instrumenter.branchPredicates)
      }
    curHints = newHints2
    instrumenterBackTranslators += backTranslator2
    simpClauses2.foreach(clause => println(clause.toPrologString))
    println("="*80)


    val interpolator = if (templateBasedInterpolation)
      Console.withErr(Console.out) {
        val builder =
          new StaticAbstractionBuilder(
            simpClauses2,
            templateBasedInterpolationType,
            instrumenter.branchPredicates)
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

            println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

            AbstractionRecord.mergeMaps(autoAbstractionMap, hintsAbstractionMap)
          }

        TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
          abstractionMap,
          templateBasedInterpolationTimeout)
      } else {
      DagInterpolator.interpolatingPredicateGenCEXAndOr _
    }

    def pickInstrumentation(space : Set[Map[Predicate, Conjunction]]) :
    Map[Predicate, Conjunction] = Random.shuffle(space).head

    val incSolver =
      new IncrementalHornPredAbs(simpClauses2,
        curHints.toInitialPredicates,
        instrumenter.branchPredicates,
        interpolator)

    lastSolver = incSolver

    val searchSpace = new MHashSet[Map[Predicate, Conjunction]]
    instrumenter.searchSpace.foreach(search =>
      searchSpace += search.toMap)

    println("Clauses instrumented, starting search for correct instrumentation.")

    var numSteps = 0

    // todo: assume empty instrumentation is in searchSpace?
    while((searchSpace nonEmpty) && rawResult == Inconclusive) {
      numSteps += 1
      val instrumentation = pickInstrumentation(searchSpace.toSet)
      println("\n(" + numSteps + ") Remaining search space size: " + searchSpace.size)
      println("Selected branches: " + instrumentation.map(instr =>
        instr._1.name + "(" + (instr._2.arithConj.positiveEqs.head.constant.intValue * (-1)) + ")").mkString(", "))

      // todo: assuming empty instrumentation is not in searchSpace below
      // left sol, right cex
      incSolver.checkWithSubstitution(instrumentation) match {
        case Right(cex) => {
          // check if cex is genuine
          val cexIsGenuine =
            cex.subdagIterator.toList.head.d._2.bodyPredicates.forall(pred =>
              !(instrumenter.branchPredicates contains pred)
            )

          if (cexIsGenuine) {
            println("\nunsafe")
            rawResult = Unsafe(cex)
          } else {
            println("\ninconclusive, iterating...")
            val prefix = cex.subdagIterator.toList.flatMap(_.d._2.body.filter(
              instrumenter.branchPredicates contains _.pred)).toSet
            val ineligibleSearchSpace = searchSpace.filter {
              search =>
                val atoms: immutable.Iterable[IAtom] =
                  search.map(t => IAtom(t._1, Seq(IExpression.i(
                    t._2.arithConj.positiveEqs.head.constant.intValue * (-1)))))
                prefix.subsetOf(atoms.toSet)
            }
            ineligibleSearchSpace.foreach(s =>
              searchSpace -= s)
          }
        }
        case Left(solution) =>
          rawResult = Safe(solution)
      }
    }
  }

  private val backTranslator =
    new ComposedBackTranslator(
      instrumenterBackTranslators.reverse ++
      backTranslators.reverse)

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
}
