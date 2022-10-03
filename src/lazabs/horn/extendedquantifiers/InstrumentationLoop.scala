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

import ap.parser.{IAtom, IFormula}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.{IncrementalHornPredAbs, NormClause, PredicateStore}
import lazabs.horn.bottomup.Util.{Dag, DagEmpty}
import lazabs.horn.preprocessor.DefaultPreprocessor
import lazabs.horn.preprocessor.HornPreprocessor.{BackTranslator, Clauses, ComposedBackTranslator}

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet}
import scala.util.Random

object InstrumentationLoop {
  class Result
  case class Safe(solution : Map[Predicate, Conjunction]) extends Result
  case class Unsafe(cex : Dag[(IAtom, Clause)]) extends Result
  case object Inconclusive extends Result
}

class InstrumentationLoop (clauses : Clauses,
                           initialPredicates : Map[Predicate, Seq[IFormula]],
                           predicateGenerator : Dag[AndOrNode[NormClause, Unit]] =>
                             Either[Seq[(Predicate, Seq[Conjunction])],
                               Dag[(IAtom, NormClause)]]) {
  import InstrumentationLoop._

  val backTranslators = new ArrayBuffer[BackTranslator]

  val preprocessor = new DefaultPreprocessor
  val (simpClauses, _, backTranslator1) =
    Console.withErr(Console.out) {
      preprocessor.process(clauses, EmptyVerificationHints)
    }
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

  while (ghostVarRanges.nonEmpty && rawResult == Inconclusive) {
    val numRanges = ghostVarRanges.head
    ghostVarRanges -= numRanges
    instrumenterBackTranslators.clear()

    println("# ghost variable ranges: " + numRanges)
    val instrumenter = new SimpleExtendedQuantifierInstrumenter(
    simpClauses, EmptyVerificationHints, Set.empty, numRanges)

    instrumenterBackTranslators += instrumenter.backTranslator

    println("="*80)
    println("Clauses after instrumentation")
    println("-"*80 )
    instrumenter.instrumentedClauses.foreach(clause => println(clause.toPrologString))
    println("="*80 + "\n")

    //val simpClauses2 = instrumenter.instrumentedClauses

    println("="*80)
    println("Clauses after instrumentation (simplified)")
    val (simpClauses2, _, backTranslator2) =
      Console.withErr(Console.out) {
        preprocessor.process(instrumenter.instrumentedClauses, EmptyVerificationHints, instrumenter.branchPredicates)
      }
    instrumenterBackTranslators += backTranslator2
    simpClauses2.foreach(clause => println(clause.toPrologString))
    println("="*80)

    // orders the space with decreasing order on the number of instrumented clauses
    // then randomly picks one instrumentation from the first group
    // i.e., we try first instrumenting everything, then eliminate some branches
    def pickInstrumentation(space : Set[Map[Predicate, Conjunction]]) :
    Map[Predicate, Conjunction] = Random.shuffle(space).head

    val incSolver =
      new IncrementalHornPredAbs(simpClauses2,
        initialPredicates,
        instrumenter.branchPredicates,
        predicateGenerator)

    lastSolver = incSolver

    // we have m predicates for m locations to instrument, corresponding to the instrumentation constraint.
    // each instrumentation predicate can be instantiated in n ways
    // i.e., the search space is n^m.
    // for the base case, we will have n = 2, with {instrument, noInstrument}, so the search space is 2^m

    val searchSpace = new MHashSet[Map[Predicate, Conjunction]]
    instrumenter.searchSpace.foreach(search =>
      searchSpace += search.toMap)

    println("Clauses instrumented, starting search for correct instrumentation.")

    // todo: assume empty instrumentation is in searchSpace?
    while((searchSpace nonEmpty) && rawResult == Inconclusive) {
      val instrumentation = pickInstrumentation(searchSpace.toSet)
      println("Remaining search space size: " + searchSpace.size)
      println("Selected branches: " + instrumentation.map(instr =>
        instr._1.name + "(" + (instr._2.arithConj.positiveEqs.head.constant.intValue * (-1)) + ")").mkString(", "))

      // todo: assuming empty instrumentation is not in searchSpace below
      // left sol, right cex
      incSolver.checkWithSubstitution(instrumentation) match {
        case Right(cex) => {
          println("unsafe, iterating...")
          searchSpace -= instrumentation // todo; very stupid implementation that only removes the last instrumentation
          //backTranslator.translate(cex).prettyPrint
          // rawResult = Unsafe(cex)
        }
        case Left(solution) =>
          rawResult = Safe(solution)
      }
    }
  }

  val backTranslator =
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
      Left(for ((p, c) <- solution)
        yield {
          (p, (new PredicateStore(lastSolver.baseContext)).convertToInputAbsy(
            p, List(c)).head)
        })
    case Unsafe(trace) =>
      Right(trace)
    case Inconclusive =>
      Right(DagEmpty)
  }

}
