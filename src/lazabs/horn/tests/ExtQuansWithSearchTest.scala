/**
 * Copyright (c) 2022 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.tests

import ap.parser.IExpression.Predicate
import ap.parser._
import ap.terfor.arithconj.ArithConj
import ap.theories._
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.bottomup._
import lazabs.horn.preprocessor.DefaultPreprocessor
import ap.terfor.conjunctions.Conjunction
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.preprocessor.HornPreprocessor.ComposedBackTranslator
import lazabs.horn.preprocessor.extendedquantifiers.{Normalizer, SimpleExtendedQuantifierInstrumenter}

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap, HashSet => MHashSet}

object ExtQuansWithSearchTest extends App {

  class Result
  case class Safe(solution : Map[Predicate, Conjunction]) extends Result
  case class Unsafe(cex : Dag[(IAtom, Clause)]) extends Result
  case object Inconclusive extends Result

  import HornClauses._
  import IExpression._
  import lazabs.horn.preprocessor.extendedquantifiers.ExtendedQuantifier

  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)

  val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)

  def sum (a : ITerm, b : ITerm) : ITerm = a + b
  def invSum (a : ITerm, b : ITerm) : ITerm = a - b
  val extQuan = new ExtendedQuantifier("sum", ar, i(0), sum, Some(invSum))
  TheoryRegistry.register(extQuan)

  {
    val a1 = new SortedConstantTerm("a1", ar.sort)
    val a2 = new SortedConstantTerm("a2", ar.sort)
    val i = new ConstantTerm("i")
    val s = new ConstantTerm("s")
    val o = new SortedConstantTerm("o",ar.objSort)
    val o2 = new SortedConstantTerm("o'",ar.objSort)


    val p = for (i <- 0 until 5) yield (new MonoSortedPredicate("p" + i,
      Seq(ar.sort, ar.sort, Sort.Integer)))

     //SELECT (read)
    val clauses = List(
      p(0)(a1, a2, i)  :- (i === 0),
      p(0)(a1, a2, i + 1) :- (p(0)(a1, a2, i), 3 === ar.select(a1, i),
                                               4 === ar.select(a2, i), i < 10),
      p(1)(a1, a2, i)     :- (p(0)(a1, a2, i), i >= 10),
      false          :- (p(1)(a1, a2, i),
                        extQuan.fun(a1, 0, 10) =/= 30) // right-open interval
    )

//    // STORE (write)

//    val clauses = List(
//      p(0)(a, i)     :- (i === 0),
//      p(0)(ar.store(a, i, 3), i + 1) :- (p(0)(a, i), i < 10),
//      p(1)(a, i)     :- (p(0)(a, i), i >= 10),
//      false          :- (p(1)(a, i),
//        extQuan.fun(a, 0, 10) =/= 30) // right-open interval
//    )

//    def max (a : ITerm, b : ITerm) : ITerm = IExpression.ite(a >= b, a, b)
//    val extQuanMax = new ExtendedQuantifier("max", ar.objSort, max, None)
//    TheoryRegistry.register(extQuanMax)
//
////    SELECT (read) - unsafe
//        val clauses = List(
//          p(0)(a, i)     :- (i === 0),
//          p(0)(a, i + 1) :- (p(0)(a, i), o === ar.select(a, i), i < 10),
//          p(1)(a, i)     :- (p(0)(a, i), i >= 10),
//          false          :- (p(1)(a, i),
//                          extQuanMax.fun(a, 0, 10) <= 30) // right-open interval
//        )

    val preprocessor = new DefaultPreprocessor
    val (simpClauses, _, backTranslator1) =
      Console.withErr(Console.out) {
        preprocessor.process(clauses, EmptyVerificationHints)
      }

    println("="*80)
    println("Clauses before instrumentation")
    println("-"*80 )
    clauses.foreach(clause => println(clause.toPrologString))
    println("="*80 + "\n")

    val instrumenter = new SimpleExtendedQuantifierInstrumenter(
      simpClauses, EmptyVerificationHints, Set.empty)

    println("="*80)
    println("Clauses after instrumentation")
    println("-"*80 )
    instrumenter.instrumentedClauses.foreach(clause => println(clause.toPrologString))
    println("="*80 + "\n")

    val simpClauses2 = instrumenter.instrumentedClauses

//    println("="*80)
//    println("Clauses after instrumentation (simplified)")
//    val (simpClauses2, _, backTranslator2) =
//      Console.withErr(Console.out) {
//        preprocessor.process(instrumenter.instrumentedClauses, EmptyVerificationHints)
//      }
//    simpClauses2.foreach(clause => println(clause.toPrologString))
//    println("="*80)

    def pickInstrumentation(space : Set[Map[Predicate, Conjunction]]) :
      Map[Predicate, Conjunction] = space.last

    val incSolver =
      new IncrementalHornPredAbs(simpClauses2,
        Map(),
        instrumenter.branchPredicates,
        DagInterpolator.interpolatingPredicateGenCEXAndOr _)

    // we have m predicates for m locations to instrument, corresponding to the instrumentation constraint.
    // each instrumentation predicate can be instantiated in n ways
    // i.e., the search space is n^m.
    // for the base case, we will have n = 2, with {instrument, noInstrument}, so the search space is 2^m

    val searchSpace = new MHashSet[Map[Predicate, Conjunction]]
    instrumenter.searchSpace.foreach(search =>
      searchSpace += search.toMap)

    println("Clauses instrumented, starting search for correct instrumentation.")

    var res : Result = Inconclusive
    // todo: assume empty instrumentation is in searchSpace?
    while((searchSpace nonEmpty) && res == Inconclusive) {
      val instrumentation = pickInstrumentation(searchSpace.toSet)
      println("Remaining search space size: " + searchSpace.size)
      println("Selected branches: " + instrumentation.map(instr =>
        instr._1.name + "(" + (instr._2.arithConj.positiveEqs.head.constant.intValue*(-1)) + ")").mkString(", "))

      // todo: assuming empty instrumentation is not in searchSpace below
      // left sol, right cex
      incSolver.checkWithSubstitution(instrumentation) match {
        case Right(cex) => {
          println("unsafe, iterating...")
          searchSpace -= instrumentation // todo; very stupid implementation that only removes the last instrumentation
          // backTranslator.translate(cex).prettyPrint
        }
        case Left(solution) =>
          res = Safe(solution)
      }
    }

    println(res)
  }
}
