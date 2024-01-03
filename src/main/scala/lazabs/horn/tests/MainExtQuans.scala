/**
 * Copyright (c) 2023 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.bottomup._
import ap.parser._
import ap.theories._
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.extendedquantifiers.Normalizer
import lazabs.horn.preprocessor.DefaultPreprocessor

object MainExtQuans extends App {

  import HornClauses._
  import IExpression._
  import lazabs.horn.extendedquantifiers.ExtendedQuantifier

  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)

  val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)

  def sum(a:    ITerm, b: ITerm): ITerm = a + b
  def invSum(a: ITerm, b: ITerm): ITerm = a - b
  val extQuan =
    new ExtendedQuantifier("sum", ar, i(0), sum, Some(invSum), None, None, None)
  TheoryRegistry.register(extQuan)

  {
    val a  = new SortedConstantTerm("a", ar.sort)
    val i  = new ConstantTerm("i")
    val s  = new ConstantTerm("s")
    val o  = new SortedConstantTerm("o", ar.objSort)
    val o2 = new SortedConstantTerm("o'", ar.objSort)

    val p = for (i <- 0 until 5)
      yield (new MonoSortedPredicate("p" + i, Seq(ar.sort, Sort.Integer)))

    //SELECT (read)
//    val clauses = List(
//      p(0)(a, i)     :- (i === 0),
//      p(0)(a, i + 1) :- (p(0)(a, i), 3 === ar.select(a, i), i < 10),
//      p(1)(a, i)     :- (p(0)(a, i), i >= 10),
//      false          :- (p(1)(a, i),
//                        extQuan.fun(a, 0, 10) =/= 30) // right-open interval
//    )

//    // STORE (write)

//    val clauses = List(
//      p(0)(a, i)     :- (i === 0),
//      p(0)(ar.store(a, i, 3), i + 1) :- (p(0)(a, i), i < 10),
//      p(1)(a, i)     :- (p(0)(a, i), i >= 10),
//      false          :- (p(1)(a, i),
//        extQuan.fun(a, 0, 10) =/= 30) // right-open interval
//    )

    def max(a: ITerm, b: ITerm): ITerm = {
      IExpression.ite(a >= b, a, b)
    }
    val extQuanMax = new ExtendedQuantifier("max",
                                            ar,
                                            Int.MinValue,
                                            max,
                                            None,
                                            None,
                                            None,
                                            None)
    TheoryRegistry.register(extQuanMax)

//    SELECT (read) - unsafe
    val clauses = List(
      p(0)(a, i) :- (i === 0),
      p(0)(a, i + 1) :- (p(0)(a, i), o === ar.select(a, i), i < 10),
      p(1)(a, i) :- (p(0)(a, i), i >= 10),
      false :- (p(1)(a, i),
      extQuanMax.morphism(a, 0, 10) <= 30) // right-open interval
      )

    val preprocessor = new DefaultPreprocessor
    val (simpClauses, _, backTranslator) =
      Console.withErr(Console.out) {
        preprocessor.process(clauses, EmptyVerificationHints)
      }
    println("Solving " + simpClauses + " ...")

    val predAbs =
      new HornPredAbs(simpClauses,
                      Map(),
                      DagInterpolator.interpolatingPredicateGenCEXAndOr _)

    println
    predAbs.result match {
      case Right(cex) => {
        println("NOT SOLVABLE")
        backTranslator.translate(cex).prettyPrint
      }
      case Left(solution) =>
        println("SOLVABLE: " + backTranslator.translate(solution))
    }
  }
}

object NormalizerTest extends App {

  import HornClauses._
  import IExpression._
  import lazabs.horn.extendedquantifiers.ExtendedQuantifier

  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)

  val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)

  def sum(a:    ITerm, b: ITerm): ITerm = a + b
  def invSum(a: ITerm, b: ITerm): ITerm = a - b

  val extQuan =
    new ExtendedQuantifier("sum", ar, i(0), sum, Some(invSum), None, None, None)
  TheoryRegistry.register(extQuan)

  {
    val a1 = new SortedConstantTerm("a1", ar.sort)
    val a2 = new SortedConstantTerm("a2", ar.sort)
    val a3 = new SortedConstantTerm("a3", ar.sort)
    val a4 = new SortedConstantTerm("a4", ar.sort)
    val a5 = new SortedConstantTerm("a5", ar.sort)
    val i  = new ConstantTerm("i")
    val s  = new ConstantTerm("s")
    val o  = new SortedConstantTerm("o", ar.objSort)
    val o2 = new SortedConstantTerm("o'", ar.objSort)

    val p = for (i <- 0 until 5)
      yield (new MonoSortedPredicate("p" + i, Seq(ar.sort, Sort.Integer)))

    val clauses = List(
      p(0)(a4, i) :- (i === 0, a3 === ar.store(a2, 1, 2), a1 === ar
        .const(0), a2 === ar.store(a1, 0, 1), o === ar
        .select(a2, 0), a4 =/= a3),
      p(1)(a1, i) :- (p(0)(a1, i), ar.select(a1, 1) >= ar.select(a1, 0)),
      false :- (p(1)(a1, i), //ar.select(a1,1) =/= 2)
      extQuan.morphism(a1, 0, 2) =/= 3) // right-open interval
      )

    val preprocessor = new DefaultPreprocessor
    val (simpClauses, _, backTranslator) =
      Console.withErr(Console.out) {
        preprocessor.process(clauses, EmptyVerificationHints)
      }

    simpClauses.foreach(clause => println(clause.toPrologString))

    val normalizer = new Normalizer

    val (normalizedClauses, _, backTranslator2) =
      normalizer.process(simpClauses, EmptyVerificationHints)

    println

    normalizedClauses.foreach(clause => println(clause.toPrologString))

    val predAbs =
      new HornPredAbs(normalizedClauses,
                      Map(),
                      DagInterpolator.interpolatingPredicateGenCEXAndOr _)

    println
    predAbs.result match {
      case Right(cex) => {
        println("NOT SOLVABLE")
        // backTranslator.translate(backTranslator2.translate(cex)).prettyPrint
      }
      case Left(solution) =>
        println("SOLVABLE: ") //+
      // backTranslator.translate(backTranslator2.translate(solution)))
    }

  }
}

object AxiomsTest extends App {

  import HornClauses._
  import IExpression._
  import lazabs.horn.extendedquantifiers.ExtendedQuantifier

  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)

  val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)

  def sum(a: ITerm, b: ITerm): ITerm = a + b
  val extQuan =
    new ExtendedQuantifier("sum", ar, i(0), sum, None, None, None, None)
  TheoryRegistry.register(extQuan)

  {
    val a  = new SortedConstantTerm("a", ar.sort)
    val i  = new ConstantTerm("i")
    val s  = new ConstantTerm("s")
    val o  = new SortedConstantTerm("o", ar.objSort)
    val o2 = new SortedConstantTerm("o'", ar.objSort)

    val p = for (i <- 0 until 5)
      yield (new MonoSortedPredicate("p" + i, Seq(ar.sort, Sort.Integer)))

    //SELECT (read)
    val clauses = List(
      p(0)(a, i) :- (i === 0),
      p(0)(a, i + 1) :- (p(0)(a, i), i === ar.select(a, i), i < 10),
      p(1)(a, i) :- (p(0)(a, i), i >= 10),
      false :- (p(1)(a, i), extQuan.morphism(a, 0, 10) =/= 45) // right-open interval
      )

//    // STORE (write)

//    val clauses = List(
//      p(0)(a, i)     :- (i === 0),
//      p(0)(ar.store(a, i, 3), i + 1) :- (p(0)(a, i), i < 10),
//      p(1)(a, i)     :- (p(0)(a, i), i >= 10),
//      false          :- (p(1)(a, i),
//        extQuan.fun(a, 0, 10) =/= 30) // right-open interval
//    )

    val preprocessor = new DefaultPreprocessor
    val (simpClauses, _, backTranslator) =
      Console.withErr(Console.out) {
        preprocessor.process(clauses, EmptyVerificationHints)
      }
    println("Solving " + simpClauses + " ...")

    val predAbs =
      new HornPredAbs(simpClauses,
                      Map(),
                      DagInterpolator.interpolatingPredicateGenCEXAndOr _)

    println
    predAbs.result match {
      case Right(cex) => {
        println("NOT SOLVABLE")
        backTranslator.translate(cex).prettyPrint
      }
      case Left(solution) =>
        println("SOLVABLE: " + backTranslator.translate(solution))
    }

  }
}
