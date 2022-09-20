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

import lazabs.horn.bottomup._
import ap.parser._
import ap.theories._
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.abstractions.{EmptyVerificationHints, VerificationHints}
import lazabs.horn.preprocessor.DefaultPreprocessor

object MainExtQuans extends App {

  import HornClauses._
  import IExpression._
  import lazabs.horn.preprocessor.ExtendedQuantifier

  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)

  val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)

  def sum (a : ITerm, b : ITerm) : ITerm = a + b
  def invSum (a : ITerm, b : ITerm) : ITerm = a - b
  val extQuan = new ExtendedQuantifier("sum", ar.objSort, sum, Some(invSum))
  TheoryRegistry.register(extQuan)

  {
    val a = new SortedConstantTerm("a", ar.sort)
    val i = new ConstantTerm("i")
    val s = new ConstantTerm("s")
    val o = new SortedConstantTerm("o",ar.objSort)
    val o2 = new SortedConstantTerm("o'",ar.objSort)


    val p = for (i <- 0 until 5) yield (new MonoSortedPredicate("p" + i,
      Seq(ar.sort, Sort.Integer)))

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

    val p3 = for (i <- 0 until 5) yield (new MonoSortedPredicate("p" + i,
      Seq(ar.sort, Sort.Integer, Sort.Integer)))

//    SELECT (read) - unsafe
        val clauses = List(
          p3(0)(a, i, s)     :- (i === 0, s === 0),
          p3(0)(a, i + 1, s) :- (p3(0)(a, i, s), o === ar.select(a, i), i < 10),
          p3(1)(a, i, s)     :- (p3(0)(a, i, s), i >= 10),
          false          :- (p3(1)(a, i, s),
                            extQuan.fun(a, 0, 10) =/= s) // right-open interval
        )

    val preprocessor = new DefaultPreprocessor
    val (simpClauses, _, backTranslator) =
      Console.withErr(Console.out) {
        preprocessor.process(clauses, EmptyVerificationHints)
      }
    println("Solving " + simpClauses + " ...")

    val predAbs =
      new HornPredAbs(simpClauses, Map(),
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
