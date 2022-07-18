/**
 * Copyright (c) 2011-2020 Philipp Ruemmer. All rights reserved.
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

object MainExtQuans extends App {

  import HornClauses._
  import IExpression._
  import lazabs.horn.preprocessor.ExtendedQuantifier

  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)

  val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)

  def sum (a : ITerm, b : ITerm) : ITerm = a + b
  val extQuan = new ExtendedQuantifier("sum", ar.objSort, sum)
  TheoryRegistry.register(extQuan)

  {
    val a = new SortedConstantTerm("a", ar.sort)
    val lo = new ConstantTerm("lo")
    val hi = new ConstantTerm("hi")

    val p = for (i <- 0 until 4) yield (new MonoSortedPredicate("p" + i,
      Seq(ar.sort, Sort.Integer, Sort.Integer)))

    val clauses = List(
      p(0)(a, lo, hi)          :- true,
      p(1)(ar.const(1), 0, 10) :- p(0)(a, lo, hi),
      false                    :- (p(1)(a, lo, hi),
                                  extQuan.fun(a, lo, hi) < 10)
    )

    println("Solving " + clauses + " ...")

    val predAbs =
      new HornPredAbs(clauses, Map(),
        DagInterpolator.interpolatingPredicateGenCEXAndOr _)

    println
    predAbs.result match {
      case Right(cex) => {
        println("NOT SOLVABLE")
        cex.prettyPrint
      }
      case Left(solution) =>
        println("SOLVABLE: " + solution)
    }
  }
}
