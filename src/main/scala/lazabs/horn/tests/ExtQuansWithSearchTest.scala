/**
 * Copyright (c) 2023 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
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

package lazabs.horn.tests

import ap.parser._
import ap.theories._
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.bottomup._
import lazabs.horn.extendedquantifiers.InstrumentationLoop
import HornClauses._
import IExpression._
import ap.api.SimpleAPI
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.extendedquantifiers.ExtendedQuantifier

object ExtQuansWithSearchTest extends App {
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)

  val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)

  def sum (a : ITerm, b : ITerm) : ITerm = a + b
  def invSum (a : ITerm, b : ITerm) : ITerm = a - b
  val extQuan = new ExtendedQuantifier("sum", ar, i(0), sum, Some(invSum), None, None, None)
  TheoryRegistry.register(extQuan)

  {
    val a1 = new SortedConstantTerm("a1", ar.sort)
    val a2 = new SortedConstantTerm("a2", ar.sort)
    val i = new ConstantTerm("i")

    val p = for (i <- 0 until 5) yield (new MonoSortedPredicate("p" + i,
      Seq(ar.sort, ar.sort, Sort.Integer)))

     //SELECT (read)
    val clauses = List(
      p(0)(a1, a2, i)     :- (i === 0),
      p(0)(a1, a2, i + 1) :- (p(0)(a1, a2, i), 3 === ar.select(a1, i),
                                               4 === ar.select(a2, i), i < 10),
      p(1)(a1, a2, i)     :- (p(0)(a1, a2, i), i >= 10),
      false               :- (p(1)(a1, a2, i),
                             extQuan.morphism(a1, 0, 10) =/= 30) // [0, 10)
      )

    val instrLoop = new InstrumentationLoop(clauses, EmptyVerificationHints)

    instrLoop.result match {
      case Left(sln) =>
        println("SAFE")
        for((pred, f) <- sln) {
          println(s"$pred -> ${SimpleAPI.pp(f)}")
        }
      case Right(cex) =>
        println("UNSAFE")
        cex.prettyPrint
    }

    println(instrLoop.result)
  }
}
