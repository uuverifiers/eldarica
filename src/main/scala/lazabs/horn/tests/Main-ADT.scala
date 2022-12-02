/**
 * Copyright (c) 2017-2020 Philipp Ruemmer. All rights reserved.
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
import ap.types.MonoSortedPredicate

object MainADT extends App {

  import HornClauses._
  import IExpression._
  
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)
  lazabs.GlobalParameters.get.assertions = true

  val pairADT =
    new ADT(List("pair"),
            List(("p", ADT.CtorSignature(List(("left", ADT.OtherSort(Sort.Integer)),
                                              ("right", ADT.OtherSort(Sort.Bool))),
                                         ADT.ADTSort(0)))))

  println("ADT: " + pairADT)

  val Pair = pairADT.sorts.head
  val P = pairADT.constructors.head
  val Seq(Seq(left, right)) = pairADT.selectors

  val Seq(i1, i2) =
    for (n <- 1 to 2) yield MonoSortedPredicate("i" + n, List(Pair))

  val p = Pair newConstant "p"

  val clauses = List(
    i1(P(0, ADT.BoolADT.True))                     :- true,
    i2(P(left(p) + 1, 1 - right(p)))               :- i1(p),
    i1(P(left(p) * 2, 1 - right(p)))               :- i2(p),
    (left(p) >= 0 & right(p) === ADT.BoolADT.True) :- i1(p)
  )

  println
  println(clauses mkString "\n")

  println
  println("Solving ...")

  println(SimpleWrapper.solve(clauses, debuggingOutput = true))

}
