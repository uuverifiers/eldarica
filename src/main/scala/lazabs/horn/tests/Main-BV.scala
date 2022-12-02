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

object MainBV extends App {
  import HornClauses._
  import IExpression._
  import ModuloArithmetic._

  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)
  lazabs.GlobalParameters.get.assertions = true

  val Seq(i1, i2) =
    for (n <- 1 to 2) yield MonoSortedPredicate("i" + n, List(UnsignedBVSort(8)))
 
  val x = UnsignedBVSort(8) newConstant "x"

  val clauses = List(
    i1(0)                  :- true,
    i2(bvadd(x, bv(8, 1))) :- (i1(x), bvult(x, bv(8, 100))),
    i1(bvadd(x, bv(8, 2))) :- i2(x),
    bvult(x, bv(8, 200))   :- i1(x)
  )

  println
  println(clauses mkString "\n")

  println
  println("Solving ...")

  println(SimpleWrapper.solve(clauses, debuggingOutput = true))

  //

  val clauses2 = List(
    i1(100)                :- true,
    i2(bvadd(x, bv(8, 3))) :- (i1(x), bvult(x, bv(8, 50))),
    i2(bvadd(x, bv(8, 1))) :- (i1(x), bvult(bv(8, 70), x)),
    i1(bvadd(x, bv(8, 2))) :- i2(x),
    (x =/= 75)             :- i1(x)
  )

  println
  println(clauses mkString "\n")

  println
  println("Solving ...")

  println(SimpleWrapper.solve(clauses2, debuggingOutput = true,
                              useTemplates = true))
}
