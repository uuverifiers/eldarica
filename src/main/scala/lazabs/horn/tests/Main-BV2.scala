/**
 * Copyright (c) 2018-2020 Philipp Ruemmer. All rights reserved.
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
import ap.SimpleAPI
import ap.theories.ModuloArithmetic._
import HornClauses._
import ap.parser.IExpression._

object MainBV2 extends App {
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.assertions = true
  lazabs.GlobalParameters.get.setLogLevel(1)

  SimpleAPI.withProver { p =>
    import p._

    val x = createConstant("x", UnsignedBVSort(32))
    val y = createConstant("y", UnsignedBVSort(32))

    val C = createRelation("C", Seq(UnsignedBVSort(32), UnsignedBVSort(32)))
    val D = createRelation("D", Seq(UnsignedBVSort(32), UnsignedBVSort(32)))

    val defClauses = List(
      C(bv(32, 1), bv(32, 1))                     :- true,
      C(bvadd(x, bv(32, 1)), bvadd(bv(32, 1), y)) :- C(x, y),
      D(x, y)                                     :- (C(x, y), x === bv(32, 0))
    )

    val prop =
      (y === bv(32, 0)) :- D(x, y)

    SimpleWrapper.solve(prop :: defClauses, useTemplates = true,
                        debuggingOutput = true) match {
      case Left(sol) => println("sat"); println(sol mapValues (pp(_)))
      case Right(cex) => println("unsat"); println(cex)
    }
  }
}
