/**
 * Copyright (c) 2018-2026 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn

import ap.SimpleAPI
import lazabs.horn.bottomup._
import HornClauses._
import ap.parser._
import IExpression.Sort
import ap.terfor.{TermOrder, TerForConvenience}
import ap.terfor.conjunctions.Conjunction

import lazabs.horn.preprocessor.DefaultPreprocessor
import lazabs.horn.abstractions.EmptyVerificationHints

import org.scalatest.freespec.AnyFreeSpec

class IncTest
    extends AnyFreeSpec
    with CHCResultMatchers {

  "Incremental Tests" - {
    lazabs.GlobalParameters.get.assertions = true

    //println("Starting incremental test ...")

    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._

      val x    = createConstant("x")
      val y    = createConstant("y")
      val n    = createConstant("n")

      val I    = createRelation("I", Seq(Sort.Integer, Sort.Integer, Sort.Integer))

      val Init = createRelation("Init", Seq(Sort.Integer))
      val f0   = createRelation("f0", Seq())
      val f1   = createRelation("f1", Seq())
      val f2   = createRelation("f2", Seq())

      val clauses = {
        import ap.parser.IExpression._
        List(
          I(0, 0, n) :- (f0(), Init(n)),
          I(x + 1, y + 1, n) :- (f1(), I(x, y, n), y < n),
          false :- (f2(), I(x, y, n), x > 2*n)
        )
      }

      val incSolver =
        new IncrementalHornPredAbs(clauses,
                                   Map(),
                                   Set(f0, f1, f2, Init))

      implicit val o = TermOrder.EMPTY
      import TerForConvenience._
      import Conjunction.{TRUE, FALSE}

      val r1 = incSolver.checkWithSubstitution(
                Map(
                  Init -> TRUE, f0 -> TRUE, f1 -> TRUE, f2 -> TRUE
                ))
      //println(r1)
      r1.isRight shouldBe true

      val r2 = incSolver.checkWithSubstitution(
                Map(
                  Init -> (v(0) > 0), f0 -> TRUE, f1 -> TRUE, f2 -> TRUE
                ))
      //println(r2)
      r2.isLeft shouldBe true

      val r3 = incSolver.checkWithSubstitution(
                Map(
                  Init -> TRUE, f0 -> TRUE, f1 -> FALSE, f2 -> TRUE
                ))
      //println(r3)
      r3.isRight shouldBe true
    }
  }

  "Incremental Tests with Preprocessor" - {
    lazabs.GlobalParameters.get.assertions = true

    //println("Starting incremental test with preprocessing ...")

    SimpleAPI.withProver(enableAssert = true) { p =>
      import p._

      val x    = createConstant("x")
      val y    = createConstant("y")
      val n    = createConstant("n")

      val I    = createRelation("I", Seq(Sort.Integer, Sort.Integer, Sort.Integer))
      val I2   = createRelation("I2", Seq(Sort.Integer, Sort.Integer, Sort.Integer))
      val I3   = createRelation("I3", Seq(Sort.Integer, Sort.Integer, Sort.Integer))

      val Init = createRelation("Init", Seq(Sort.Integer))
      val f0   = createRelation("f0", Seq())
      val f1   = createRelation("f1", Seq())
      val f2   = createRelation("f2", Seq())

      val clauses = {
        import ap.parser.IExpression._
        List(
          I(0, 0, n) :- (f0(), Init(n)),
          I2(x, y, n) :- (I(x, y, n), y < n),
          I3(x, y, n) :- (I(x, y, n), y < 10),
          I(x + 1, y + 1, n) :- (f1(), I2(x, y, n)),
          false :- (f2(), I(x, y, n), x > 2*n)
        )
      }

      val preprocessor = new DefaultPreprocessor

      val (simplifiedClauses, simpPreHints, backTranslator) = hideOutput {
        preprocessor.process(clauses, EmptyVerificationHints,
                             Set(f0, f1, f2, Init))
      }

      val incSolver =
        new IncrementalHornPredAbs(simplifiedClauses,
                                   Map(),
                                   Set(f0, f1, f2, Init))

      implicit val o = TermOrder.EMPTY
      import TerForConvenience._
      import Conjunction.{TRUE, FALSE}

      val r1 = incSolver.checkWithSubstitution(
              Map(
                Init -> TRUE, f0 -> TRUE, f1 -> TRUE, f2 -> TRUE
              ))
      //println(r1)
      r1.isRight shouldBe true

      val r2 = incSolver.checkWithSubstitution(
          Map(
                Init -> (v(0) > 0), f0 -> TRUE, f1 -> TRUE, f2 -> TRUE
              ))
      //println(r2)
      r2.isLeft shouldBe true

      val r3 = incSolver.checkWithSubstitution(
          Map(
                Init -> TRUE, f0 -> TRUE, f1 -> FALSE, f2 -> TRUE
              ))
      //println(r3)
      r3.isRight shouldBe true
    }
  }

}
