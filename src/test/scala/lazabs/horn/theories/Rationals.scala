/**
 * Copyright (c) 2023 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.theories

import lazabs.horn.bottomup._
import ap.parser._
import ap.theories.rationals.Rationals
import ap.theories.ADT
import ap.types.MonoSortedPredicate
import lazabs.horn.CHCResultMatchers
import org.scalatest.freespec.AnyFreeSpec

import lazabs.horn.preprocessor.DefaultPreprocessor
import lazabs.horn.abstractions.EmptyVerificationHints

class RationalTests
    extends AnyFreeSpec
    with CHCResultMatchers {

  import HornClauses._
  import IExpression._
  import Rationals.{plus, mul, frac, int2ring, lt, leq}
  
  ap.util.Debug enableAllAssertions true

  def solve(clauses : Seq[Clause]) = hideOutput {
    val preprocessor = new DefaultPreprocessor

    val (simplifiedClauses, simpPreHints, backTranslator) =
      preprocessor.process(clauses, EmptyVerificationHints)

    val predAbs =
      new HornPredAbs(simplifiedClauses, Map(),
                      DagInterpolator.interpolatingPredicateGenCEXAndOr _)

    predAbs.result match {
      case Right(cex) => Right(backTranslator.translate(cex))
      case Left(sol)  => Left(backTranslator.translate(sol))
    }
  }

  "Solving clauses over rationals" - {
    val x = Rationals.dom newConstant "x"
    val y = Rationals.dom newConstant "y"

    val inv1 = MonoSortedPredicate("inv1", List(Rationals.dom, Rationals.dom))
    val inv2 = MonoSortedPredicate("inv2", List(Rationals.dom, Rationals.dom))
  
    "Simple 1" - {
      val clauses = List(
        inv1(int2ring(0), y) :- (lt(int2ring(0), y), lt(y, int2ring(3))),
        inv1(plus(x, y), y)  :- inv1(x, y),
        inv2(x, y)           :- (inv1(x, y), leq(int2ring(10), x)),
        inv2(x, plus(x, y))  :- inv2(x, y),
        lt(y, int2ring(20))  :- inv2(x, y)
      )

      solve(clauses) should beUnsat
    }

    "Simple 2" - {
      val clauses = List(
        inv1(int2ring(0), y)                  :- (lt(int2ring(0), y),
                                                  lt(y, int2ring(1))),
        inv1(plus(x, int2ring(1)), plus(y,y)) :- (inv1(x, y), leq(x, int2ring(5))),
        lt(y, int2ring(100))                  :- inv1(x, y)
      )

      solve(clauses) should beSat
    }
  }

  "ADTs with rationals" - {
    val ratADT =
      new ADT(List("u"),
              List(("aFloat",
                    ADT.CtorSignature(List(("getFloat",
                                            ADT.OtherSort(Rationals.dom))),
                                      ADT.ADTSort(0))),
                   ("nan",
                    ADT.CtorSignature(List(),
                                      ADT.ADTSort(0)))))

    val U                     = ratADT.sorts.head
    val Seq(aFloat, nan)      = ratADT.constructors
    val Seq(Seq(getFloat), _) = ratADT.selectors

    val x = U newConstant "x"
    val y = U newConstant "y"

    val inv1 = MonoSortedPredicate("inv1", List(U, U))

    "Nondeterministic inputs" - {
      val clauses = List(
        inv1(x, aFloat(plus(getFloat(x), getFloat(y)))) :-
          (x =/= nan(), y =/= nan()),
        false :-
          (inv1(x, y), lt(getFloat(y), getFloat(x)))
      )

      solve(clauses) should beUnsat
    }
  }

}
