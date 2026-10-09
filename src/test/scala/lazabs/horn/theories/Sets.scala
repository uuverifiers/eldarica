/**
 * Copyright (c) 2026 Philipp Ruemmer. All rights reserved.
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

import ap.parser._
import ap.theories.arrays.SetTheory
import ap.types.MonoSortedPredicate

import lazabs.horn.bottomup._
import lazabs.horn.CHCResultMatchers
import lazabs.horn.preprocessor.DefaultPreprocessor
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.HornWrapper

import org.scalatest.freespec.AnyFreeSpec

class SetTests
    extends AnyFreeSpec
    with CHCResultMatchers {

  import IExpression._
  import HornClauses._

  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.assertions = true

  def solve(clauses : Seq[Clause]) = hideOutput {
    val preprocessor = new DefaultPreprocessor

    val (simplifiedClauses, simpPreHints, backTranslator) =
      preprocessor.process(clauses, EmptyVerificationHints)

    val predAbs = new HornPredAbs(simplifiedClauses)

    predAbs.result match {
      case Right(cex) => {
        val fullCEX = backTranslator.translate(cex)
        HornWrapper.verifyCEX(fullCEX, clauses)
        //println(fullCEX)
        Right(fullCEX)
      }
      case Left(sol) => {
        val fullSol = backTranslator.translate(sol)
        HornWrapper.verifySolution(fullSol, clauses)
        //println(fullSol)
        Left(fullSol)
      }
    }
  }

  "Solving clauses with sets" - {
    val setTheory = new SetTheory(Sort.Integer)
    import setTheory.{contains, subsetOf, union, isect, compl, set, emptySet,
                      including, excluding, sort => Set}

    val inv1 = MonoSortedPredicate("inv1", List(Set, Set))
    val inv2 = MonoSortedPredicate("inv2", List(Set, Set))
    val inv3 = MonoSortedPredicate("inv3", List(Set, Set))

    val x = Set.newConstant("x")
    val y = Set.newConstant("y")
    val a = Sort.Integer.newConstant("a")
    val b = Sort.Integer.newConstant("b")

    "Recursion-free 1" - {
      val clauses = List(
        inv1(set(1, 4), set(2)) :- true,
        inv2(x, union(x, y)) :- inv1(x, y),
        false :- (inv2(x, y), contains(y, 3))
      )

      solve(clauses) should beSat
    }

    "Recursion-free 2" - {
      val clauses = List(
        inv1(set(1), set(2)) :- true,
        inv2(x, union(x, y)) :- inv1(x, y),
        false :- (inv2(x, y), contains(y, 1))
      )

      solve(clauses) should beUnsat
    }

    "Recursion-free 3" - {
      val clauses = List(
        inv1(set(1), set(2)) :- true,
        inv2(x, union(x, y)) :- inv1(x, y),
        inv3(x, excluding(y, 1)) :- inv2(x, y),
        false :- (inv3(x, y), contains(y, 1))
      )

      solve(clauses) should beSat
    }

    "Recursion-free 4" - {
      val clauses = List(
        inv1(x, set(2)) :- !contains(x, 1),
        inv2(x, union(x, y)) :- inv1(x, y),
        false :- (inv2(x, y), contains(y, 1))
      )

      solve(clauses) should beSat
    }

    "Recursion-free 5" - {
      val clauses = List(
        inv1(set(1), set(2)) :- true,
        inv2(x, union(x, y)) :- inv1(x, y),
        false :- (inv2(x, y), subsetOf(y, x))
      )

      solve(clauses) should beSat
    }

    "Recursive 1" - {
      val clauses = List(
        inv1(set(1), set(2)) :- true,
        inv1(including(x, 2), including(y, 3)) :- inv1(x, y),
        inv2(x, union(x, y)) :- inv1(x, y),
        false :- (inv2(x, y), contains(y, 4))
      )

      solve(clauses) should beSat
    }
/*
    Currently throws an exception, to be checked.

    "Recursive 2" - {
      val clauses = List(
        inv1(set(1), set(2)) :- true,
        inv1(including(x, 2), including(y, 3)) :- inv1(x, y),
        inv2(x, union(x, y)) :- inv1(x, y),
        false :- (inv2(x, y), contains(y, 2))
      )
      
      solve(clauses) should beUnsat
    }
*/
    "Recursive 3" - {
      val clauses = List(
        inv1(emptySet(), emptySet()) :- true,
        inv1(including(x, a), including(y, b)) :-
           (inv1(x, y) & a >= 0 & a <= 10 & b >= 20 & b <= 100),
        false :- (inv1(x, y), contains(y, 15))
      )

      solve(clauses) should beSat
    }

/*
    Currently throws an exception, to be checked.

    "Recursive 4" - {
      val clauses = List(
        inv1(emptySet(), emptySet()) :- true,
        inv1(including(x, a), including(y, b)) :-
           (inv1(x, y) & a >= 0 & a <= 10 & b >= 20 & b <= 100),
        inv2(x, union(x, y)) :- inv1(x, y),
        false :- (inv2(x, y), contains(y, 50))
      )

      solve(clauses) should beSat
    }
*/

    "Recursive 5" - {
      val clauses = List(
        inv1(emptySet(), emptySet()) :- true,
        inv1(including(x, a), including(y, b)) :-
           (inv1(x, y) & a >= 0 & a <= 10 & b >= 20 & b <= 100),
        inv2(isect(x, y), union(x, y)) :- inv1(x, y),
        false :- (inv2(x, y), contains(x, 0)),
        false :- (inv2(x, y), contains(y, 1000))
      )

      solve(clauses) should beSat
    }

  }
}