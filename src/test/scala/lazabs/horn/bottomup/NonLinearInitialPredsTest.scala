/**
 * Copyright (c) 2026 Martin Schaef. All rights reserved.
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

package lazabs.horn.bottomup

import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.Util.NullStream
import lazabs.GlobalParameters

import ap.parser._
import ap.theories.GroebnerMultiplication
import ap.types.{Sort, MonoSortedPredicate}

import org.scalatest.freespec.AnyFreeSpec
import org.scalatest.matchers.should.Matchers

/**
 * Regression test for non-linear initial-predicates hints.
 * 
 * When an initial-predicate hint contains a variable-times-variable
 * multiplication (e.g., (* x x)), the predicate abstraction machinery
 * must handle the mul function from GroebnerMultiplication even if the
 * CHC clauses themselves are purely linear.
 * 
 * Bug: "key not found: mul/3" when initial-predicates contain non-linear mult.
 */
class NonLinearInitialPredsTest extends AnyFreeSpec with Matchers {

  // Set up GlobalParameters for tests
  private def withGlobalParams[T](f: => T): T = {
    GlobalParameters.parameters.withValue(new GlobalParameters) {
      f
    }
  }

  "Non-linear initial-predicates" - {

    "should not throw 'key not found: mul/3' on var*var hint" in withGlobalParams {
      val inv = MonoSortedPredicate("inv", Seq(Sort.Integer))
      val x  = Sort.Integer newConstant "x"
      val x1 = Sort.Integer newConstant "x1"

      val clauses = List(
        Clause(IAtom(inv, Seq(IIntLit(0))), List(), IBoolLit(true)),
        Clause(IAtom(inv, Seq(IConstant(x1))),
               List(IAtom(inv, Seq(IConstant(x)))),
               IExpression.Eq(IConstant(x1), IConstant(x) + 1)),
        Clause(SimpleWrapper.FALSEAtom,
               List(IAtom(inv, Seq(IConstant(x)))),
               IConstant(x) < 0)
      )

      // Construct a NON-LINEAR initial-predicate: (>= (* x x) 0)
      // using GroebnerMultiplication.mul to build var*var
      val v0 = ISortedVariable(0, Sort.Integer)
      val mulExpr = IFunApp(GroebnerMultiplication.mul, Seq(v0, v0))
      val pred = IIntFormula(IIntRelation.GeqZero, mulExpr)

      val initialPredicates = Map(inv.asInstanceOf[ap.terfor.preds.Predicate] ->
                                  Seq(pred.asInstanceOf[IFormula]))

      // This should NOT throw. Before the fix, it throws:
      //   java.util.NoSuchElementException: key not found: mul/3
      Console.withOut(NullStream) {
        Console.withErr(NullStream) {
          noException should be thrownBy {
            SimpleWrapper.solve(clauses,
                               initialPredicates = initialPredicates,
                               useTemplates = false,
                               debuggingOutput = false)
          }
        }
      }
    }

    "should solve a problem using a non-linear initial-predicate hint" in withGlobalParams {
      // Same simple linear problem — solution is inv(x) := x >= 0
      val inv = MonoSortedPredicate("inv", Seq(Sort.Integer))
      val x  = Sort.Integer newConstant "x"
      val x1 = Sort.Integer newConstant "x1"

      val clauses = List(
        Clause(IAtom(inv, Seq(IIntLit(0))), List(), IBoolLit(true)),
        Clause(IAtom(inv, Seq(IConstant(x1))),
               List(IAtom(inv, Seq(IConstant(x)))),
               IExpression.Eq(IConstant(x1), IConstant(x) + 1)),
        Clause(SimpleWrapper.FALSEAtom,
               List(IAtom(inv, Seq(IConstant(x)))),
               IConstant(x) < 0)
      )

      // Provide both a useful linear predicate and a harmless non-linear one
      val v0 = ISortedVariable(0, Sort.Integer)
      val geqZero = IIntFormula(IIntRelation.GeqZero, v0)
      val mulExpr = IFunApp(GroebnerMultiplication.mul, Seq(v0, v0))
      val nonlinPred = IIntFormula(IIntRelation.GeqZero, mulExpr)

      val initialPredicates = Map(inv.asInstanceOf[ap.terfor.preds.Predicate] ->
                                  Seq(geqZero.asInstanceOf[IFormula],
                                      nonlinPred.asInstanceOf[IFormula]))

      val result = Console.withOut(NullStream) {
        Console.withErr(NullStream) {
          SimpleWrapper.solve(clauses,
                             initialPredicates = initialPredicates,
                             useTemplates = false,
                             debuggingOutput = false)
        }
      }

      // Should return sat (Left)
      result shouldBe a[Left[_, _]]
    }
  }
}
