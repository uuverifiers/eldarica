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

package lazabs.horn.abstractions

import lazabs.horn.Util.NullStream
import lazabs.horn.abstractions.VerificationHints._

import ap.parser._

import org.scalatest.freespec.AnyFreeSpec
import org.scalatest.matchers.should.Matchers

/**
 * Unit tests for AbsReader — the template/hint file parser.
 * Tests exercise parsing of initial-predicates and templates directives,
 * covering linear arithmetic, non-linear multiplication, and array sorts.
 */
class AbsReaderTests extends AnyFreeSpec with Matchers {

  /** Parse a .tpl hint string and return the AbsReader instance. */
  private def parseHints(tplContent: String): AbsReader =
    Console.withOut(NullStream) {
      Console.withErr(NullStream) {
        new AbsReader(new java.io.StringReader(tplContent))
      }
    }

  // =========================================================================
  // BASELINE SANITY — must pass today (proves the harness works)
  // =========================================================================

  "Baseline sanity" - {

    "1. Simple linear initial-predicates hint parses" in {
      val tpl =
        """(initial-predicates P ((x0 Int) (x1 Int))
          |  (>= x0 0)
          |)""".stripMargin
      val reader = parseHints(tpl)
      reader.initialPredicates should have size 1
      val (name, preds) = reader.initialPredicates.head
      name shouldBe "P"
      preds should have size 1
      // The formula should reference variable 0 (x0) in a >= constraint.
      // Princess represents (>= x0 0) as a GeqZ on the variable.
      val hint = reader.allHints("P").head
      hint shouldBe a[VerifHintInitPred]
    }

    "2. Templates directive with a linear term parses" in {
      val tpl =
        """(templates Q ((x0 Int) (x1 Int))
          |  (term x0 5)
          |)""".stripMargin
      val reader = parseHints(tpl)
      reader.allHints should contain key "Q"
      val hints = reader.allHints("Q")
      hints should have size 1
      hints.head shouldBe a[VerifHintTplEqTerm]
      hints.head.asInstanceOf[VerifHintTplEqTerm].cost shouldBe 5
    }

    "3. Constant-times-variable (* 2 x0) parses" in {
      val tpl =
        """(templates R ((x0 Int) (x1 Int))
          |  (term (* 2 x0) 3)
          |)""".stripMargin
      val reader = parseHints(tpl)
      val hints = reader.allHints("R")
      hints should have size 1
      val term = hints.head.asInstanceOf[VerifHintTplEqTerm]
      term.cost shouldBe 3
      // Princess normalizes (* 2 x0) to a linear term 2*v(1)
      // (de Bruijn index 1 because x0 is last pushed, i.e., index = arity-1-0).
      // Assert the term contains the expected coefficient via string form.
      val str = term.t.toString
      // The term should mention "2" as a factor
      str should include("2")
    }
  }

  // =========================================================================
  // NON-LINEAR (feature C) — variable-times-variable multiplication
  // =========================================================================

  "Non-linear multiplication" - {

    "4. Variable-times-variable (* x0 x1) in initial-predicates" in {
      val tpl =
        """(initial-predicates P ((x0 Int) (x1 Int))
          |  (>= (* x0 x1) 0)
          |)""".stripMargin
      val reader = parseHints(tpl)
      val (name, preds) = reader.initialPredicates.head
      name shouldBe "P"
      preds should have size 1
      val hint = reader.allHints("P").head.asInstanceOf[VerifHintInitPred]
      // The formula should contain a multiplication function application.
      // Princess represents non-linear mult via IFunApp with
      // GroebnerMultiplication.mul or similar. Check it parsed to IFormula.
      hint.f shouldBe an[IFormula]
      // Stronger: the formula should contain a function application (mul).
      val containsFunApp = hint.f.toString.contains("mul") ||
        hint.f.toString.contains("*") ||
        containsSubExpr(hint.f, { case IFunApp(_, _) => true })
      containsFunApp shouldBe true
    }

    "5. Non-linear inside larger formula (>= (* x0 x1) 0) and (= x2 (* x0 x1))" in {
      val tpl =
        """(initial-predicates P ((x0 Int) (x1 Int) (x2 Int))
          |  (>= (* x0 x1) 0)
          |  (= x2 (* x0 x1))
          |)""".stripMargin
      val reader = parseHints(tpl)
      val (name, preds) = reader.initialPredicates.head
      name shouldBe "P"
      preds should have size 2
      val hints = reader.allHints("P")
      hints should have size 2
      // Both should parse as VerifHintInitPred with IFormula payloads
      all(hints) shouldBe a[VerifHintInitPred]
    }

    "6. Non-linear templates term element" in {
      val tpl =
        """(templates P ((x0 Int) (x1 Int))
          |  (term (* x0 x1) 7)
          |)""".stripMargin
      val reader = parseHints(tpl)
      val hints = reader.allHints("P")
      hints should have size 1
      hints.head shouldBe a[VerifHintTplEqTerm]
      val term = hints.head.asInstanceOf[VerifHintTplEqTerm]
      term.cost shouldBe 7
      // The term should represent a non-linear product.
      // Check that it contains a function application (Princess mul).
      val str = term.t.toString
      (str.contains("mul") || str.contains("*") ||
        containsSubExpr(term.t, { case IFunApp(_, _) => true })) shouldBe true
    }

    "7. Higher-degree multiplication (* x0 (* x0 x1))" in {
      val tpl =
        """(templates P ((x0 Int) (x1 Int))
          |  (term (* x0 (* x0 x1)) 4)
          |)""".stripMargin
      val reader = parseHints(tpl)
      val hints = reader.allHints("P")
      hints should have size 1
      hints.head shouldBe a[VerifHintTplEqTerm]
      val term = hints.head.asInstanceOf[VerifHintTplEqTerm]
      term.cost shouldBe 4
      // Should contain nested multiplication — at least 2 function applications
      val funApps = collectSubExprs(term.t, { case IFunApp(_, _) => true })
      funApps should be >= 2
    }
  }

  // =========================================================================
  // ARRAYS (feature D) — array-sorted parameters, select, store
  // =========================================================================

  "Array hints" - {

    "8. Array-sorted parameter declaration parses" in {
      // The existing templates.tpl fixture already shows this works for templates.
      // Here we verify it works for initial-predicates too.
      val tpl =
        """(initial-predicates P ((a0 (Array Int Int)) (x0 Int))
          |  (>= x0 0)
          |)""".stripMargin
      val reader = parseHints(tpl)
      reader.initialPredicates should have size 1
      val (name, preds) = reader.initialPredicates.head
      name shouldBe "P"
      preds should have size 1
      // predArities should reflect 2 parameters
      reader.predArities("P") shouldBe 2
    }

    "9. select over array param (= (select a0 0) 5)" in {
      val tpl =
        """(initial-predicates P ((a0 (Array Int Int)) (x0 Int))
          |  (= (select a0 0) 5)
          |)""".stripMargin
      val reader = parseHints(tpl)
      val (name, preds) = reader.initialPredicates.head
      name shouldBe "P"
      preds should have size 1
      val hint = reader.allHints("P").head.asInstanceOf[VerifHintInitPred]
      hint.f shouldBe an[IFormula]
      // The formula should contain a select function application
      val str = hint.f.toString
      (str.contains("select") ||
        containsSubExpr(hint.f, { case IFunApp(_, _) => true })) shouldBe true
    }

    "10. store over array param (= a1 (store a0 0 5))" in {
      val tpl =
        """(initial-predicates P ((a0 (Array Int Int)) (a1 (Array Int Int)))
          |  (= a1 (store a0 0 5))
          |)""".stripMargin
      val reader = parseHints(tpl)
      val (name, preds) = reader.initialPredicates.head
      name shouldBe "P"
      preds should have size 1
      val hint = reader.allHints("P").head.asInstanceOf[VerifHintInitPred]
      hint.f shouldBe an[IFormula]
      // Should contain store function
      val str = hint.f.toString
      (str.contains("store") ||
        containsSubExpr(hint.f, { case IFunApp(_, _) => true })) shouldBe true
    }

    "11. Mixed array + integer parameter list" in {
      val tpl =
        """(templates P ((x0 Int) (a0 (Array Int Int)) (x1 Int))
          |  (term x0 1)
          |  (term (select a0 x1) 2)
          |  (term x1 3)
          |)""".stripMargin
      val reader = parseHints(tpl)
      reader.predArities("P") shouldBe 3
      val hints = reader.allHints("P")
      hints should have size 3
      all(hints) shouldBe a[VerifHintTplEqTerm]
      // Verify costs are in order — proves positional params handled correctly
      hints(0).asInstanceOf[VerifHintTplEqTerm].cost shouldBe 1
      hints(1).asInstanceOf[VerifHintTplEqTerm].cost shouldBe 2
      hints(2).asInstanceOf[VerifHintTplEqTerm].cost shouldBe 3
    }
  }

  // =========================================================================
  // Helpers
  // =========================================================================

  /** Check if an IExpression tree contains a sub-expression matching pf. */
  private def containsSubExpr(e: IExpression,
                              pf: PartialFunction[IExpression, Boolean]): Boolean = {
    if (pf.isDefinedAt(e) && pf(e)) return true
    e match {
      case IFunApp(_, args) => args.exists(a => containsSubExpr(a, pf))
      case IPlus(a, b)     => containsSubExpr(a, pf) || containsSubExpr(b, pf)
      case ITimes(_, sub)  => containsSubExpr(sub, pf)
      case INot(f)         => containsSubExpr(f, pf)
      case IBinFormula(_, f1, f2) =>
        containsSubExpr(f1, pf) || containsSubExpr(f2, pf)
      case ISortedQuantified(_, _, f) => containsSubExpr(f, pf)
      case IAtom(_, args)  => args.exists(a => containsSubExpr(a, pf))
      case ITermITE(c, l, r) =>
        containsSubExpr(c, pf) || containsSubExpr(l, pf) || containsSubExpr(r, pf)
      case IFormulaITE(c, l, r) =>
        containsSubExpr(c, pf) || containsSubExpr(l, pf) || containsSubExpr(r, pf)
      case IEquation(l, r) => containsSubExpr(l, pf) || containsSubExpr(r, pf)
      case IIntFormula(_, t) => containsSubExpr(t, pf)
      case _ => false
    }
  }

  /** Count sub-expressions matching pf in an IExpression tree. */
  private def collectSubExprs(e: IExpression,
                              pf: PartialFunction[IExpression, Boolean]): Int = {
    val here = if (pf.isDefinedAt(e) && pf(e)) 1 else 0
    val children = e match {
      case IFunApp(_, args) => args.map(a => collectSubExprs(a, pf)).sum
      case IPlus(a, b)     => collectSubExprs(a, pf) + collectSubExprs(b, pf)
      case ITimes(_, sub)  => collectSubExprs(sub, pf)
      case INot(f)         => collectSubExprs(f, pf)
      case IBinFormula(_, f1, f2) =>
        collectSubExprs(f1, pf) + collectSubExprs(f2, pf)
      case ISortedQuantified(_, _, f) => collectSubExprs(f, pf)
      case IAtom(_, args)  => args.map(a => collectSubExprs(a, pf)).sum
      case ITermITE(c, l, r) =>
        collectSubExprs(c, pf) + collectSubExprs(l, pf) + collectSubExprs(r, pf)
      case IFormulaITE(c, l, r) =>
        collectSubExprs(c, pf) + collectSubExprs(l, pf) + collectSubExprs(r, pf)
      case IEquation(l, r) => collectSubExprs(l, pf) + collectSubExprs(r, pf)
      case IIntFormula(_, t) => collectSubExprs(t, pf)
      case _ => 0
    }
    here + children
  }
}
