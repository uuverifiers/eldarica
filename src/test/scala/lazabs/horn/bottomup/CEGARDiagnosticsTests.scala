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

import lazabs.horn.Util.NullStream
import lazabs.Main

import java.io.{File, ByteArrayOutputStream, PrintStream}

import org.scalatest.freespec.AnyFreeSpec
import org.scalatest.matchers.should.Matchers

/**
 * Tests for two new CEGAR diagnostic features:
 *
 * (A) -pPredicates:<file> emitting predicates per relation symbol, including
 *     after timeout (currently only fires on successful completion).
 *
 * (B) -pClauseStatus:<file> emitting which Horn clauses are satisfied vs
 *     violated in the current abstract reachability graph.
 *
 * Option surface design:
 *   -pPredicates:<file>    (existing) — dump final predicates per relation
 *                          symbol. Extension: also dump on timeout.
 *   -pClauseStatus:<file>  (new) — dump clause status (SATISFIED/UNPROVEN)
 *                          grouped by clause index. Fires on completion and
 *                          on timeout.
 *
 * Output format for -pPredicates (existing, extended to timeout):
 *   (initial-predicates <RelSymbol> (<args>)
 *     <formula>
 *     ...
 *   )
 *
 * Output format for -pClauseStatus (new):
 *   (clause-status
 *     (clause <0-based-index> <SATISFIED|UNPROVEN>
 *       <printed-clause-head> :- <printed-clause-body>)
 *     ...
 *   )
 *
 * Identification scheme for clauses: 0-based index into the normalized clause
 * list (normClauses), with the clause printed in "head :- body" form for
 * human readability. The index is stable across runs for the same input.
 */
class CEGARDiagnosticsTests extends AnyFreeSpec with Matchers {

  // A sat problem that requires CEGAR to find predicates.
  // monniaux-loop1 style: inv with a loop invariant needed.
  private val simpleSatProblem = """
    |(set-logic HORN)
    |(declare-fun inv (Int Int) Bool)
    |(assert (inv 0 0))
    |(assert (forall ((I Int) (J Int))
    |  (=> (and (<= I 1000) (inv I J)) (inv (+ I 1) (+ J 2)))))
    |(assert (forall ((I Int) (J Int)) (=> (inv I J) (<= J 3000))))
    |(check-sat)
  """.stripMargin

  // A problem with multiple relation symbols that requires CEGAR.
  // p counts up, q counts down; invariant needed for both.
  private val multiRelProblem = """
    |(set-logic HORN)
    |(declare-fun p (Int Int) Bool)
    |(declare-fun q (Int Int) Bool)
    |(assert (forall ((X Int) (Y Int))
    |  (=> (and (= X 0) (= Y 100)) (p X Y))))
    |(assert (forall ((X Int) (Y Int))
    |  (=> (and (p X Y) (< X 100)) (p (+ X 1) (- Y 1)))))
    |(assert (forall ((X Int) (Y Int))
    |  (=> (and (p X Y) (>= X 100)) (q X Y))))
    |(assert (forall ((X Int) (Y Int))
    |  (=> (q X Y) (= (+ X Y) 100))))
    |(check-sat)
  """.stripMargin

  // A problem designed to reliably time out: CEGAR diverges because the
  // required invariant has unbounded quantifier depth. Each refinement adds
  // a new predicate but never closes the abstraction. Using -t:5 gives
  // enough budget that even a slow CI runner won't solve it accidentally
  // while still keeping tests quick.
  private val timeoutProblem = """
    |(set-logic HORN)
    |(declare-fun inv (Int Int Int Int Int Int) Bool)
    |(assert (forall ((a Int) (b Int) (c Int) (d Int) (e Int) (f Int))
    |  (=> (and (= a 0) (= b 0) (= c 0) (= d 0) (= e 0) (= f 0))
    |      (inv a b c d e f))))
    |(assert (forall ((a Int) (b Int) (c Int) (d Int) (e Int) (f Int))
    |  (=> (inv a b c d e f)
    |      (inv (+ a 1) (+ b a) (+ c (* a b)) (+ d (* b c))
    |           (+ e (* c d)) (+ f (* d e))))))
    |(assert (forall ((a Int) (b Int) (c Int) (d Int) (e Int) (f Int))
    |  (=> (inv a b c d e f) (>= f (- 0 1)))))
    |(check-sat)
  """.stripMargin

  /** Write content to a temp file and return its path. */
  private def writeTempSmt2(content: String): File = {
    val f = File.createTempFile("eldarica-test-", ".smt2")
    f.deleteOnExit()
    val pw = new java.io.PrintWriter(f)
    pw.write(content)
    pw.close()
    f
  }

  /** Run Eldarica's main with given args, capturing stdout+stderr.
   *  Returns (exitNormally: Boolean, stdout: String, stderr: String). */
  private def runEldarica(args: String*): (Boolean, String, String) = {
    val out = new ByteArrayOutputStream()
    val err = new ByteArrayOutputStream()
    var normal = false
    try {
      Console.withOut(new PrintStream(out)) {
        Console.withErr(new PrintStream(err)) {
          Main.doMain(args.toArray, false)
        }
      }
      normal = true
    } catch {
      case _: Main.MainException =>
        normal = false
      case Main.PrintingFinishedException =>
        normal = true
      case _: Exception =>
        normal = false
    }
    (normal, out.toString("UTF-8"), err.toString("UTF-8"))
  }

  // ===========================================================================
  // FEATURE (A): Predicate output per relation symbol
  // ===========================================================================

  "Feature A: Predicate output per relation symbol" - {

    "A1. On a solved problem, -pPredicates produces output with relation symbols" in {
      val input = writeTempSmt2(simpleSatProblem)
      val predFile = File.createTempFile("eldarica-preds-", ".tpl")
      predFile.deleteOnExit()

      runEldarica("-abstract", "-pngNo",
                  s"-pPredicates:${predFile.getAbsolutePath}",
                  input.getAbsolutePath)

      val output = scala.io.Source.fromFile(predFile).mkString
      // The output should contain the relation symbol "inv" as a predicate group
      output should include ("inv")
      // Output should be in the (initial-predicates ...) format
      output should include ("initial-predicates")
    }

    "A2. On timeout, -pPredicates still emits predicates generated so far" in {
      val input = writeTempSmt2(timeoutProblem)
      val predFile = File.createTempFile("eldarica-preds-timeout-", ".tpl")
      predFile.deleteOnExit()

      runEldarica("-abstract", "-pngNo", "-t:5",
                  s"-pPredicates:${predFile.getAbsolutePath}",
                  input.getAbsolutePath)

      val output = scala.io.Source.fromFile(predFile).mkString
      // EXPECTED FAILURE: Currently the predicate file is empty on timeout
      // because the dump only fires after successful HornPredAbs construction.
      // The implementation must catch TimeoutException and dump predicates
      // from predStore.predicates before re-throwing.
      output.trim should not be empty
      output should include ("initial-predicates")
    }

    "A3. Predicate output is grouped per relation symbol" in {
      val input = writeTempSmt2(simpleSatProblem)
      val predFile = File.createTempFile("eldarica-preds-multi-", ".tpl")
      predFile.deleteOnExit()

      runEldarica("-abstract", "-pngNo",
                  s"-pPredicates:${predFile.getAbsolutePath}",
                  input.getAbsolutePath)

      val output = scala.io.Source.fromFile(predFile).mkString
      // The output must be structured as (initial-predicates <name> ...) blocks
      // — not a flat undifferentiated list. Each block groups predicates for
      // one relation symbol.
      val blocks = """\(initial-predicates\s+(\w+)""".r.findAllMatchIn(output).toList
      blocks.length should be >= 1
      // Each block should name a relation symbol
      blocks.head.group(1) should not be empty
      // The block should contain actual predicate formulas (indented lines)
      output.split("\n").exists(_.trim.startsWith("(")) shouldBe true
    }
  }

  // ===========================================================================
  // FEATURE (B): Clause status output (satisfied vs unproven)
  // ===========================================================================

  "Feature B: Clause status output" - {

    "B4. On a partially-solved problem (timeout), distinguishes SATISFIED from UNPROVEN" in {
      val input = writeTempSmt2(timeoutProblem)
      val statusFile = File.createTempFile("eldarica-clause-status-", ".txt")
      statusFile.deleteOnExit()

      // This tests the new -pClauseStatus option
      runEldarica("-abstract", "-pngNo", "-t:5",
                  s"-pClauseStatus:${statusFile.getAbsolutePath}",
                  input.getAbsolutePath)

      val output = scala.io.Source.fromFile(statusFile).mkString
      // EXPECTED FAILURE: Option does not exist yet.
      // Once implemented, output should contain both SATISFIED and UNPROVEN.
      output should include ("clause-status")
      output should include ("SATISFIED")
      output should include ("UNPROVEN")
    }

    "B5. On a fully-solved problem, all clauses report SATISFIED" in {
      val input = writeTempSmt2(simpleSatProblem)
      val statusFile = File.createTempFile("eldarica-clause-status-solved-", ".txt")
      statusFile.deleteOnExit()

      runEldarica("-abstract", "-pngNo",
                  s"-pClauseStatus:${statusFile.getAbsolutePath}",
                  input.getAbsolutePath)

      val output = scala.io.Source.fromFile(statusFile).mkString
      // EXPECTED FAILURE: Option does not exist yet.
      output should include ("clause-status")
      output should include ("SATISFIED")
      output should not include ("UNPROVEN")
    }

    "B6. Clauses are identified by stable index and printed form" in {
      val input = writeTempSmt2(simpleSatProblem)
      val statusFile = File.createTempFile("eldarica-clause-status-id-", ".txt")
      statusFile.deleteOnExit()

      runEldarica("-abstract", "-pngNo",
                  s"-pClauseStatus:${statusFile.getAbsolutePath}",
                  input.getAbsolutePath)

      val output = scala.io.Source.fromFile(statusFile).mkString
      // EXPECTED FAILURE: Option does not exist yet.
      // Each clause should be identified by its 0-based index and a readable
      // representation. Expect lines like:
      //   (clause 0 SATISFIED inv(...) :- ...)
      //   (clause 1 SATISFIED inv(...) :- inv(...))
      //   (clause 2 SATISFIED false :- inv(...))
      output should include ("clause-status")
      // Check for index-based identification pattern
      val clausePattern = """\(clause\s+\d+\s+(SATISFIED|UNPROVEN)""".r
      clausePattern.findFirstIn(output) should not be empty
    }

    "B7. Clause status is available on timeout" in {
      val input = writeTempSmt2(timeoutProblem)
      val statusFile = File.createTempFile("eldarica-clause-status-timeout-", ".txt")
      statusFile.deleteOnExit()

      runEldarica("-abstract", "-pngNo", "-t:5",
                  s"-pClauseStatus:${statusFile.getAbsolutePath}",
                  input.getAbsolutePath)

      val output = scala.io.Source.fromFile(statusFile).mkString
      // EXPECTED FAILURE: Option does not exist yet.
      // Even on timeout, the clause status should be dumped from the
      // current state of abstractEdges vs normClauses.
      output.trim should not be empty
      output should include ("clause-status")
      // At least some clauses should have been processed
      val clausePattern = """\(clause\s+\d+\s+(SATISFIED|UNPROVEN)""".r
      clausePattern.findAllIn(output).length should be > 0
    }
  }
}
