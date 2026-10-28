/**
 * Copyright (c) 2026 Zafer Esen, Philipp Ruemmer. All rights reserved.
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
package lazabs.horn.symex

import ap.terfor.conjunctions.Conjunction
import lazabs.horn.bottomup.RelationSymbol
import Symex.FeasibilityCheckResult

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

/**
 * Subsumption of a clause with a single atom by the union of the stored clauses. 
 * E.g., false :- P(x), x >= 2 is subsumed by the following two together:
 *       false :- P(x), x >= 3
 *       false :- P(x), x <= 2
 * `singleAtomConstraint(clause)` is the relation symbol and constraint of
 * a clause whose only atom has the arguments of occurrence 0, None otherwise.
 */
class UnionSubsumption[C](
    singleAtomConstraint : C => Option[(RelationSymbol, Conjunction)],
    checkFeasibility     : (Conjunction, Option[Long]) =>
                             FeasibilityCheckResult)(
    implicit symex_sf : SymexSymbolFactory) {
  import FeasibilityCheckResult._

  private val budgetMsOf      = new MHashMap[RelationSymbol, Long]
  private val initialBudgetMs = 5L // doubled on expiry

  // after n fruitless tests in a row, the next 2^n - 1 clauses (at most
  // 4095) are not tested.
  private val fruitlessTestsOf = new MHashMap[RelationSymbol, Int]
  private val untestedLeftOf   = new MHashMap[RelationSymbol, Int]
  private val maxGapExponent   = 12

  private val collectStats = lazabs.GlobalParameters.get.log
  private var proverNanos  = 0L

  // logging
  private var tests          = 0L
  private var testsSkipped   = 0L
  private var statesSubsumed = 0L
  private var budgetsExpired = 0L

  def stats : String =
    s"union subsumption: $tests tests, $testsSkipped skipped, " +
    s"$statesSubsumed states subsumed, $budgetsExpired budgets expired, " +
    s"${proverNanos / 1000000} ms"

  def appliesTo(clause : C) : Boolean = singleAtomConstraint(clause).isDefined

  def isSubsumed(clause : C, stored : Iterator[C]) : Boolean = {
    val Some((rs, constraint)) = singleAtomConstraint(clause)
    val reduce = symex_sf.reducer(constraint)
    val overlapping = new ArrayBuffer[Conjunction]
    val subsumedByOne = stored exists { storedClause =>
      singleAtomConstraint(storedClause) exists {
        case (storedRs, storedConstraint) =>
          storedRs == rs && {
            val reduced = reduce(storedConstraint)
            if (!reduced.isFalse)
              overlapping += reduced
            reduced.isTrue
          }
      }
    }
    subsumedByOne ||
      overlapping.nonEmpty && !isTestSkipped(rs) &&
        isImpliedByProver(rs, constraint, overlapping)
  }

  private def isTestSkipped(rs : RelationSymbol) : Boolean = {
    val untestedLeft = untestedLeftOf.getOrElse(rs, 0)
    if (untestedLeft > 0) {
      untestedLeftOf(rs) = untestedLeft - 1
      testsSkipped += 1
    }
    untestedLeft > 0
  }

  private def isImpliedByProver(rs          : RelationSymbol,
                                constraint  : Conjunction,
                                disjunction : Seq[Conjunction]) : Boolean = {
    tests += 1
    val budgetMs = budgetMsOf.getOrElse(rs, initialBudgetMs)
    val uncovered = Conjunction.conj(
      constraint +: disjunction.map(_.negate), symex_sf.order)
    val start = if (collectStats) System.nanoTime else 0L
    val checkResult = checkFeasibility(uncovered, Some(budgetMs))
    if (collectStats)
      proverNanos += System.nanoTime - start
    if (checkResult == BudgetExpired) {
      budgetsExpired += 1
      budgetMsOf(rs) = 2 * budgetMs
    }
    if (checkResult == Infeasible) {
      statesSubsumed += 1
      fruitlessTestsOf(rs) = 0
      true
    } else {
      val fruitlessTests = fruitlessTestsOf.getOrElse(rs, 0) + 1
      fruitlessTestsOf(rs) = fruitlessTests
      untestedLeftOf(rs) = (1 << (fruitlessTests min maxGapExponent)) - 1
      false
    }
  }
}
