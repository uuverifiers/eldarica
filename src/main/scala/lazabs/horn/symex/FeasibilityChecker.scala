/**
 * Copyright (c) 2022-2026 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import ap.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
import ap.terfor.conjunctions.Conjunction

sealed abstract class FeasibilityCheckResult
object FeasibilityCheckResult {
  case object Feasible      extends FeasibilityCheckResult
  case object Infeasible    extends FeasibilityCheckResult
  case object BudgetExpired extends FeasibilityCheckResult
  case class  Undecided(status : ProverStatus.Value)
      extends FeasibilityCheckResult
  case object Skipped       extends FeasibilityCheckResult
}

/**
 * Feasibility checks of constraints by the prover, within a budget.
 */
trait FeasibilityChecker {
  val prover     : SimpleAPI
  val statistics : SymexStatistics

  val initialBudgetMs  : Long = 2000
  val budgetGrowthRate : Long = 2
  val cheapBudgetMs    : Long = 5

  private val collectCheckTimes = lazabs.GlobalParameters.get.log

  /**
   * Checks the constraint within budgetMs and counts the result. If the
   * constraint does not end the search when feasible, -symStateChecks
   * decides how it is checked.
   */
  protected def checkFeasibilityWithinBudget(
      constraint           : Conjunction,
      endsSearchIfFeasible : Boolean,
      budgetMs             : Long) : FeasibilityCheckResult = {
    import FeasibilityCheckResult._
    import lazabs.GlobalParameters.SymexStateChecks
    val checkBudgetMs =
      if (endsSearchIfFeasible) Some(budgetMs)
      else lazabs.GlobalParameters.get.symexStateChecks match {
        case SymexStateChecks.Full  => Some(budgetMs)
        case SymexStateChecks.Cheap =>
          // use a cheap budget for the first feasibility check
          if (budgetMs == initialBudgetMs) Some(cheapBudgetMs)
          else Some(budgetMs)
        case SymexStateChecks.None  => None
      }
    val checkStart = if (collectCheckTimes) System.nanoTime else 0L
    val checkResult = checkBudgetMs match {
      case Some(millis) => checkFeasibility(constraint, Some(millis))
      case None => if (constraint.isFalse) Infeasible else Skipped
    }
    if (collectCheckTimes)
      statistics.checkNanos += System.nanoTime - checkStart
    statistics.countCheck(checkResult, endsSearchIfFeasible)
    checkResult
  }

  private[symex] def checkFeasibility(constraint : Conjunction,
                                      budgetMs   : Option[Long])
    : FeasibilityCheckResult = {
    import FeasibilityCheckResult._
    if (constraint.isTrue) {
      Feasible
    } else if (constraint.isFalse) {
      Infeasible
    } else prover.scope {
      prover.addAssertionPreproc(constraint)
      prover.checkSat(block = false)
      proverStatusWithin(budgetMs) match {
        case ProverStatus.Running =>
          toFeasibilityCheckResult(prover.stop) match {
            case Undecided(_) => BudgetExpired
            case decided      => decided
          }
        case status => toFeasibilityCheckResult(status)
      }
    }
  }

  private val proverPollIntervalMs = 100L

  /**
   * Waits for the result of `checkSat(block = false)`, Running if the
   * budget runs out first. The timeout checker is called between polls, so
   * that the run can time out or be stopped during a long check.
   */
  protected def proverStatusWithin(budgetMs : Option[Long])
    : ProverStatus.Value = {
    val deadline = budgetMs map (System.currentTimeMillis + _)
    def nextPollMs = deadline match {
      case Some(time) => (time - System.currentTimeMillis) min
                           proverPollIntervalMs
      case None       => proverPollIntervalMs
    }
    var status = prover.getStatus(nextPollMs)
    while (status == ProverStatus.Running && nextPollMs > 0) {
      try {
        lazabs.GlobalParameters.get.timeoutChecker()
      } catch {
        case e : Exception =>
          prover.stop
          throw e
      }
      status = prover.getStatus(nextPollMs)
    }
    status
  }

  private def toFeasibilityCheckResult(status : ProverStatus.Value)
    : FeasibilityCheckResult = {
    import FeasibilityCheckResult._
    status match {
      case ProverStatus.Valid | ProverStatus.Sat     => Feasible
      case ProverStatus.Invalid | ProverStatus.Unsat => Infeasible
      case _                                         => Undecided(status)
    }
  }
}
