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

import Symex.FeasibilityCheckResult

/**
 * The search statistics: counters for the verdict and the -log output.
 */
class SymexStatistics {
  import FeasibilityCheckResult._

  var statesDerived       = 0L
  var checksFeasible      = 0L
  var checksInfeasible    = 0L
  var checksPostponed     = 0L
  var undecidedStates     = 0L
  var undecidedEmptyGoals = 0L
  var depthPrunedChoices  = 0L
  var checkNanos          = 0L
  var resolutionNanos     = 0L
  var statesWithUnconnectedConjunctsDropped = 0L

  def countCheck(checkResult          : FeasibilityCheckResult,
                 endsSearchIfFeasible : Boolean) : Unit =
    checkResult match {
      case Feasible        => checksFeasible   += 1
      case Infeasible      => checksInfeasible += 1
      case BudgetExpired   => checksPostponed  += 1
      case Undecided(_)    =>
        if (endsSearchIfFeasible) undecidedEmptyGoals += 1
        else undecidedStates += 1
      case Skipped         =>
    }

  def printStatistics(statesStored       : Int,
                      duplicatesRejected : Long,
                      subsumptionChecker : SubsumptionChecker[_],
                      simplifierStats    : Option[String],
                      simplifierNanos    : Long,
                      solveNanos         : Long) : Unit = {
    println(s"states: $statesDerived derived by resolution, " +
            s"$statesStored added to the database")
    println(s"checks: " +
            s"${checksFeasible + checksInfeasible + checksPostponed} " +
            s"($checksFeasible feasible, $checksInfeasible infeasible, " +
            s"$checksPostponed postponed)")
    println(s"undecided checks: ${undecidedStates + undecidedEmptyGoals} " +
            s"($undecidedStates states, $undecidedEmptyGoals empty goals)")
    println(s"depth bound: $depthPrunedChoices choices pruned")
    println(s"duplicate states rejected: $duplicatesRejected")
    println(subsumptionChecker.stats)
    println(s"unconnected conjuncts: dropped from " +
            s"$statesWithUnconnectedConjunctsDropped states")
    simplifierStats foreach println
    val solveMs = solveNanos / 1000000
    val checkMs = checkNanos / 1000000
    val simpMs  = simplifierNanos / 1000000
    val subsMs  = subsumptionChecker.timeNanos / 1000000
    val resMs   = resolutionNanos / 1000000
    val otherMs =
      0L max (solveMs - checkMs - simpMs - subsMs - resMs)
    println(s"time (ms): $solveMs solve ($checkMs checks, " +
            s"$simpMs simplification, $resMs resolution, " +
            s"$subsMs subsumption, $otherMs other)")
  }
}
