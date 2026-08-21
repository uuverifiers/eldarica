/**
 * Copyright (c) 2022 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

trait SubsumptionChecker {
  // returns: cuc is subsumed by some clauses in the unitClauseDB
  def checkForwardSubsumption(cuc:          UnitClause,
                              unitClauseDB: UnitClauseDB): Boolean

  // returns: a set of cucs subsumed by this cuc that are in the unitClauseDB
  def checkBackwardSubsumption(
      cuc:          UnitClause,
      unitClauseDB: UnitClauseDB
  ): Set[UnitClause]

  def subsumptionStats : Option[String] = None
}

trait NoSubsumptionChecker extends SubsumptionChecker {

  override def checkForwardSubsumption(cuc          : UnitClause,
                                       unitClauseDB : UnitClauseDB) = false

  override def checkBackwardSubsumption(
      cuc          : UnitClause,
      unitClauseDB : UnitClauseDB
  ) : Set[UnitClause] =  Set()
}

trait EntailmentSubsumptionChecker extends SubsumptionChecker {
  self : Symex[_] =>

  private val newestToCheck = 32 // use this many cucs that were last derived
  private val oldestToCheck = 8  // use this many oldest cucs

  // counters for the log summary
  private var candidatePairs   = 0L
  private var duplicateSkips   = 0L
  private var entailmentChecks = 0L
  private var statesSubsumed   = 0L

  override def subsumptionStats : Option[String] =
    Some(s"subsumption: $candidatePairs candidate pairs, " +
         s"$duplicateSkips duplicate skips, " +
         s"$entailmentChecks entailment checks, " +
         s"$statesSubsumed states subsumed")

  override def checkForwardSubsumption(cuc          : UnitClause,
                                       unitClauseDB : UnitClauseDB)
  : Boolean = {
    unitClauseDB.inferred(cuc.rs) match {
      case Some(stored) =>
        val candidates =
          if (stored.size <= newestToCheck + oldestToCheck)
            stored.reverseIterator // below the limit
          else // use the limit
            stored.reverseIterator.take(newestToCheck) ++
              stored.iterator.take(oldestToCheck)
        val subsumed = candidates exists { old =>
          candidatePairs += 1
          if (old.isPositive != cuc.isPositive) // polarity must match
            false
          else if (old.constraint == cuc.constraint) {
            // ignore syntactic equality, this should be checked
            // separately for cheaper
            duplicateSkips += 1
            false
          } else {
            entailmentChecks += 1
            symex_sf.reducer(cuc.constraint)(old.constraint).isTrue
          }
        }
        if (subsumed) statesSubsumed += 1
        subsumed
      case None => false
    }
  }

  override def checkBackwardSubsumption(cuc          : UnitClause,
                                        unitClauseDB : UnitClauseDB)
  : Set[UnitClause] = Set()
}
