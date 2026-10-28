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

/**
 * Forward subsumption of a new clause by the stored clauses with its key
 * (passed oldest first), scanning only a window of them: the newest and
 * the oldest ones. `subsumes(stored, clause)` is the test for one pair.
 */
class SubsumptionChecker[C](subsumes : (C, C) => Boolean) {

  private val newestToCheck = 32 // use this many clauses that were last derived
  private val oldestToCheck = 8  // use this many oldest clauses

  private val collectStats     = lazabs.GlobalParameters.get.log
  private var subsumptionNanos = 0L

  def timeNanos : Long = subsumptionNanos

  // logging
  private var candidatePairs   = 0L
  private var statesSubsumed   = 0L
  private var calls            = 0L
  private var truncatedCalls   = 0L
  private var storedSizeSum    = 0L

  def stats : String =
    s"subsumption: $candidatePairs candidate pairs, " +
    s"$statesSubsumed states subsumed" +
    (if (calls > 0)
       s"\nsubsumption window: $calls calls, $truncatedCalls truncated " +
       s"at ${newestToCheck + oldestToCheck}, " +
       s"average stored states per call ${storedSizeSum / calls}"
     else "")

  def isSubsumed(clause : C, stored : IndexedSeq[C]) : Boolean =
    if (!collectStats)
      isSubsumedImpl(clause, stored)
    else {
      val start = System.nanoTime
      try isSubsumedImpl(clause, stored)
      finally subsumptionNanos += System.nanoTime - start
    }

  private def isSubsumedImpl(clause : C, stored : IndexedSeq[C]) : Boolean = {
    calls += 1
    storedSizeSum += stored.size
    if (stored.size > newestToCheck + oldestToCheck)
      truncatedCalls += 1
    val candidates =
      if (stored.size <= newestToCheck + oldestToCheck)
        stored.reverseIterator // below the limit
      else // use the limit
        stored.reverseIterator.take(newestToCheck) ++
          stored.iterator.take(oldestToCheck)
    val subsumed = candidates exists { storedClause =>
      candidatePairs += 1
      subsumes(storedClause, clause)
    }
    if (subsumed) statesSubsumed += 1
    subsumed
  }
}
