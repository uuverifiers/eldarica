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

import ap.terfor.preds.Predicate
import lazabs.GlobalParameters.SymexChoiceOrder

import scala.collection.mutable.PriorityQueue

/**
 * Resolution choices, taken cheapest first. The key of a choice is its
 * cost plus the number of choices enqueued before it, so that, with costs
 * bounded below, every choice is taken after finitely many others. Under
 * first-in-first-out order every cost is 0.
 * E.g., choices a, b, c enqueued in this order with costs 5, 0, 0 have
 * keys 5, 1, 2 and are taken in the order b, c, a.
 */
class ResolutionChoiceQueue[Choice](order : SymexChoiceOrder.Value) {
  private case class KeyedChoice(key            : Long,
                                 enqueuedBefore : Long,
                                 choice         : Choice)

  private val choices = new PriorityQueue[KeyedChoice]()(
    Ordering.by((keyed : KeyedChoice) => (keyed.key, keyed.enqueuedBefore))
      .reverse)
  private var enqueuedCount = 0L

  def enqueue(choice : Choice, guidedCost : => Long) : Unit = {
    val cost = if (order == SymexChoiceOrder.Guided) guidedCost else 0L
    choices enqueue KeyedChoice(cost + enqueuedCount, enqueuedCount, choice)
    enqueuedCount += 1
  }

  def dequeue() : Choice = choices.dequeue().choice

  def isEmpty  : Boolean = choices.isEmpty
  def nonEmpty : Boolean = choices.nonEmpty
}

object ResolutionChoiceQueue {
  /**
   * The cost of a choice under guided order: lowest for a resolvent that
   * ends the search if feasible, then lower for small constraints, for few
   * unfoldings of one predicate on the derivation of the resolvent and for
   * predicates far from where the search starts.
   */
  def guidedCost(endsSearchIfFeasible : Boolean,
                 constraintSize       : Int,
                 largestUnfoldCount   : Int,
                 distanceFromStart    : Int) : Long =
    (if (endsSearchIfFeasible) -100000L else 0L) + constraintSize +
      100L * largestUnfoldCount - 10L * distanceFromStart
}

/**
 * How often each predicate was unfolded on a derivation, and the largest
 * of these counts. An unfolding of a predicate is a resolution step with a
 * clause that has the predicate in the head.
 * E.g., a derivation by p(x) :- x = 0, then twice p(x + 1) :- p(x), then
 * q(x) :- p(x) has the counts p: 3, q: 1, the largest 3.
 */
class UnfoldCounts private (private val counts : Map[Predicate, Int],
                            val largest        : Int) {
  def afterUnfolding(pred : Predicate) : UnfoldCounts = {
    val count = counts.getOrElse(pred, 0) + 1
    new UnfoldCounts(counts + (pred -> count), largest max count)
  }

  def countOf(pred : Predicate) : Int = counts.getOrElse(pred, 0)

  def largestAfterUnfolding(pred : Predicate) : Int =
    largest max (counts.getOrElse(pred, 0) + 1)

  // pointwise maximum, for a derivation from several others
  def join(that : UnfoldCounts) : UnfoldCounts =
    new UnfoldCounts(
      that.counts.foldLeft(counts) { case (joined, (pred, count)) =>
        if (joined.getOrElse(pred, 0) >= count) joined
        else joined + (pred -> count)
      },
      largest max that.largest)
}

object UnfoldCounts {
  val none = new UnfoldCounts(Map(), 0)
}
