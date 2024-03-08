/**
 * Copyright (c) 2011-2023 Philipp Ruemmer. All rights reserved.
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

import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction

import scala.collection.mutable.PriorityQueue

import lazabs.horn.Util._

  case class AbstractState(rs : RelationSymbol, preds : Seq[RelationSymbolPred]) {
    val instances = toStream {
      case i => for (p <- preds) yield (p negInstances i)
    }
    val predConjunction = toStream {
      case i => rs.sf.reduce(Conjunction.conj(instances(i), rs.sf.order))
    }
    val predSet = preds.toSet
    val predHashCodeSet = predSet map (_.hashCode)
    override val hashCode = rs.hashCode + 3 * preds.hashCode
    override def equals(that : Any) = that match {
      case that : AbstractState => this.hashCode == that.hashCode &&
                                   this.rs == that.rs &&
                                   this.preds == that.preds
      case _ => false
    }
    override def toString = "(" + rs.name + ", <" + (preds mkString ", ") + ">)"
  }

  //////////////////////////////////////////////////////////////////////////////

  trait StateQueue {
    type TimeType
    type Expansion = (Seq[AbstractState], NormClause, Conjunction, TimeType)
    def isEmpty : Boolean
    def size : Int
    def enqueue(states : Seq[AbstractState],
                clause : NormClause, assumptions : Conjunction) : Unit
    def enqueue(exp : Expansion) : Unit
    def dequeue : Expansion
    def removeGarbage(reachableStates : scala.collection.Set[AbstractState])
    def incTime : Unit = {}
  }

  class ListStateQueue extends StateQueue {
    type TimeType = Unit
    private var states = List[(Seq[AbstractState], NormClause, Conjunction)]()
    def isEmpty : Boolean =
      states.isEmpty
    def size : Int =
      states.size
    def enqueue(s : Seq[AbstractState],
                clause : NormClause, assumptions : Conjunction) : Unit = {
      states = (s, clause, assumptions) :: states
//      println("enqueuing ... " +  (s, clause, assumptions))
    }
    def enqueue(exp : Expansion) : Unit =
      enqueue(exp._1, exp._2, exp._3)
    def dequeue : Expansion = {
      val (a, b, c) = states.head
      states = states.tail
      (a, b, c, ())
    }
    def removeGarbage(reachableStates : scala.collection.Set[AbstractState]) = 
      states = states filter {
        case (s, _, _) => s forall (reachableStates contains _)
      }
  }
  
  class PriorityStateQueue extends StateQueue {
    type TimeType = Int

    private var time = 0

    private def priority(s : Expansion) = {
      val (states, NormClause(_, _, (RelationSymbol(headSym), _)), _,
           birthTime) = s
      (headSym match {
        case HornClauses.FALSE => -10000
        case _ => 0
       }) + (
        for (AbstractState(_, preds) <- states.iterator)
        yield preds.size).sum +
      birthTime
    }

    private implicit val ord = new Ordering[Expansion] {
      def compare(s : Expansion, t : Expansion) =
        priority(t) - priority(s)
    }

    private val states = new PriorityQueue[Expansion]

    def isEmpty : Boolean =
      states.isEmpty
    def size : Int =
      states.size
    def enqueue(s : Seq[AbstractState],
                clause : NormClause, assumptions : Conjunction) : Unit = {
      states += ((s, clause, assumptions, time))
    }
    def enqueue(exp : Expansion) : Unit = {
      states += exp
    }
    def dequeue : Expansion =
      states.dequeue
    def removeGarbage(reachableStates : scala.collection.Set[AbstractState]) = {
      val remainingStates = (states.iterator filter {
        case (s, _, _, _) => s forall (reachableStates contains _)
      }).toArray
      states.dequeueAll
      states ++= remainingStates
    }
    override def incTime : Unit =
      time = time + 1
  }
