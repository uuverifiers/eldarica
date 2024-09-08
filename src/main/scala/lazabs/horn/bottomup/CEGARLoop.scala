/**
 * Copyright (c) 2024 Philipp Ruemmer. All rights reserved.
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

import ap.parser.IAtom
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate

import lazabs.horn._
import Util._

import scala.collection.mutable.ArrayBuffer
import scala.util.{Try, Success, Failure}
import java.util.concurrent.LinkedBlockingQueue

/**
 * Abstract class representing different implementations of the main CEGAR loop.
 */
abstract class CEGARLoop[CC](context : HornPredAbsContext[CC]) {
  type LoopResult = Either[Map[Predicate, Conjunction], Dag[(IAtom, CC)]]
  def apply(cegar : CEGAR[CC])
           (implicit ev : CC => HornClauses.ConstraintClause) : LoopResult
}

/**
 * Sequential implementation of the main CEGAR loop.
 */
class SeqCEGARLoop[CC](_context : HornPredAbsContext[CC])
      extends CEGARLoop[CC](_context) {
  import CEGAR._

  def apply(cegar : CEGAR[CC])
           (implicit ev : CC => HornClauses.ConstraintClause) : LoopResult = {
    import cegar._

    var res : LoopResult = null

    while (!nextToProcess.isEmpty && res == null) {
      lazabs.GlobalParameters.get.timeoutChecker()

      // checkSubsumptionInvs

      val expansion@(states, clause, assumptions, _) = nextToProcess.dequeue

      if (!isBackwardSubsumed(expansion)) {
        genEdge(clause, states, assumptions) match {
          case GERInconsistent =>
            // nothing to do
          case GERNewEdge(e) =>
            addEdge(e)
          case _ : GERCounterexample =>
            for (dag <- handleCounterexample(expansion))
              res = Right(dag)
        }
      }
    }
  
    if (res == null)
      Left(genSolution)
    else
      res
  }
}

/**
 * Parallel implementation of the main CEGAR loop using Java threads.
 */
class ThreadedCEGARLoop[CC](_context : HornPredAbsContext[CC],
                            threadNum : Int)
      extends CEGARLoop[CC](_context) {
  import CEGAR._

  val inputQueue =
    new LinkedBlockingQueue[Option[CEGARStateQueue#Expansion]]
  val resultQueue =
    new LinkedBlockingQueue[(CEGARStateQueue#Expansion, Try[GenEdgeResult])]

  class GenEdgeThread(cegar : CEGAR[CC]) extends Thread {
    import cegar._

    override def run() : Unit = {
      var cont = true
      while (cont)
        inputQueue.take match {
          case Some(expansion@(states, clause, assumptions, _)) => {
            val res =
              try {
                Success(genEdge(clause, states, assumptions))
              } catch {
                case t : Throwable => Failure(t)
              }
            resultQueue.put((expansion, res))
          }
          case None =>
            // the signal for the thread to terminate
            cont = false
        }
    }
  }

  var busyThreads : Int = 0

  def enqueueN()(implicit cegar : CEGAR[CC]) : Unit =
    if (busyThreads < threadNum) {
      if (enqueue())
        enqueueN()
    }

  def enqueue()(implicit cegar : CEGAR[CC]) : Boolean = {
    import cegar._
    if (nextToProcess.isEmpty) {
      false
    } else {
      val expansion = nextToProcess.dequeue
      if (isBackwardSubsumed(expansion)) {
        enqueue()
      } else {
        inputQueue.put(Some(expansion))
        busyThreads = busyThreads + 1
        true
      }
    }
  }

  def waitForResult()(implicit cegar : CEGAR[CC])
                 : (CEGARStateQueue#Expansion, Try[GenEdgeResult]) = {
    val res = resultQueue.take
    busyThreads = busyThreads - 1
    res
  }

  def startThreads()(implicit cegar : CEGAR[CC]) : Seq[GenEdgeThread] = {
    val threads = for (_ <- 0 until threadNum) yield new GenEdgeThread(cegar)
    threads.foreach(_.start)
    threads
  }

  def stopThreads(threads : Seq[GenEdgeThread])
                 (implicit cegar : CEGAR[CC]) : Unit = {
    for (_ <- 0 until threadNum)
      inputQueue.put(None)
    threads.foreach(_.join())    
  }

  def apply(cegar : CEGAR[CC])
           (implicit ev : CC => HornClauses.ConstraintClause) : LoopResult = {
    import cegar._
    implicit val _cegar = cegar

    var result : Option[LoopResult] = None
    val counterexamples = new ArrayBuffer[CEGARStateQueue#Expansion]
    val threads = startThreads()

    try {
      enqueueN()

      while (busyThreads > 0 || !counterexamples.isEmpty) {
        lazabs.GlobalParameters.get.timeoutChecker()

        // checkSubsumptionInvs

        if (busyThreads > 0) {
          val (expansion, result) = waitForResult()

          result match {
            case Success(GERInconsistent) =>
              // nothing to do
            case Success(GERNewEdge(e)) =>
              addEdge(e)
            case Success(_ : GERCounterexample) =>
              counterexamples += expansion
          }
        } else {
          assert(!counterexamples.isEmpty)

          val cex = counterexamples.head
          for (expansion <- counterexamples.tail)
            nextToProcess.enqueue(expansion)

          counterexamples.clear()

          for (dag <- handleCounterexample(cex))
            result = Some(Right(dag))
        }

        if (result.isEmpty && counterexamples.isEmpty)
          enqueueN()
      }
    } finally {
      stopThreads(threads)
    }

    result.getOrElse(Left(genSolution))
  }
}

