/**
 * Copyright (c) 2018 Hossein Hojjat and Philipp Ruemmer.
 * All rights reserved.
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

package lazabs

import lazabs.Main.{TimeoutException, StoppedException}

object ParallelComputation {
  /**
   * Run a computation for all given parameter sets in parallel. If the
   * <code>parameters</code> list is empty, the computation will just be
   * run with the current global parameters.
   */
  def apply[A](parameters : Seq[GlobalParameters],
               startDelay : Int = 200,
               checkPeriod : Int = 50)
              (comp: => A) =
    if (parameters.isEmpty)
      comp
    else
      (new ParallelComputation(comp, parameters, startDelay, checkPeriod)).result
}

/**
 * Simple class to do some computation in parallel for several settings,
 * and stop all threads as soon as one of them has produced a result.
 */
class ParallelComputation[A](comp: => A,
                             parameters : Seq[GlobalParameters],
                             startDelay : Int = 100,
                             checkPeriod : Int = 50) {

  private var resultOpt : Option[A] = None
  private var exceptionOpt : Option[Throwable] = None

  private val threads =
    (for (p <- parameters.iterator; if resultOpt.isEmpty) yield {
       val thread = new Thread(new Runnable { def run : Unit = {

         GlobalParameters.parameters.value = p
         p.timeoutChecker = () => {
           if (resultOpt.isDefined || exceptionOpt.isDefined)
             throw StoppedException
         }

         try {
           resultOpt = Some(comp)
         } catch {
           case StoppedException | TimeoutException =>
             // nothing
           case t : Throwable =>
             exceptionOpt = Some(t)
         }

       }})

       thread.start
       thread join startDelay

       thread
     }).toList

  while (resultOpt.isEmpty && exceptionOpt.isEmpty)
    try {
      GlobalParameters.get.timeoutChecker()
      threads.head join checkPeriod
    } catch {
      case t : Throwable =>
        exceptionOpt = Some(t)
    }

  for (t <- threads)
    t.join

  /**
   * Result produced by any of the computations; or an exception thrown
   * by any of the computations
   */
  val result : A =
    resultOpt getOrElse { throw exceptionOpt.get }
  
}