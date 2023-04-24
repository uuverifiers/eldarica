/**
 * Copyright (c) 2011-2016 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.concurrency

import ap.parser._
import lazabs.horn.bottomup.{HornClauses, HornPredAbs, DagInterpolator, Util}

object MainLimits extends App {

  import HornClauses._
  import IExpression._
  import ParametricEncoder._
  
  ap.util.Debug enableAllAssertions true

  val l = for (i <- 0 to 2) yield (new Predicate("l" + i, 1 + 1))

  val id   = new ConstantTerm("id")
  val id2   = new ConstantTerm("id2")
  val id3   = new ConstantTerm("id3")
  val id4   = new ConstantTerm("id4")
  val sem  = new ConstantTerm("sem")
  
  val proc = List(

    (l(0)(0, id) :- true,
     NoSync),
  
    (l(1)(sem + 1, id) :- (l(0)(sem, id), sem < 3),
     NoSync),
  
    (l(0)(sem - 1, id) :- l(1)(sem, id),
     NoSync)
  
  )

  val assertions =
    List(false :- (l(1)(sem, id),
                   l(1)(sem, id2),
                   l(1)(sem, id3),
                   l(1)(sem, id4)))

  val system =
    System(List((proc, Infinite)), 1, None, NoTime, List(), assertions)

  new VerificationLoop(system)

}