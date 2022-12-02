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

object MainGPU extends App {

  import HornClauses._
  import IExpression._
  import ParametricEncoder._
  
  ap.util.Debug enableAllAssertions false

  //////////////////////////////////////////////////////////////////////////////

  {
  println("GPU example")

  val p = for (i <- 0 to 9) yield (new Predicate("p" + i, 2 + 3))

  val lock   = new ConstantTerm("lock")
  val N      = new ConstantTerm("N")
  val id     = new ConstantTerm("id")
  val id_var = new ConstantTerm("id_var")
  val t      = new ConstantTerm("t")
  val id2     = new ConstantTerm("id2")
  val id_var2 = new ConstantTerm("id_var2")
  val t2      = new ConstantTerm("t2")
  
  val barrier = new SimpleBarrier("b", List(p.tail.toSet))

  val kernel = List(

    // init
    (p(0)(lock, N, id, id_var, t) :- true,
     NoSync),

    // assume(!lock && 0 <= id && id < N)
    (p(1)(0, N, id, id_var, t) :- (p(0)(0, N, id, id_var, t),
                                   id >= 0, id < N),
     NoSync),
    
    // lock := 1
    (p(2)(1, N, id, id_var, t) :- p(1)(lock, N, id, id_var, t),
     NoSync),
    
    // id_var := id
    (p(3)(lock, N, id, id, t) :- p(2)(lock, N, id, id_var, t),
     NoSync),
    
    // skip (was: ar[id] := id)
    (p(4)(lock, N, id, id_var, t) :- p(3)(lock, N, id, id_var, t),
     NoSync),
    
    // barrier
    (p(5)(lock, N, id, id_var, t) :- p(4)(lock, N, id, id_var, t),
     BarrierSync(barrier)),
    
    // t := * (was: ar[id] + ar[id + 1])
    (p(6)(lock, N, id, id_var, t2) :- p(5)(lock, N, id, id_var, t),
     NoSync),
    
    // barrier
    (p(7)(lock, N, id, id_var, t) :- p(6)(lock, N, id, id_var, t),
     BarrierSync(barrier)),
    
    // skip (was: ar[id] := t/2)
    (p(8)(lock, N, id, id_var, t) :- p(7)(lock, N, id, id_var, t),
     NoSync),
    
    // id_var := (id_var + 1) % N
    (p(9)(lock, N, id, id_var+1, t) :- (p(8)(lock, N, id, id_var, t),
                                        id_var < N - 1),
     NoSync),
    (p(9)(lock, N, id, 0, t) :- p(8)(lock, N, id, N-1, t),
     NoSync),
    
    // barrier
    (p(6)(lock, N, id, id_var, t) :- p(9)(lock, N, id, id_var, t),
     BarrierSync(barrier))

  )

  val assertions =
    List(

         // barrier divergence
         false :- (p(4)(lock, N, id, id_var, t),
                   p(6)(lock, N, id2, id_var2, t2)),
         false :- (p(4)(lock, N, id, id_var, t),
                   p(9)(lock, N, id2, id_var2, t2)),
         false :- (p(6)(lock, N, id, id_var, t),
                   p(9)(lock, N, id2, id_var2, t2)),

         // data races
         (id_var =/= id_var2) :-     (p(3)(lock, N, id, id_var, t),
                                      p(3)(lock, N, id2, id_var2, t2)),
         (id_var =/= id_var2) :-     (p(3)(lock, N, id, id_var, t),
                                      p(5)(lock, N, id2, id_var2, t2)),
         (id_var =/= (id_var2+1)) :- (p(3)(lock, N, id, id_var, t),
                                      p(5)(lock, N, id2, id_var2, t2)),
         (id_var =/= id_var2) :-     (p(3)(lock, N, id, id_var, t),
                                      p(7)(lock, N, id2, id_var2, t2)),

         (id_var =/= id_var2) :-     (p(7)(lock, N, id, id_var, t),
                                      p(7)(lock, N, id2, id_var2, t2)),
         (id_var =/= id_var2) :-     (p(7)(lock, N, id, id_var, t),
                                      p(5)(lock, N, id2, id_var2, t2)),
         (id_var =/= (id_var2+1)) :- (p(7)(lock, N, id, id_var, t),
                                      p(5)(lock, N, id2, id_var2, t2))

    )

  val system =
    System(List((kernel, Infinite)), 2, None, NoTime, List(), assertions)

  new VerificationLoop(system)
  }


}