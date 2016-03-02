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

object Main extends App {

  import HornClauses._
  import IExpression._
  import ParametricEncoder._
  
  ap.util.Debug enableAllAssertions true

  def solve(enc : ParametricEncoder) = {
  println("Solving ...")
  
  val predAbs =
    new HornPredAbs(enc.allClauses, Map(),
                    DagInterpolator.interpolatingPredicateGenCEXAndOr _)

  println
  predAbs.result match {
    case Right(cex) => {
      println("NOT SOLVABLE")
      Util.show(for (p <- cex) yield p._1, "horn-cex")
      cex.prettyPrint
    }
    case Left(solution) =>
      println("SOLVABLE: " + solution)
  }
  }

  //////////////////////////////////////////////////////////////////////////////

  {
    println("Boardcast channel test (encoded using barriers)")

    val p = for (i <- 0 until 3) yield (new Predicate("p" + i, 2))
    val q = for (i <- 0 until 3) yield (new Predicate("q" + i, 1))
    val id = new ConstantTerm("id")
    val c = new ConstantTerm("c")
    val id2 = new ConstantTerm("id2")
    val c2 = new ConstantTerm("c2")
    val d = new ConstantTerm("d")
    
    val bcChan = new SimpleBarrier("bcChan",
                                    List(Set(p(1)),
                                         Set(q(0), q(1))))
    
    val pProc = List(
      (p(0)(id, 0) :- true,
       NoSync),
      (p(1)(id, c) :- p(0)(id, c),
       NoSync),
      (p(2)(id, c+1) :- p(1)(id, c),
       BarrierSync(bcChan)),
      (p(1)(id, c) :- p(2)(id, c),
       NoSync)
    )

    val qProc = List(
      (q(0)(0) :- true,
       NoSync),
      (q(1)(d) :- q(0)(d),
       NoSync),
      (q(1)(d+1) :- q(1)(d),
       BarrierSync(bcChan))
    )

    val assertions =
//      List((c <= d) :- (p(1)(id, c), q(1)(d)))
      List((c === c2) :- (p(1)(id, c), p(1)(id2, c2)))

    val system =
      System(List((pProc, Infinite),
                  (qProc, Singleton)),
             0, None, NoTime, List(), assertions)

    new VerificationLoop(system)
  }

  //////////////////////////////////////////////////////////////////////////////

  /*

     Diverges with default settings
     (try with abstraction?)
  
  {
  println("BIP temperature control system, untimed")

  val l = for (i <- 0 to 6) yield (new Predicate("l" + i, 1 + 1))
  val sync = new ConstantTerm("sync")
  val X = new ConstantTerm("X")
  val t1 = new ConstantTerm("t1")
  val t2 = new ConstantTerm("t2")
  val th = new ConstantTerm("th")

  val barrier = new SimpleBarrier("barrier",
                                  List(Set(l(1), l(2)),
                                       Set(l(5), l(6)),
                                       Set(l(3), l(4))))
  
//        sync:
//        1    -> { tick1, tick, tick2 }
//        2    -> { rest1, heat }
//        3    -> { rest2, heat }
//        4    -> { cool1, cool }
//        5    -> { cool2, cool }

  val Rod1 = List(
    (l(1)(sync, 3600) :- true,
     NoSync),
    (l(1)(sync, t1 + 1) :- (l(1)(sync, t1), sync === 1),
     BarrierSync(barrier)),
    (l(2)(sync, t1) :- (l(1)(sync, t1), sync === 4, t1 >= 3600),
     BarrierSync(barrier)),
    (l(2)(sync, t1) :- (l(2)(sync, t1), sync === 1),
     BarrierSync(barrier)),
    (l(1)(sync, 0) :- (l(2)(sync, t1), sync === 2),
     BarrierSync(barrier))
  )

  val Rod2 = List(
    (l(3)(sync, 3600) :- true,
     NoSync),
    (l(3)(sync, t2 + 1) :- (l(3)(sync, t2), sync === 1),
     BarrierSync(barrier)),
    (l(4)(sync, t2) :- (l(3)(sync, t2), sync === 5, t2 >= 3600),
     BarrierSync(barrier)),
    (l(4)(sync, t2) :- (l(4)(sync, t2), sync === 1),
     BarrierSync(barrier)),
    (l(3)(sync, 0) :- (l(4)(sync, t2), sync === 3),
     BarrierSync(barrier))
  )

  val Controller = List(
    (l(5)(sync, 100) :- true,
     NoSync),
    (l(5)(X, th) :- l(5)(sync, th),
     NoSync),
    (l(6)(X, th) :- l(6)(sync, th),
     NoSync),
    (l(5)(sync, th + 1) :- (l(5)(sync, th), sync === 1, th < 1000),
     BarrierSync(barrier)),
    (l(6)(sync, th) :- (
       l(5)(sync, th), (sync === 5) | (sync === 6), th === 1000),
     BarrierSync(barrier)),
    (l(6)(sync, th - 2) :- (l(6)(sync, th), sync === 1, th > 100),
     BarrierSync(barrier)),
    (l(5)(sync, th) :- (
       l(6)(sync, th), (sync === 2) | (sync === 3), th === 100),
     BarrierSync(barrier))
  )

  val assertions =
    List(((th >= 100) & (th <= 1000)) :- l(5)(sync, th))

  val system =
    System(List((Rod1, Singleton),
                (Controller, Singleton),
                (Rod2, Singleton)),
           1, None, NoTime, List(), assertions)

  new VerificationLoop(system)
  }
  */

  //////////////////////////////////////////////////////////////////////////////

  {
  println("BIP temperature control system, with discrete time")

  val l = for (i <- 0 to 8) yield (new Predicate("l" + i, 2 + 1))
  val sync = new ConstantTerm("sync")
  val X = new ConstantTerm("X")
  val C = new ConstantTerm("C")
  val t1 = new ConstantTerm("t1")
  val t2 = new ConstantTerm("t2")
  val th = new ConstantTerm("th")

  val barrier = new SimpleBarrier("barrier",
                                  List(Set(l(1), l(2), l(3)),
                                       Set(l(4), l(5), l(6)),
                                       Set(l(7), l(8))))
  
//        sync:
//        2    -> { rest1, heat }
//        3    -> { rest2, heat }
//        4    -> { cool1, cool }
//        5    -> { cool2, cool }

  val Rod1 = List(
    (l(3)(C, sync, C) :- true,
     NoSync),
    (l(2)(C, sync, t1) :- (l(3)(C, sync, t1), sync === 4),
     BarrierSync(barrier)),
    (l(2)(C, sync, t1) :- (l(1)(C, sync, t1), sync === 4, C - t1 >= 3600),
     BarrierSync(barrier)),
    (l(1)(C, sync, C) :- (l(2)(C, sync, t1), sync === 2),
     BarrierSync(barrier)),

    (l(1)(C, sync, t1) :- (l(1)(C, sync, t1), (sync === 3) | (sync === 5)),
     BarrierSync(barrier)),
    (l(2)(C, sync, t1) :- (l(2)(C, sync, t1), (sync === 3) | (sync === 5)),
     BarrierSync(barrier)),
    (l(3)(C, sync, t1) :- (l(3)(C, sync, t1), (sync === 3) | (sync === 5)),
     BarrierSync(barrier))
  )

  val Rod2 = List(
    (l(6)(C, sync, C) :- true,
     NoSync),
    (l(5)(C, sync, t2) :- (l(6)(C, sync, t2), sync === 5),
     BarrierSync(barrier)),
    (l(5)(C, sync, t2) :- (l(4)(C, sync, t2), sync === 5, C - t2 >= 3600),
     BarrierSync(barrier)),
    (l(4)(C, sync, C) :- (l(5)(C, sync, t2), sync === 3),
     BarrierSync(barrier)),

    (l(4)(C, sync, t2) :- (l(4)(C, sync, t2), (sync === 2) | (sync === 4)),
     BarrierSync(barrier)),
    (l(5)(C, sync, t2) :- (l(5)(C, sync, t2), (sync === 2) | (sync === 4)),
     BarrierSync(barrier)),
    (l(6)(C, sync, t2) :- (l(6)(C, sync, t2), (sync === 2) | (sync === 4)),
     BarrierSync(barrier))
  )

  val Controller = List(
    (l(7)(C, sync, C) :- true,
     NoSync),
    (l(8)(C, sync, C) :- (
       l(7)(C, sync, th), (sync === 4) | (sync === 5), C - th === 900),
     BarrierSync(barrier)),
    (l(7)(C, sync, C) :- (
       l(8)(C, sync, th), (sync === 2) | (sync === 3), C - th === 450),
     BarrierSync(barrier)),

    (l(7)(C, X, th) :- l(7)(C, sync, th),
     NoSync),
    (l(8)(C, X, th) :- l(8)(C, sync, th),
     NoSync)
  )

  val timeInvs = List(
    (C - th <= 900) :- l(7)(C, sync, th),
    (C - th <= 450) :- l(8)(C, sync, th)
  )

  val assertions =
//    List(((C - th >= 0) & (C - th <= 900)) :- l(7)(C, sync, th))
    List(false :- (
           l(1)(C, sync, t1), l(4)(C, sync, t2), l(7)(C, sync, th),
           C - th === 900, C - t1 < 3600, C - t2 < 3600))

  val system =
    System(List((Rod1, Singleton),
                (Rod2, Singleton),
                (Controller, Singleton)),
           2, None, DiscreteTime(0), timeInvs, assertions)

  new VerificationLoop(system)
  }

  //////////////////////////////////////////////////////////////////////////////

  {
  println("BIP-style communication via barriers")

  val p = for (i <- 0 to 3) yield (new Predicate("p" + i, 3 + 1))
  val q = for (i <- 0 to 3) yield (new Predicate("q" + i, 3 + 1))
  val r = for (i <- 0 to 3) yield (new Predicate("r" + i, 3 + 1))
  
  val a_flag = new ConstantTerm("a_flag")
  val b_flag = new ConstantTerm("b_flag")
  val c_flag = new ConstantTerm("c_flag")
  val l = new ConstantTerm("l")
  val l2 = new ConstantTerm("l2")
  val l3 = new ConstantTerm("l3")

  val abc_barrier = new SimpleBarrier("abc_barrier",
                                      List(Set(p(1), p(2)),
                                           Set(q(1), q(2)),
                                           Set(r(1), r(2))))

  val barrierCondition =
    ((a_flag === 1) & (b_flag === 0) & (c_flag === 0)) |
    ((a_flag === 1) & (b_flag === 1) & (c_flag === 0)) |
    ((a_flag === 1) & (b_flag === 1) & (c_flag === 1))

  val aProcess = List(
    (p(0)(0, 0, 0, 0) :- true,
     NoSync),
    (p(1)(1, b_flag, c_flag, l) :- p(0)(0, b_flag, c_flag, l),
     NoSync),
    (p(2)(a_flag, b_flag, c_flag, l) :-
         (p(1)(a_flag, b_flag, c_flag, l), barrierCondition),
     BarrierSync(abc_barrier)),
    (p(3)(0, b_flag, c_flag, l) :- p(2)(a_flag, b_flag, c_flag, l),
     NoSync),
    (p(0)(a_flag, b_flag, c_flag, l+1) :- p(3)(a_flag, b_flag, c_flag, l),
     NoSync)
  )

  val bProcess = List(
    (q(0)(0, 0, 0, 0) :- true,
     NoSync),
    (q(1)(a_flag, 1, c_flag, l) :- q(0)(a_flag, 0, c_flag, l),
     NoSync),
    (q(2)(a_flag, b_flag, c_flag, l) :-
         (q(1)(a_flag, b_flag, c_flag, l), barrierCondition),
     BarrierSync(abc_barrier)),
    (q(3)(a_flag, 0, c_flag, l) :- q(2)(a_flag, b_flag, c_flag, l),
     NoSync),
    (q(0)(a_flag, b_flag, c_flag, l+1) :- q(3)(a_flag, b_flag, c_flag, l),
     NoSync)
  )

  val cProcess = List(
    (r(0)(0, 0, 0, 0) :- true,
     NoSync),
    (r(1)(a_flag, b_flag, 1, l) :- r(0)(a_flag, b_flag, 0, l),
     NoSync),
    (r(2)(a_flag, b_flag, c_flag, l) :-
         (r(1)(a_flag, b_flag, c_flag, l), barrierCondition),
     BarrierSync(abc_barrier)),
    (r(3)(a_flag, b_flag, 0, l) :- r(2)(a_flag, b_flag, c_flag, l),
     NoSync),
    (r(0)(a_flag, b_flag, c_flag, l+1) :- r(3)(a_flag, b_flag, c_flag, l),
     NoSync)
  )

  val assertions =
    List((l >= l2) :- (p(0)(a_flag, b_flag, c_flag, l),
                       q(0)(a_flag, b_flag, c_flag, l2)),
         (l2 >= l3) :- (q(0)(a_flag, b_flag, c_flag, l2),
                        r(0)(a_flag, b_flag, c_flag, l3)))

  val system =
    System(List((aProcess, Singleton),
                (bProcess, Singleton),
                (cProcess, Singleton)),
           3, None, NoTime, List(), assertions)

  new VerificationLoop(system)
  }

  //////////////////////////////////////////////////////////////////////////////

  {
  println("Barrier example")

  val p = for (i <- 0 to 4) yield (new Predicate("p" + i, 1 + 3))

  val lock = new ConstantTerm("lock")
  val id   = new ConstantTerm("id")
  val cnt  = new ConstantTerm("cnt")
  val t    = new ConstantTerm("t")
  val id2  = new ConstantTerm("id2")
  val cnt2 = new ConstantTerm("cnt2")
  val t2   = new ConstantTerm("t2")
  
  val barrier = new SimpleBarrier("b", List(p.tail.toSet))

  val counterProcess = List(

    (p(0)(lock, id, 0, t) :- true,
     NoSync),

    (p(1)(0, id, cnt, t) :- p(0)(0, id, cnt, t),
     NoSync),
    
    (p(2)(1, id, cnt, t) :- p(1)(lock, id, cnt, t),
     NoSync),
    
    (p(3)(lock, id, cnt, cnt + 1) :- p(2)(lock, id, cnt, t),
     NoSync),
    
    (p(4)(lock, id, t, t) :- p(3)(lock, id, cnt, t),
     NoSync),
    
    (p(2)(lock, id, cnt, t) :- p(4)(lock, id, cnt, t),
     BarrierSync(barrier))

  )

  val assertions =
    List((cnt === cnt2) :- (p(2)(lock, id, cnt, t),
                            p(2)(lock, id2, cnt2, t2)))

  val system =
    System(List((counterProcess, Infinite)), 1, None, NoTime, List(), assertions)

  new VerificationLoop(system)

  }

  //////////////////////////////////////////////////////////////////////////////

  {
  println("Train crossing example")

  val train = for (i <- 0 to 4) yield (new Predicate("train" + i, 4 + 3))
  val gate  = for (i <- 0 to 5) yield (new Predicate("gate" + i, 4 + 3))
  
  val C = new ConstantTerm("C")
  val U = new ConstantTerm("U")
  val e = new ConstantTerm("e")
  val ticket = new ConstantTerm("ticket")
  val my_ticket = new ConstantTerm("my_ticket")
  val my_ticket2 = new ConstantTerm("my_ticket2")
  val next_waiting_ticket = new ConstantTerm("next_waiting_ticket")
  val next_available_ticket = new ConstantTerm("next_available_ticket")
  val x = new ConstantTerm("x")
  val x2 = new ConstantTerm("x2")
  val y = new ConstantTerm("y")
  val id = new ConstantTerm("id")
  val id2 = new ConstantTerm("id2")

  val go = new CommChannel("go")
  val appr = new CommChannel("appr")
  val leave = new CommChannel("leave")
  val stop = new CommChannel("stop")

  val gateProcess = List(

    (gate(1)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, C) :- true,               NoSync),

    (gate(5)(C, U, e, ticket, next_available_ticket, next_available_ticket, y) :-
       gate(1)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     NoSync),

    (gate(3)(C, U, e, next_waiting_ticket, next_waiting_ticket+1, next_available_ticket, y) :-
       (gate(5)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),
        next_waiting_ticket < next_available_ticket),                                               NoSync),

    (gate(2)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y) :-
       (gate(5)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),
        next_waiting_ticket === next_available_ticket),                                             NoSync),

    (gate(0)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y) :-
       gate(3)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Send(go)),

    (gate(0)(C, U, e, ticket, next_waiting_ticket, next_available_ticket+1, y) :-
       gate(2)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Receive(appr)),

    (gate(5)(C, U, e, ticket, next_waiting_ticket+1, next_available_ticket, y) :-
       gate(0)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Receive(leave)),

    (gate(4)(C, U, e, next_available_ticket, next_waiting_ticket, next_available_ticket+1, C) :-
       gate(0)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Receive(appr)),

    (gate(0)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y) :-
       gate(4)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),                     Send(stop))

  )

  val trainProcess = List(

    (train(4)(C, U, e, ticket, id, my_ticket, C) :- true,                                           NoSync),

    (train(1)(C, U, id, ticket, id, my_ticket, C) :-
       train(4)(C, U, e, ticket, id, my_ticket, x),                                                 Send(appr)),

    (train(2)(C, U, e, ticket, id, ticket, C) :-
       (train(1)(C, U, e, ticket, id, my_ticket, x),
        C - x <= U*10, e === id),                                                                   Receive(stop)),

    (train(3)(C, U, e, ticket, id, my_ticket, C) :-
       (train(2)(C, U, e, ticket, id, my_ticket, x),
        my_ticket === ticket),                                                                      Receive(go)),

    (train(0)(C, U, e, ticket, id, my_ticket, C) :-
       (train(3)(C, U, e, ticket, id, my_ticket, x),
        C - x >= U*7),                                                                              NoSync),

    (train(0)(C, U, e, ticket, id, my_ticket, C) :-
       (train(1)(C, U, e, ticket, id, my_ticket, x),
        C - x >= U*10),                                                                             NoSync),

    (train(4)(C, U, id, ticket, id, my_ticket, C) :-
       (train(0)(C, U, e, ticket, id, my_ticket, x),
        C - x >= U*3),                                                                              Send(leave))

  )

  val timeInvs = List(
    (C - y <= U*5) :- gate(4)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),
    (C - x <= U*20) :- train(1)(C, U, e, ticket, id, my_ticket, x),
    (C - x <= U*15) :- train(3)(C, U, e, ticket, id, my_ticket, x),
    (C - x <= U*5) :- train(0)(C, U, e, ticket, id, my_ticket, x)
  )

  val assertions =
    List(false :- (train(0)(C, U, e, ticket, id, my_ticket, x),
                   train(0)(C, U, e, ticket, id2, my_ticket2, x2)))

  val system =
    System(
      List((gateProcess, Singleton), (trainProcess, Infinite)),
      4, None,
      ContinuousTime(0, 1),
      timeInvs,
      assertions)

  new VerificationLoop(system)

/*  val enc =
    new ParametricEncoder(system, assertions, List(List(1, 2)))

  solve(enc) */

  }

 
  //////////////////////////////////////////////////////////////////////////////

  println



/*
P(c,my_id,x,num,id,t)    :- (x = c) , \+(my_id = 0) , (num = 0) , (t = 0).

P(c,my_id,x2,num,id,r1)  :- P(c,my_id,x1,num,id,r0) , \+(my_id = 0) ,
                            (id = 0) , (c - x2 =< 1) , (c - x2 = 0) , (r1 = 1) , (r0 = 0).
P(c,my_id,x2,num,id2,r2) :- P(c,my_id,x1,num,id1,r1) , ((c - x1) =< 1) , (c - x2 = 0) , (id2 = my_id) , (r1 = 1) , (r2 = 2).
P(c,my_id,x2,num,id,r1)  :- P(c,my_id,x1,num,id,r2) , (id = 0) , ((c - x2) =< 1) , ((c - x2) = 0) , (r1 = 1) , (r2 = 2).
P(c,my_id,x,num,id,r3)   :- P(c,my_id,x,num,id,r2) , (c - x > 1) , (id = my_id) , (r2 = 2) , (r3 = 3).
P(c,my_id,x,num2,id,r4)  :- P(c,my_id,x,num1,id,r3) , (num2 = num1 + 1) , (r3 = 3) , (r4 = 4).
P(c,my_id,x,num2,id2,r0) :- P(c,my_id,x,num1,id1,r4) , (id2 = 0) , (num2 = 0) , (r4 = 4) , (r0 = 0).

P(c2,my_id,x,num,id,t)   :- (c2 >= c1) , \+(t = 1) , P(c1,my_id,x,num,id,t).
P(c2,my_id,x,num,id,t)   :- (c2 >= c1) , (c2 - x =< 1) , (t = 1) , P(c1,my_id,x,num,id,t).


p(A,D,E,B,C,F) :- (C = A),\+((B = 0)),(D = 0),(F = 0).
p(A,D,E,B,C,F) :- p(A,D,E,B,G,H),\+((B = 0)),(E = 0),((A - C) =< 1),((A - C) = 0),(F = 1),(H = 0).
p(A,D,E,B,C,F) :- p(A,D,H,B,G,I),((A - G) =< 1),((A - C) = 0),(E = B),(I = 1),(F = 2).
p(A,D,E,B,C,F) :- p(A,D,E,B,G,H),(E = 0),((A - C) =< 1),((A - C) = 0),(F = 1),(H = 2).
p(A,D,E,B,C,F) :- p(A,D,E,B,C,G),((A - C) > 1),(E = B),(G = 2),(F = 3).
p(A,D,E,B,C,F) :- p(A,G,E,B,C,H),(D = (G + 1)),(H = 3),(F = 4).
p(A,D,E,B,C,F) :- p(A,G,H,B,C,I),(E = 0),(D = 0),(I = 4),(F = 0).
p(A,D,E,B,C,F) :- (A >= G),\+((F = 1)),p(G,D,E,B,C,F).
p(A,D,E,B,C,F) :- (A >= G),((A - C) =< 1),(F = 1),p(G,D,E,B,C,F).

false :- p(A,D,E,B,C,F),(D > 1).

*/

  //////////////////////////////////////////////////////////////////////////////
  
  {
  println("Simplified train crossing example for FM submission")
  
  ap.util.Debug enableAllAssertions true

  val train = for (i <- 0 to 4) yield (new Predicate("train" + i, 1 + 2))
  val gate  = for (i <- 0 to 5) yield (new Predicate("gate" + i, 1 + 2))
  
  val c = new ConstantTerm("c")
  val n = new ConstantTerm("n")
  val x = new ConstantTerm("x")
  val x1 = new ConstantTerm("x1")
  val x2 = new ConstantTerm("x2")
  val y = new ConstantTerm("y")
  val id  = new ConstantTerm("id")
  val id1 = new ConstantTerm("id1")
  val id2 = new ConstantTerm("id2")

  val go = new CommChannel("go")
  val appr = new CommChannel("appr")
  val leave = new CommChannel("leave")
  val stop = new CommChannel("stop")

  val gateProcess = List(

    (gate(0)(c, n, c) :- 
        (true),                                                                                     NoSync),
        
    (gate(1)(c, 0, y) :-
        gate(0)(c, n, y),                                                                           NoSync),
        
/*    (gate(2)(c, n, y) :-
        (gate(1)(c, n, y),
        !(n === 0)),                                                                                NoSync),
        
    (gate(3)(c, n, y) :-
        (gate(1)(c, n, y),
        (n === 0)),                                                                                 NoSync),
  */      
    (gate(4)(c, n, y) :-
        (gate(1)(c, n, y), n =/= 0),                                                                         Send(go)),

    (gate(4)(c, n + 1, y) :-
        (gate(1)(c, n, y), n === 0),                                                                         Receive(appr)),
        
    (gate(1)(c, n - 1, y) :-
        (gate(4)(c, n, y)),                                                                         Receive(leave)),
        
    (gate(5)(c, n + 1, c) :-
        (gate(4)(c, n, y)),                                                                         Receive(appr)),
        
    (gate(4)(c, n, c) :-
        (gate(5)(c, n, y)),                                                                         Send(stop))

  )
  
  val trainProcess = List(

    (train(0)(c, id, c) :- 
        true,                                                                                       NoSync),
        
    (train(2)(c, id, c) :- 
        (train(0)(c, id, x)),                                                                       Send(appr)),
        
    (train(1)(c, id, c) :- 
        (train(2)(c, id, x),
         c - x >= 10),                                                                              NoSync),
         
    (train(0)(c, id, c) :- 
        (train(1)(c, id, x),
         c - x >= 3),                                                                               Send(leave)),
         
    (train(3)(c, id, c) :- 
        (train(2)(c, id, x),
         c - x <= 10),                                                                              Receive(stop)),
         
    (train(4)(c, id, c) :- 
        (train(3)(c, id, x)),                                                                       Receive(go)),
        
    (train(1)(c, id, c) :- 
        (train(4)(c, id, x),
        c - x >= 7),                                                                                NoSync)

  )

  val timeInvs = List(
    (c - y <= 5)    :- gate(5)(c, n, y),
    (c - x <= 5)    :- train(1)(c, id, x),
    (c - x <= 20)   :- train(2)(c, id, x),
    (c - x <= 15)   :- train(4)(c, id, x)
  )

  val assertions =
    List(false :- (train(1)(c, id1, x1),
                   train(1)(c, id2, x2)))

  val system =
    System(
      List((gateProcess, Singleton), (trainProcess, Infinite)),
      1, 
      None,
      DiscreteTime(0),
      timeInvs,
      assertions)

    // can we get deadlocks?
//    List(false :- (train(1)(c, id1, x1),
//                   gate(1)(c, n, y)))

  new VerificationLoop(system)

  }

  //////////////////////////////////////////////////////////////////////////////

  {
  println("Monolithic version of Fischer")

  val A = new ConstantTerm("A")
  val B = new ConstantTerm("B")
  val C = new ConstantTerm("C")
  val D = new ConstantTerm("D")
  val E = new ConstantTerm("E")
  val F = new ConstantTerm("F")
  val G = new ConstantTerm("G")
  val H = new ConstantTerm("H")
  val I = new ConstantTerm("I")

  val p = new Predicate("p", 6)

  val c1 = p(A,D,E,B,C,F) :- ((C === A) ,  !((B === 0)) ,  (D === 0) ,  (F === 0))
  val c2 = p(A,D,E,B,C,F) :- (p(A,D,E,B,G,H), !((B === 0)), (E === 0), ((A - C) <= 1), ((A - C) === 0), (F === 1), (H === 0))
  val c3 = p(A,D,E,B,C,F) :- (p(A,D,H,B,G,I), ((A - G) <= 1), ((A - C) === 0), (E === B), (I === 1), (F === 2))
  val c4 = p(A,D,E,B,C,F) :- (p(A,D,E,B,G,H), (E === 0), ((A - C) <= 1), ((A - C) === 0), (F === 1), (H === 2))
  val c5 = p(A,D,E,B,C,F) :- (p(A,D,E,B,C,G), ((A - C) > 1), (E === B), (G === 2), (F === 3))
  val c6 = p(A,D,E,B,C,F) :- (p(A,G,E,B,C,H), (D === (G + 1)), (H === 3), (F === 4))
  val c7 = p(A,D,E,B,C,F) :- (p(A,G,H,B,C,I), (E === 0), (D === 0), (I === 4), (F === 0))

  val timeInv = false :- (p(A,D,E,B,C,F), !((F === 1) ==> ((A - C) <= 1)))

  val assertion = false :- (p(A,D,E,B,C,F), D > 1)

  new VerificationLoop(System(
                            List((for (c <- List(c1, c2, c3, c4, c5, c6, c7))
                                    yield (c, NoSync),
                                  Infinite)),
                            3, None,
                            DiscreteTime(0),
                            List(timeInv),
                            List(assertion)))

/*  val enc =
    new ParametricEncoder(System(
                            List((for (c <- List(c1, c2, c3, c4, c5, c6, c7))
                                    yield (c, NoSync),
                                  Infinite)),
                            3, None,
                            DiscreteTime(0),
                            List(timeInv)),
                          List(assertion),
                          List(List(2)))

  solve(enc) */
  }

  //////////////////////////////////////////////////////////////////////////////

  println

  {
  println("Fischer with one predicate per control state")

  val A = new ConstantTerm("A")
  val B = new ConstantTerm("B")
  val C = new ConstantTerm("C")
  val D = new ConstantTerm("D")
  val E = new ConstantTerm("E")
  val F = new ConstantTerm("F")
  val G = new ConstantTerm("G")
  val H = new ConstantTerm("H")
  val I = new ConstantTerm("I")

  val p0 = new Predicate("p0", 6)
  val p1 = new Predicate("p1", 6)
  val p2 = new Predicate("p2", 6)
  val p3 = new Predicate("p3", 6)
  val p4 = new Predicate("p4", 6)


  val c1 = p0(A,D,E,B,C,F) :- ((C === A) ,  !((B === 0)) ,  (D === 0) ,  (F === 0))
  val c2 = p1(A,D,E,B,C,F) :- (p0(A,D,E,B,G,H),!((B === 0)), (E === 0), ((A - C) <= 1), ((A - C) === 0), (F === 1), (H === 0))
  val c3 = p2(A,D,E,B,C,F) :- (p1(A,D,H,B,G,I),((A - G) <= 1), ((A - C) === 0), (E === B), (I === 1), (F === 2))
  val c4 = p1(A,D,E,B,C,F) :- (p2(A,D,E,B,G,H),(E === 0), ((A - C) <= 1), ((A - C) === 0), (F === 1), (H === 2))
  val c5 = p3(A,D,E,B,C,F) :- (p2(A,D,E,B,C,G),((A - C) > 1), (E === B), (G === 2), (F === 3))
  val c6 = p4(A,D,E,B,C,F) :- (p3(A,G,E,B,C,H),(D === (G + 1)), (H === 3), (F === 4))
  val c7 = p0(A,D,E,B,C,F) :- (p4(A,G,H,B,C,I),(E === 0), (D === 0), (I === 4), (F === 0))

  val timeInv = false :- (p1(A,D,E,B,C,F), !((A - C) <= 1))

  val assertion = false :- (p4(A,D,E,B,C,F) & D > 1)

  new VerificationLoop(System(
                          List((for (c <- List(c1, c2, c3, c4, c5, c6, c7))
                                  yield (c, NoSync),
                                Infinite)),
                          3, None,
                          DiscreteTime(0),
                          List(timeInv),
                          List(assertion)))

/*
  val enc =
  new ParametricEncoder(System(
                          List((for (c <- List(c1, c2, c3, c4, c5, c6, c7))
                                  yield (c, NoSync),
                                Infinite)),
                          3, None,
                          DiscreteTime(0),
                          List(timeInv)),
                        List(assertion),
                        List(List(2)))

  solve(enc) */
  }

  //////////////////////////////////////////////////////////////////////////////

  println

  {
  println("Fischer with one predicate per control state, parametrised delays")

  val A = new ConstantTerm("A")
  val B = new ConstantTerm("B")
  val C = new ConstantTerm("C")
  val D = new ConstantTerm("D")
  val E = new ConstantTerm("E")
  val F = new ConstantTerm("F")
  val G = new ConstantTerm("G")
  val H = new ConstantTerm("H")
  val I = new ConstantTerm("I")
  val delay1 = new ConstantTerm("delay1")
  val delay2 = new ConstantTerm("delay2")

  val p0 = new Predicate("p0", 8)
  val p1 = new Predicate("p1", 8)
  val p2 = new Predicate("p2", 8)
  val p3 = new Predicate("p3", 8)
  val p4 = new Predicate("p4", 8)


  val c1 = p0(A,D,E,delay1,delay2,B,C,F) :- ((C === A) ,  !((B === 0)) ,  (D === 0) ,  (F === 0))
  val c2 = p1(A,D,E,delay1,delay2,B,C,F) :- (p0(A,D,E,delay1,delay2,B,G,H),!((B === 0)), (E === 0), ((A - C) === 0), (F === 1), (H === 0))
  val c3 = p2(A,D,E,delay1,delay2,B,C,F) :- (p1(A,D,H,delay1,delay2,B,G,I),((A - G) <= delay1), ((A - C) === 0), (E === B), (I === 1), (F === 2))
  val c4 = p1(A,D,E,delay1,delay2,B,C,F) :- (p2(A,D,E,delay1,delay2,B,G,H),(E === 0), ((A - C) === 0), (F === 1), (H === 2))
  val c5 = p3(A,D,E,delay1,delay2,B,C,F) :- (p2(A,D,E,delay1,delay2,B,C,G),((A - C) > delay2), (E === B), (G === 2), (F === 3))
  val c6 = p4(A,D,E,delay1,delay2,B,C,F) :- (p3(A,G,E,delay1,delay2,B,C,H),(D === (G + 1)), (H === 3), (F === 4))
  val c7 = p0(A,D,E,delay1,delay2,B,C,F) :- (p4(A,G,H,delay1,delay2,B,C,I),(E === 0), (D === 0), (I === 4), (F === 0))

  val timeInv = ((A - C) <= delay1) :- p1(A,D,E,delay1,delay2,B,C,F)

  val assertion = (D <= 1) :- p4(A,D,E,delay1,delay2,B,C,F)

  new VerificationLoop(System(
                          List((for (c <- List(c1, c2, c3, c4, c5, c6, c7))
                                  yield (c, NoSync),
                                Infinite)),
                          5, Some({ case Seq(_, _, _, delay1, delay2) =>
                                      delay1 > 0 & delay2 >= delay1 }),
                          DiscreteTime(0),
                          List(timeInv),
                          List(assertion)))

/*
  val enc =
  new ParametricEncoder(System(
                          List((for (c <- List(c1, c2, c3, c4, c5, c6, c7))
                                  yield (c, NoSync),
                                Infinite)),
                          5, Some({ case Seq(_, _, _, delay1, delay2) =>
                                      delay1 > 0 & delay2 >= delay1 }),
                          DiscreteTime(0),
                          List(timeInv)),
                        List(assertion),
                        List(List(2)))

  solve(enc) */
  }

  //////////////////////////////////////////////////////////////////////////////

  println

  {
  println("Finite Fischer instances")

  val A = new ConstantTerm("A")
  val B = new ConstantTerm("B")
  val C = new ConstantTerm("C")
  val D = new ConstantTerm("D")
  val E = new ConstantTerm("E")
  val F = new ConstantTerm("F")
  val G = new ConstantTerm("G")
  val H = new ConstantTerm("H")
  val I = new ConstantTerm("I")
  
  def genFischerProcess(id : ITerm) : (Process, Seq[Clause], Predicate) = {
    val p0 = new Predicate("p0", 5)
    val p1 = new Predicate("p1", 5)
    val p2 = new Predicate("p2", 5)
    val p3 = new Predicate("p3", 5)
    val p4 = new Predicate("p4", 5)
  
    val c1 = p0(A,D,E,C,F) :- ((C === A) ,  (D === 0) ,  (F === 0))
    val c2 = p1(A,D,E,C,F) :- (p0(A,D,E,G,H), (E === 0), ((A - C) <= 1), ((A - C) === 0), (F === 1), (H === 0))
    val c3 = p2(A,D,E,C,F) :- (p1(A,D,H,G,I),((A - G) <= 1), ((A - C) === 0), (E === id), (I === 1), (F === 2))
    val c4 = p1(A,D,E,C,F) :- (p2(A,D,E,G,H),(E === 0), ((A - C) <= 1), ((A - C) === 0), (F === 1), (H === 2))
    val c5 = p3(A,D,E,C,F) :- (p2(A,D,E,C,G),((A - C) > 1), (E === id), (G === 2), (F === 3))
    val c6 = p4(A,D,E,C,F) :- (p3(A,G,E,C,H),(D === (G + 1)), (H === 3), (F === 4))
    val c7 = p0(A,D,E,C,F) :- (p4(A,G,H,C,I),(E === 0), (D === 0), (I === 4), (F === 0))
  
    (for (c <- List(c1, c2, c3, c4, c5, c6, c7)) yield (c, NoSync),
     List(false :- (p1(A,D,E,C,F), !((A - C) <= 1))),
     p4)
  }

  for (N <- List(2, 3, 4)) {
    println
    println("Fischer " + N)

    val (processes, timeInvs, critical) = (for (i <- 1 to N) yield genFischerProcess(i)).toList.unzip3
  
    val assertions =
      (for (List(p, q) <- critical.toList combinations 2)
       yield (false :- (p(A,D,E,C,F) & q(A,D,E,C,F)))).toList

    new VerificationLoop(System(for (p <- processes) yield (p, Singleton),
                                 3, None,
                                 DiscreteTime(0),
                                 timeInvs.flatten,
                                 assertions))

/*
    val enc =
    new ParametricEncoder(System(for (p <- processes) yield (p, Singleton),
                                 3, None,
                                 DiscreteTime(0),
                                 timeInvs.flatten),
                          assertions,
                            List(for (_ <- 1 to N) yield 1)
                          )

    solve(enc) */
  }
  }

  println

  {
  println("Artificial synchronisation example")

  val rec = new ConstantTerm("rec")
  val snt = new ConstantTerm("snt")
  val C = new ConstantTerm("C")
  val n = new ConstantTerm("n")
  val id = new ConstantTerm("id")

  val c = new CommChannel("c")

  val p0 = new Predicate("p0", 5)
  val p1 = new Predicate("p1", 5)
  val p2 = new Predicate("p2", 5)

  val enc =
  new ParametricEncoder(System(
                        List((
                        List((p0(C, 0, 0, 0, id) :- true,                         NoSync),
                             (p1(C, n+1, 1, rec, id) :- p0(C, n, 0, rec, id),     Send(c)),
                             (p2(C, n+1, snt, 1, id) :- p0(C, n, snt, 0, id),     Receive(c)),
                             (p0(C, n-1, 0, rec, id) :- p1(C, n, snt, rec, id),   NoSync),
                             (p0(C, n-1, snt, 0, id) :- p2(C, n, snt, rec, id),   NoSync)),
                        Infinite)),
                        4, None,
                        DiscreteTime(0),
                        List(),
                        List(false :- (p0(C, n, snt, rec, id), n > 2),
                             false :- (p1(C, n, snt, rec, id), n > 2),
                             false :- (p2(C, n, snt, rec, id), n > 2))),
                        List(List(1)))

  solve(enc)
  }
}
