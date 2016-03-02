/**
 * Copyright (c) 2011-2014 Pavle Subotic. All rights reserved.
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

object MainBenchmarksBuggy extends App {

  import HornClauses._
  import IExpression._
  import ParametricEncoder._
  
  ap.util.Debug enableAllAssertions false

  ////////////////////////////////////////////////////////////////
  // Benchmarks - turn off = false or on = true
  val fischerFlagB = false
  val csmaFlagB = false
  val tta2FlagB = false
  val lynchFlagB = false
  val lynch2FlagB = false
  val trainFlagB = false
  val bipFlagB = false
  ////////////////////////////////////////////////////////////////

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

  // Fisher Buggy  Protocol
  {
    println("Fisher Buggy example")

    // global
    val C = new ConstantTerm("C")
    val U = new ConstantTerm("U")
    val gid = new ConstantTerm("gid")
    val gidn = new ConstantTerm("gidn")
    val num = new ConstantTerm("num")
    val numn = new ConstantTerm("numn")

    // local
    val idn = new ConstantTerm("idn")
    val id = new ConstantTerm("id")
    val xn = new ConstantTerm("xn")
    val x = new ConstantTerm("x")
    val l1 = new ConstantTerm("l1")
    val l2 = new ConstantTerm("l2")

    val p = for (i <- 0 to 4) yield (new Predicate("p" + i, 7))
    val obs = for (i <- 0 to 1) yield (new Predicate("obs" + i, 5))

    val c1 = p(0)(C, U, num,  gid, id, x,  l1) :- ((x === C), !((id === 0)), (num === 0), (l1 === 0))
    val c2 = p(1)(C, U, num,  gid, id, xn, l2) :- (p(0)(C, U, num, gid, id, x, l1), !((id === 0)), (gid === 0), 
                                                  ((C - xn) <= U*1), ((C - xn) === 0), (l1 === 0), (l2 === 1))

    val c3 = p(2)(C, U, num,  gidn, id, xn, l2) :- (p(1)(C, U, num, gid, id, x, l1), ((C - x) <= U*1), (C - xn === 0), (gidn === id),  (l1 === 1), (l2 === 2))
    val c4 = p(3)(C, U, num,  gid, id, x,  l2) :- (p(2)(C, U, num, gid, id, x, l1),/* (gid === id),*/  ((C - x) > U*1), (l1 === 2), (l2 === 3))
    val c7 = p(1)(C, U, num,  gid, id, xn, l2) :- (p(2)(C, U, num, gid, id, x, l1), (gid === 0), ((C - xn) <= U*1), (C - xn === 0), (l1 === 2), (l2 === 1))
    val c5 = p(4)(C, U, numn, gid, id,  x, l2) :- (p(3)(C, U, num, gid, id, x, l1), (numn === num + 1), (l2 === 4), (l1 === 3))

    val c6 = p(0)(C, U, numn, gidn,id, x,  l2) :- (p(4)(C, U, num, gid, id, x, l1), (gidn === 0), (numn === 0), (l2 === 0), (l1 === 4))

    val o1= obs(0)(C, U, num, gid, 0) :- (num === 0)
    val o2= obs(1)(C, U, numn, gid, 1) :- (obs(0)(C, U, num, gid, 0), num > 1) 

    val timeInv =  false :- (p(1)(C, U, num, gid, id, x, l1), !((C - x) <= U*1))

    val assertion = false :- (obs(0)(C, U, num, gid, 0) & num > 1)

    val system = System(
                            List((for (c <- List(c1, c2, c3, c4, c5, c6, c7)) // p
                                    yield (c, NoSync),
                                  Infinite)
                                  ,(for (o <- List(o1, o2))
                                    yield (o, NoSync),
                                  Singleton)
                                ), 
                            4, None,
                            ContinuousTime(0, 1),
                            List(timeInv), List(assertion))
    if (fischerFlagB)
      new VerificationLoop(system) 
  }


  println

  // CSMA Buggy Protocol
  {
    println("CSMA Buggy example")

    // Constants
    val lambda = 808
    val sigma = 26

    // Processes
    val sender = for (i <- 0 to 3) yield (new Predicate("sender" + i, 7))
    val bus  = for (i <- 0 to 2) yield (new Predicate("bus" + i, 6))

    val C = new ConstantTerm("C") // global clock
    val U = new ConstantTerm("U")

    val c = new ConstantTerm("c1") 
    val cn = new ConstantTerm("c2")

    val err = new ConstantTerm("err") 
    val errn = new ConstantTerm("err")

    val gid = new ConstantTerm("gid") 
    val gidn = new ConstantTerm("gidn") 
    val id = new ConstantTerm("id")

    val l1 = new ConstantTerm("l1") // loc 1
    val l2 = new ConstantTerm("l2") // loc 2

    // channels (non broadcast)
    val begin = new CommChannel("begin")
    val send = new CommChannel("send")
    val busy = new CommChannel("busy")
    val end = new CommChannel("end")

    // broadcast channel via barrier
    val bcChan = new SimpleBarrier("cd", List(sender.toSet, bus.toSet)) // domain is all states of bus and incomming states of sender

    val senderProcess = List(
      (sender(0)(C, U, err, gid, id, c, l1) :- ((err === 0), (C - c === 0), (l1 === 0)), NoSync),

      (sender(0)(C, U, err, gidn, id, cn, l2) :-
         (sender(0)(C, U, err, gid, id, c, l1), (C - cn === 0) , (gidn === id), (l1 === 0)), 
          BarrierSync(bcChan)),

      (sender(1)(C, U, errn, gid, id, cn, l2) :-
         (sender(0)(C, U, err, gid, id, c, l1), (C - cn === 0), (errn === err + 1), (C - cn <= U*lambda), (l2 === 1), (l1 === 0)),
          Send(begin)),

      (sender(0)(C, U, errn, gid, id, cn, l2) :-
         (sender(1)(C, U, err, gid, id, c, l1), (C - c === U*lambda), (errn === err - 1), (C - cn === 0), (l1 === 1), (l2 === 0)), 
         Send(end)),

      (sender(2)(C, U, err, gid, id, cn, l2) :-
         (sender(0)(C, U, err, gid, id, c, l1), (C - cn === 0), (C - cn <= U*2*sigma), (l1 === 0), (l2 === 2)),
         BarrierSync(bcChan)),

      (sender(2)(C, U, err, gid, id, cn, l2) :-
         (sender(0)(C, U, err, gid, id, c, l1), (C - cn === 0), (C - cn <= U*2*sigma), (l1 === 0), (l2 === 2)),
         Receive(busy)),

      (sender(2)(C, U, err, gid, id, cn, l2) :-
         (sender(2)(C, U, err, gid, id, c, l1), (C - cn === 0), (C - cn <= U*2*sigma), (l1 === 2), (l2 === 2)),
         BarrierSync(bcChan)),

      (sender(1)(C, U, errn, gid, id, cn, l2) :-
         (sender(2)(C, U, err, gid, id, c, l1), (C - cn === 0), (errn === err + 1), (C - c <= U*2*sigma), (C - cn <= U*lambda), (l1 === 2), (l2 === 1)),
         Send(begin)),

      (sender(2)(C, U, errn, gid, id, cn, l2) :-
         (sender(1)(C, U, err, gid, id, c, l1), (C - cn === 0), (errn === err - 1), (C - cn < U*2*sigma), (l1 === 1), (l2 === 2)),
         BarrierSync(bcChan)),

      (sender(3)(C, U, err, gid, id, c, l2) :-
         (sender(1)(C, U, err, gid, id, c, l1), (err > 1), (C - c > U*2*sigma), (l1 === 1), (l2 === 3)),
         NoSync)
    )

    val busProcess = List(
      (bus(0)(C, U, err, gid, c, l1) :- ((C === c), (err === 0), (l1 === 0)), 
      NoSync),

      (bus(1)(C, U, err, gid, cn, l2) :-
         (bus(0)(C, U, err, gid, c, l1), (C - cn === 0), (l1 === 0), (l2 === 1)), 
         Receive(begin)),

      (bus(0)(C, U, err, gid, cn, l2) :-
         (bus(1)(C, U, err, gid, c, l1), (C - cn === 0), (l1 === 1), (l2 === 0)), 
         Receive(end)),

      (bus(1)(C, U, err, gid, c, l2) :-
         (bus(1)(C, U, err, gid, c, l1), (C - c >= U*sigma), (l1 === 1), (l2 === 1)), 
         Send(busy)),

      (bus(2)(C, U, err, gid, cn, l2) :-
         (bus(1)(C, U, err, gid, c, l1), (C - c < U*sigma), (C - cn < U*sigma), (C - cn === 0), (l1 === 1), (l2 === 1)), 
         Receive(begin)),

      (bus(0)(C, U, err, gid, cn, l2) :-
         (bus(2)(C, U, err, gid, c, l1), (C - c < U*sigma), (C - cn === 0), (l1 === 2), (l2 === 0)), 
         BarrierSync(bcChan))
    )

    val timeInvs = List(
      (C - c <= U*lambda) :- sender(1)(C, U, err, gid, id, c, l1),
      (C - c < U*2*sigma) :- sender(2)(C, U, err, gid, id, c, l1)
      //,(C - c < U*sigma) :- bus(2)(C, U, err, gid, c, l1)
    )

    val assertions =
      List(false :- (sender(3)(C, U, err, gid, id, c, l1), err > 1))

    val system =
    System(
      List(
           (senderProcess, Infinite), 
           (busProcess, Singleton)
          ),
      4, None, ContinuousTime(0, 1), timeInvs, assertions)

    if (csmaFlagB)
      new VerificationLoop(system)

  }


  println
  // Lynch Shavit Buggy Protocol
  {
    println("Lynch-Shavit Buggy example")

    val T = 1; // Time bound constant

    // global
    val C = new ConstantTerm("C")
    val U = new ConstantTerm("U")
    val count = new ConstantTerm("count")
    val countn = new ConstantTerm("countn")
    val v1 = new ConstantTerm("v1")
    val v1n = new ConstantTerm("v1n")
    val v2 = new ConstantTerm("v2")
    val v2n = new ConstantTerm("v2n")

    // local
    val id = new ConstantTerm("id")
    val cn = new ConstantTerm("cn")
    val c = new ConstantTerm("c")
    val l1 = new ConstantTerm("l1")
    val l2 = new ConstantTerm("l2")

    val p = for (i <- 0 to 8) yield (new Predicate("p" + i, 8))
    val obs = for (i <- 0 to 1) yield (new Predicate("obs" + i, 6))

    val c1 = p(0)(C, U, count, v1, v2, id, c, l1) :- ((c === C), (count === 0), (v1 === -1), (v2 === 0), (l1 === 0))

    val c2 = p(1)(C, U, count, v1, v2, id, cn, l2) :- (p(0)(C, U, count, v1, v2,  id, c, l1), 
               (v1 === -1), (id > -1), ((C - cn) === 0), ((C - cn) <= U*T), (l1 === 0), (l2 === 1))

    val c3 = p(2)(C, U, count, v1n, v2,  id, cn,  l2) :- (p(1)(C, U, count, v1, v2,  id, c,  l1),
               (C - c <= U*T), (v1n === id), (C - cn === 0), (l1 === 1), (l2 === 2))

    val c4 = p(0)(C, U, count, v1, v2, id, c, l2) :- (p(2)(C, U, count, v1, v2, id, c, l1),
               !(v1 === id), (l1 === 2), (l2 === 0))

    val c5 = p(3)(C, U, count, v1, v2,  id, c,  l2) :- (p(2)(C, U, count, v1, v2,  id, c,  l1),
               /*(v1 === id),*/ (C - c > U*T), (l1 === 2), (l2 === 3))

    val c6 = p(0)(C, U, count, v1, v2,  id, c,  l2) :- (p(3)(C, U, count, v1, v2,  id, c,  l1),
               (v2 === 1), (l1 === 3), (l2 === 0))

    val c7 = p(4)(C, U, count, v1, v2,  id, cn,  l2) :- (p(3)(C, U, count, v1, v2,  id, c,  l1),
               (v2 === 0), (C - cn === 0), ((C - cn) <= U*T), (l1 === 3), (l2 === 4))

    val c8 = p(5)(C, U, count, v1, v2n,  id, cn,  l2) :- (p(4)(C, U, count, v1, v2,  id, c,  l1),
               (v2n === 1), (C - cn === 0), ((C - c) <= U*T), (l1 === 4), (l2 === 5))

    val c9 = p(0)(C, U, count, v1, v2,  id, c,  l2) :- (p(5)(C, U, count, v1, v2,  id, c,  l1),
               !(v1 === id), (l1 === 5), (l2 === 0))

   // going to CS
    val c10 = p(6)(C, U, countn, v1, v2,  id, c,  l2) :- (p(5)(C, U, count, v1, v2,  id, c,  l1),
               (countn === count + 1), /*(v1 === id),*/ (l1 === 5), (l2 === 6))
   // out of CS
   val c11 = p(7)(C, U, countn, v1, v2,  id, cn,  l2) :- (p(6)(C, U, count, v1, v2,  id, c,  l1),
               (countn === count - 1), (C - cn === 0), (l1 === 6), (l2 === 7))

   // 7 to 8
   val c12 = p(8)(C, U, count, v1, v2n,  id, cn, l2) :- (p(7)(C, U, count, v1, v2,  id, c, l1),
              (C - cn === 0), (v2n === 0), (C - c <= U*T), (l1 === 7), (l2 === 8))

   // 8  to 0
   val c13 = p(0)(C, U, count, v1, v2,  id, c,  l2) :- (p(8)(C, U, count, v1, v2,  id, c,  l1),
               (v1n === 0), (C - c <= U*T), (l1 === 8), (l2 === 0))

   val o1= obs(0)(C, U, count, v1, v2, 0) :- (count === 0)
   val o2= obs(1)(C, U, countn, v1, v2, 1) :- (obs(0)(C, U, count, v1, v2, 0), count > 1) 

    val timeInv =  List(false :- (p(1)(C, U, count, v1, v2, id, c,  l1), ((C - c) <= U*T)), 
                        false :- (p(4)(C, U, count, v1, v2, id, c,  l1), ((C - c) <= U*T))
                        )

    //val assertion = false :- (p(6)(C, U, count, v1, v2, id, c,  l1) & count > 1)
    val assertion = false :- (obs(0)(C, U, count, v1, v2, 0) & count > 1)

    val system = System(
                            List((for (c <- List(c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13)) // p
                                    yield (c, NoSync),
                                  Infinite)
                                  ,(for (o <- List(o1, o2))
                                    yield (o, NoSync),
                                  Singleton)
                                ), 
                            5, None,
                            ContinuousTime(0, 1),
                            timeInv, List(assertion))
    if(lynchFlagB)
      new VerificationLoop(system) 
  }

  println

  // Lynch Shavit Buggy Protocol
  {
    println("Lynch-Shavit Buffy example")

    val T = 1; // Time bound constant

    // global
    val C = new ConstantTerm("C")
    val U = new ConstantTerm("U")
    val count = new ConstantTerm("count")
    val countn = new ConstantTerm("countn")
    val v1 = new ConstantTerm("v1")
    val v1n = new ConstantTerm("v1n")
    val v2 = new ConstantTerm("v2")
    val v2n = new ConstantTerm("v2n")

    // local
    val id = new ConstantTerm("id")
    val id2 = new ConstantTerm("id")
    val cn = new ConstantTerm("cn")
    val c = new ConstantTerm("c")
    val l1 = new ConstantTerm("l1")
    val l2 = new ConstantTerm("l2")

    val p = for (i <- 0 to 8) yield (new Predicate("p" + i, 6))
    //val obs = for (i <- 0 to 1) yield (new Predicate("obs" + i, 6))

    val c1 = p(0)(C, U, v1, v2, id, c) :- ( (id > -1), (c === C), (v1 === -1), (v2 === 0))

    val c2 = p(1)(C, U, v1, v2, id, cn) :- (p(0)(C, U, v1, v2,  id, c), 
               (v1 === -1), (id > -1), ((C - cn) === 0))

    val c3 = p(2)(C, U, v1n, v2,  id, cn) :- (p(1)(C, U, v1, v2,  id, c), (id > -1),
               (C - c <= U*T), (v1n === id), (C - cn === 0))

    val c4 = p(0)(C, U, v1, v2, id, c) :- (p(2)(C, U, v1, v2, id, c), (id > -1),
               !(v1 === id))

    val c5 = p(3)(C, U, v1, v2,  id, c) :- (p(2)(C, U, v1, v2,  id, c), (id > -1),
               /*(v1 === id),*/ (C - c > U*T))

    val c6 = p(0)(C, U, v1, v2, id, c) :- (p(3)(C, U, v1, v2,  id, c), (id > -1),
               (v2 === 1))

    val c7 = p(4)(C, U, v1, v2, id, cn) :- (p(3)(C, U, v1, v2,  id, c), (id > -1),
               (v2 === 0), (C - cn === 0))

    val c8 = p(5)(C, U, v1, v2n,  id, cn) :- (p(4)(C, U, v1, v2,  id, c), (id > -1),
               (v2n === 1), (C - cn === 0), ((C - c) <= U*T))

    val c9 = p(0)(C, U, v1, v2,  id, c) :- (p(5)(C, U, v1, v2,  id, c), (id > -1),
               !(v1 === id))

   // going to CS
    val c10 = p(6)(C, U, v1, v2,  id, c) :- (p(5)(C, U, v1, v2,  id, c), (id > -1)
               /*,(v1 === id)*/)
   // out of CS
   val c11 = p(7)(C, U, v1, v2,  id, cn) :- (p(6)(C, U, v1, v2,  id, c), (id > -1),
               (C - cn === 0))

   // 7 to 8
   val c12 = p(8)(C, U, v1, v2n,  id, cn) :- (p(7)(C, U, v1, v2,  id, c), (id > -1),
              (C - cn === 0), (v2n === 0))

   // 8  to 0
   val c13 = p(0)(C, U, v1, v2, id, cn) :- (p(8)(C, U, v1, v2, id, c), (id > -1),
               (v1n === 0), (C - c <= U*T))

   //val o1= obs(0)(C, U, count, v1, v2, 0) :- (count === 0)
   //val o2= obs(1)(C, U, countn, v1, v2, 1) :- (obs(0)(C, U, count, v1, v2, 0), count > 1) 

    val timeInv =  List()

    val assertion = false :- (p(6)(C, U, v1, v2, id, c) & (p(6)(C, U, v1, v2, id2, c)))
    //val assertion = false :- (obs(0)(C, U, count, v1, v2, 0) & count > 1)

    val system = System(
                            List((for (c <- List(c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13)) // p
                                    yield (c, NoSync),
                                  Infinite)

                                ), 
                            4, None,
                            ContinuousTime(0, 1),
                            timeInv, List(assertion))
    if(lynch2FlagB)
      new VerificationLoop(system) 
  }

  {
    println("Train crossingi buggy example")

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

    (gate(3)(C, U, e, next_waiting_ticket, next_waiting_ticket /*+1*/, next_available_ticket, y) :-
       (gate(5)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),
        next_waiting_ticket /*<*/ > next_available_ticket),                                               NoSync),

    (gate(2)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y) :-
       (gate(5)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y),
        next_waiting_ticket /*===*/ > next_available_ticket),                                             NoSync),

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
        C - x <= U*10 ,e === id),                                                                   Receive(stop)),

    (train(3)(C, U, e, ticket, id, my_ticket, C) :-
       (train(2)(C, U, e, ticket, id, my_ticket, x),
        !(my_ticket === ticket)),                                                                      Receive(go)),

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
      (C - y <= U*5) :- gate(4)(C, U, e, ticket, next_waiting_ticket, next_available_ticket, y)
      ,(C - x <= U*20) :- train(1)(C, U, e, ticket, id, my_ticket, x),
      (C - x <= U*15) :- train(3)(C, U, e, ticket, id, my_ticket, x)
      ,(C - x <= U*5) :- train(0)(C, U, e, ticket, id, my_ticket, x)
    )

    val assertions =
      List(false :- (train(0)(C, U, e, ticket, id, my_ticket, x),
                   train(0)(C, U, e, ticket, id2, my_ticket2, x2)))

    val system =
      System(
        List((gateProcess, Singleton), (trainProcess, Infinite)),
        4, None,
        ContinuousTime(0, 1),
        timeInvs, assertions)

    if(trainFlagB)
      new VerificationLoop(system)
  }

  println 

  {
  println("BIP temperature control system, with discrete time Buggy")

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
    List(false :- (
           l(1)(C, sync, t1), l(4)(C, sync, t2), l(7)(C, sync, th),
           C - th === 900, C - t1 < 3600, C - t2 < 3600))

  val system =
    System(List((Rod1, Singleton),
                (Rod2, Singleton),
                (Controller, Singleton)),
           2, None, DiscreteTime(0), timeInvs, assertions)

  if(bipFlagB)
    new VerificationLoop(system)
  }

  // Buggy TTA 2
  {
    println("TTA example, v2")

    val max_init_time = 300
    val tau_listen = 100
    val tau_coldstart = 50
    val slot_time = 30

    val no_chan = -1
    val cs_frame = 0
    val i_frame = 1

    val node = for (i <- 0 to 4) yield (new Predicate("node" + i, 7 + 3))

    val C = new ConstantTerm("C") // global clock
    val U = new ConstantTerm("U")
    val lock = new ConstantTerm("lock")
//    val N = new ConstantTerm("N")
    val N = 3
    val origin = new ConstantTerm("origin") 
    val originn = new ConstantTerm("originn") 
    val chan = new ConstantTerm("chan")
    val chann = new ConstantTerm("chann")
    val sender = new ConstantTerm("sender")
    val id = new ConstantTerm("id")
    val id2 = new ConstantTerm("id2")
    val slot = new ConstantTerm("slot")
    val slotn = new ConstantTerm("slot")
    val c = new ConstantTerm("c1") 
    val cn = new ConstantTerm("cn")

    val exact_listen_time =
      id * slot_time - slot_time + (N * slot_time * 2)
    val exact_coldstart_time =
      id * slot_time - slot_time + (N * slot_time)

    val inc_slot = ite(slot === (N - 1), 0, slot + 1)
    val inc_slotn = ite(slotn === (N - 1), 0, slotn + 1)

    val bcChan = new SimpleBarrier("bcChan",
              List(Set(node(1), node(2), node(3), node(4))))

    val nodeProcess = List(

      (node(0)(  C, 1, lock, N, no_chan, sender, origin, id, slot, C) :- true,
       NoSync),
      
      (node(1)(  C, U, 0,    N, chan, sender, origin, id, slot, c) :- (
         node(0)(C, U, 0,    N, chan, sender, origin, id, slot, c),
         id >= 0, id < N),
       NoSync),
      
      //////////////////////////////////////////////////////////////////////////

      (node(1)(  C, U, lock, N, chan, sender, origin, id, slot, c) :- (
         node(1)(C, U, lock, N, chan, sender, origin, id, slot, c),
         sender =/= id),
       BarrierSync(bcChan)),

      (node(2)(  C, U, 1,    N, chan, sender, origin, id, slot, C) :- (
         node(1)(C, U, lock, N, chan, sender, origin, id, slot, c)),
       NoSync),
      
      //////////////////////////////////////////////////////////////////////////

      (node(2)(  C, U, lock, N, cs_frame, id,     id,      id, slot, c) :- (
         node(2)(C, U, lock, N, chan,     sender, origin,  id, slot, c)),
       NoSync),
      
      (node(3)(  C, U, lock, N, chan, sender, origin, id, slot, C) :- (
         node(2)(C, U, lock, N, chan, sender, origin, id, slot, c),
         chan === cs_frame /*,sender === id */ /*, origin === id*/,
         C - c >= exact_listen_time),
       BarrierSync(bcChan)),
      
      (node(3)(  C, U, lock, N, chan, sender, origin, id, slot, C) :- (
         node(2)(C, U, lock, N, chan, sender, origin, id, slot, c),
         chan === cs_frame /*,sender =/= id*/),
       BarrierSync(bcChan)),
      
      (node(4)(  C, U, lock, N, chan, sender, origin, id, origin, C) :- (
         node(2)(C, U, lock, N, chan, sender, origin, id, slot,   c),
         chan === i_frame, sender =/= id),
       BarrierSync(bcChan)),
      
      //////////////////////////////////////////////////////////////////////////

      (node(3)(  C, U, lock, N, cs_frame, id,     id,     id, slot, c) :- (
         node(3)(C, U, lock, N, chan,     sender, origin, id, slot, c)),
       NoSync),
      
      (node(3)(  C, U, lock, N, chan, sender, origin, id, slot, C) :- (
         node(3)(C, U, lock, N, chan, sender, origin, id, slot, c),
         chan === cs_frame, sender === id, origin === id,
         C - c >= exact_coldstart_time),
       BarrierSync(bcChan)),
      
      (node(4)(  C, U, lock, N, chan, sender, origin, id, origin, C) :- (
         node(3)(C, U, lock, N, chan, sender, origin, id, slot,   c),
         chan === cs_frame, sender =/= id),
       BarrierSync(bcChan)),
      
      (node(4)(  C, U, lock, N, chan, sender, origin, id, origin, C) :- (
         node(3)(C, U, lock, N, chan, sender, origin, id, slot,   c),
         chan === i_frame, sender =/= id),
       BarrierSync(bcChan)),
      
      //////////////////////////////////////////////////////////////////////////

      (node(4)(  C, U, lock, N, i_frame, id,     id,      id, slot, c) :- (
         node(4)(C, U, lock, N, chan,    sender, origin,  id, slot, c)),
       NoSync),
      
      (node(4)(  C, U, lock, N, chan, sender, origin, id, slot, c) :- (
         node(4)(C, U, lock, N, chan, sender, origin, id, slot, c),
         chan === cs_frame, sender =/= id),
       BarrierSync(bcChan)),
      
      (node(4)(  C, U, lock, N, chan, sender, origin, id, id,   C) :- (
         node(4)(C, U, lock, N, chan, sender, origin, id, id - 1, c),
         chan === i_frame, sender === id, origin === id,
         id > 0,
         C - c >= U * slot_time),
       BarrierSync(bcChan)),
      
      (node(4)(  C, U, lock, N, chan, sender, origin, id, id,   C) :- (
         node(4)(C, U, lock, N, chan, sender, origin, id, N - 1, c),
         chan === i_frame, sender === id, origin === id,
         id === 0,
         C - c >= U * slot_time),
       BarrierSync(bcChan)),
      
      (node(4)(  C, U, lock, N, chan, sender, origin, id, slot + 1, C) :- (
         node(4)(C, U, lock, N, chan, sender, origin, id, slot,     c),
         chan === i_frame, sender =/= id, slot < (N - 1)),
       BarrierSync(bcChan)),

      (node(4)(  C, U, lock, N, chan, sender, origin, id, 0, C) :- (
         node(4)(C, U, lock, N, chan, sender, origin, id, N - 1,     c),
         chan === i_frame, sender =/= id),
       BarrierSync(bcChan))

    )

    val timeInvs = List(
      (C - c <= U * max_init_time) :-
          node(1)(C, U, lock, N, chan, sender, origin, id, slot, c),
      /*(C - c <= U * tau_listen)*/
      (C - c <= exact_listen_time) :-
          node(2)(C, U, lock, N, chan, sender, origin, id, slot, c),
      /*(C - c <= U * tau_coldstart)*/
      (C - c <= exact_coldstart_time) :-
          node(3)(C, U, lock, N, chan, sender, origin, id, slot, c),
      (C - c <= U * slot_time) :-
          node(4)(C, U, lock, N, chan, sender, origin, id, slot, c)
    )

    val assertions = List(
           false :- (node(4)(C, U, lock, N, chan, sender, origin, id, slot, c),
                     node(4)(C, U, lock, N, chan, sender, origin, id2, slotn, cn),
                     id >= 0, id < N, id2 >= 0, id2 < N, slot < slotn)
//             false :- node(4)(C, U, lock, N, chan, sender, origin, id, slot, c)
    )

    val system = System(List((nodeProcess, Infinite)),
                        7, None, DiscreteTime(0), timeInvs, assertions)

    if (tta2FlagB)
      new VerificationLoop(system)
  }

}

