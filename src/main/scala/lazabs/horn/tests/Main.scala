/**
 * Copyright (c) 2011-2020 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.tests

import ap.parser._
import lazabs.horn.bottomup._

object HornPredAbsMain extends App {
  
  import HornClauses._
  import IExpression._
  
  ap.util.Debug enableAllAssertions false

  {

  val x = new ConstantTerm("x")
  val y = new ConstantTerm("y")
  val z = new ConstantTerm("z")
  val a = new ConstantTerm("a")
  
  val r = new Predicate("r", 2)
  val s = new Predicate("s", 2)

  val x1 = new ConstantTerm("x1")
  val y1 = new ConstantTerm("y1")
  val x2 = new ConstantTerm("x2")
  val y2 = new ConstantTerm("y2")
  val x3 = new ConstantTerm("x3")
  val y3 = new ConstantTerm("y3")
  
  val r1 = new Predicate("r1", 4)
  val r2 = new Predicate("r2", 4)

  {
  val c1 = Clause(r(x, y), List(), y === x + 1)
  val c2 = Clause(r(x, y), List(), y === x + 2)
  val c3 = Clause(r(x, z), List(r(x, y), r(y, z)), true)
  val c4 = Clause(s(x, z), List(r(x, y), r(y, z)), true)
  val c5 = Clause(FALSE(), List(s(x, z)), x >= 0 & z <= 0)
  
  val clauses = Seq(c1, c2, c3, c4, c5)

  println("Solving " + clauses + " ...")
  
  val predAbs =
    new HornPredAbs(clauses, Map(), DagInterpolator.interpolatingPredicateGenCEX _)

  println
  predAbs.result match {
    case Right(cex) => {
      println("NOT SOLVABLE")
      cex.prettyPrint
    }
    case Left(solution) =>
      println("SOLVABLE: " + solution)
  }
  }
  
  println
  
  /*
        r1(y1,x1,y3,x3) :- ((y1 == y2) && (x1 == x2)),((x3 == 1) && (y3 == 2))
        r2(y1,x1,y3,x3) :- r1(y1,x1,y2,x2),(x3 == (y2 - 1))
        r2(y1,x1,y3,x3) :- r1(y1,x1,y2,x2),(y3 == (x2 + 1))
        false :- r2(y1,x1,y2,x2),((x2 < 0) && (y2 < 0))
    */    

  {
  val c1 = Clause(r1(y1, x1, y3, x3), List(),
                  ((y1 === y2) & (x1 === x2)) & ((x3 === 1) & (y3 === 2)))
  val c2 = Clause(r2(y1, x1, y3, x3), List(r1(y1, x1, y2, x2)),
                  (x3 === y2 - 1))
  val c3 = Clause(r2(y1, x1, y3, x3), List(r1(y1, x1, y2, x2)),
                  (y3 === x2 + 1))
  val c4 = Clause(FALSE(), List(r2(y1, x1, y2, x2)),
                  (x2 < 0 & y2 < 0))

  val clauses = Seq(c1, c2, c3, c4)
  
  println("Solving " + clauses + " ...")
  
  val predAbs =
    new HornPredAbs(clauses, Map(), DagInterpolator.interpolatingPredicateGenCEX _)

  println
  predAbs.result match {
    case Right(cex) => {
      println("NOT SOLVABLE")
      cex.prettyPrint
    }
    case Left(solution) =>
      println("SOLVABLE: " + solution)
  }
  }

  }
  
  {

  val i0 = new ConstantTerm("i0")
  val t0 = new ConstantTerm("t0")
  val i1 = new ConstantTerm("i1")
  val t1 = new ConstantTerm("t1")
  val n  = new ConstantTerm("n")
  val l  = new ConstantTerm("l")

  val q0 = new Predicate("q0", 6)  // i0, t0, i1, t1, n, l
  val q1 = new Predicate("q1", 6)
  val q2 = new Predicate("q2", 6)
  val q3 = new Predicate("q3", 6)
  val q4 = new Predicate("q4", 6)
  val q5 = new Predicate("q5", 6)
  val q6 = new Predicate("q6", 6)
  val r0 = new Predicate("r0", 6)
  val r1 = new Predicate("r1", 6)
  val r2 = new Predicate("r2", 6)
  val r3 = new Predicate("r3", 6)
  val r4 = new Predicate("r4", 6)
  val r5 = new Predicate("r5", 6)
  val r6 = new Predicate("r6", 6)

  val bound0 : ITerm = 0
  val bound1 : ITerm = 1

  val clauses_init = List(
    Clause(q0(0, 0, 0, 0, 0, 0), List(), true),
    Clause(r0(0, 0, 0, 0, 0, 0), List(), true)
  )

  val clauses_0 = List(
    Clause(q1(i0, t0, i1, t1, n, l), List(q0(i0, t0, i1, t1, n, l)), i0 < bound0),
    Clause(q2(i0, t0, i1, t1, n, 1), List(q1(i0, t0, i1, t1, n, 0)), true),
    Clause(q3(i0, n, i1, t1, n, l),  List(q2(i0, t0, i1, t1, n, l)), true),
    Clause(q4(i0, t0, i1, t1, t0 + 1, l), List(q3(i0, t0, i1, t1, n, l)), true),
    Clause(q5(i0, t0, i1, t1, n, 0), List(q4(i0, t0, i1, t1, n, l)), true),
    Clause(q0(i0 + 1, t0, i1, t1, n, l), List(q5(i0, t0, i1, t1, n, l)), true),
    Clause(q6(i0, t0, i1, t1, n, l), List(q0(i0, t0, i1, t1, n, l)), i0 >= bound0)
  )

  val clauses_1 = List(
    Clause(r1(i0, t0, i1, t1, n, l), List(r0(i0, t0, i1, t1, n, l)), i1 < bound1),
    Clause(r2(i0, t0, i1, t1, n, 1), List(r1(i0, t0, i1, t1, n, 0)), true),
    Clause(r3(i0, t0, i1, n, n, l),  List(r2(i0, t0, i1, t1, n, l)), true),
    Clause(r4(i0, t0, i1, t1, t1 + 1, l), List(r3(i0, t0, i1, t1, n, l)), true),
    Clause(r5(i0, t0, i1, t1, n, 0), List(r4(i0, t0, i1, t1, n, l)), true),
    Clause(r0(i0, t0, i1 + 1, t1, n, l), List(r5(i0, t0, i1, t1, n, l)), true),
    Clause(r6(i0, t0, i1, t1, n, l), List(r0(i0, t0, i1, t1, n, l)), i1 >= bound1)
  )

  val ni_clauses_0_1 = for (Clause(IAtom(_, args),
                                   List(assump@IAtom(_, args2)), constraint) <- clauses_0;
                            p <- List(r0, r1, r2, r3, r4, r5, r6)) yield {
    Clause(IAtom(p, args), List(assump, IAtom(p, args2)), constraint)
  }

  val ni_clauses_1_0 = for (Clause(IAtom(_, args),
                                   List(assump@IAtom(_, args2)), constraint) <- clauses_1;
                            p <- List(q0, q1, q2, q3, q4, q5, q6)) yield {
    Clause(IAtom(p, args), List(assump, IAtom(p, args2)), constraint)
  }

  val assertions = List(
//    Clause(FALSE(), List(q6(i0, t0, i1, t1, n, l), r6(i0, t0, i1, t1, n, l)), n =/= bound0 + bound1)
    Clause(FALSE(), List(q6(i0, t0, i1, t1, n, l), r6(i0, t0, i1, t1, n, l)), n < 0)
  )

  val clauses =
    clauses_init ++ clauses_0 ++ clauses_1 ++ ni_clauses_0_1 ++ ni_clauses_1_0 ++ assertions

  println("Solving " + clauses + " ...")
  
  val predAbs =
    new HornPredAbs(clauses,
                    Map(),
                    DagInterpolator.interpolatingPredicateGenCEX _)

  println
  predAbs.result match {
    case Right(cex) => {
      println("NOT SOLVABLE")
      cex.prettyPrint
    }
    case Left(solution) =>
      println("SOLVABLE: " + solution)
  }
  }

}
