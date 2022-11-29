/**
 * Copyright (c) 2022 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import ap.theories.ExtArray

/**
 * An example application
 */
object SymexExample1Sat extends App {

  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running example 1 (expected: SAT")

  /**
   * A simple example that encodes a simple set of clauses and directly attempts
   * to solve them. */
  SimpleAPI.withProver { p =>
    import p._
    {
      val p0 = createRelation("p0", List(Sort.Integer))
      val p1 = createRelation("p1", List(Sort.Integer))
      val p2 = createRelation("p2", List(Sort.Integer))
      val x  = createConstant("x")
      val y  = createConstant("y")

      val clauses: Seq[Clause] = List(
        p0(x) :- (x > 2),
        p1(x) :- (p0(x), x > 0),
        p0(x - 1) :- p1(x),
        p2(x) :- (p0(x), x <= 0),
        (x >= 0) :- p2(x)
      )
      val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
      println(symex.solve())
    }
  }
}

object SymexExample1Unsat extends App {

  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running example 1 (Expected: UNSAT)")

  SimpleAPI.withProver { p =>
    import p._
    {
      val p0 = createRelation("p0", List(Sort.Integer))
      val p1 = createRelation("p1", List(Sort.Integer))
      val p2 = createRelation("p2", List(Sort.Integer))
      val x  = createConstant("x")

      val clauses: Seq[Clause] = List(
        p0(x) :- (x > 2),
        p1(x) :- (p0(x), x >= 0),
        p0(x - 1) :- p1(x),
        p2(x) :- (p0(x), x <= 0),
        (x >= 0) :- p2(x)
      )
      val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
      println(symex.solve())
    }
  }
}

object SymexExample2Sat extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._
  println("Running example 2 (Expected: SAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val arr = ExtArray(Seq(Sort.Integer), Sort.Integer)
      val p0  = createRelation("p0", List(arr.sort, Sort.Integer))
      val p1  = createRelation("p1", List(Sort.Integer))
      val p2  = createRelation("p2", List(Sort.Integer))
      val x   = createConstants("x", 1 to 10)
      val a   = createConstants("a", 1 to 10, arr.sort)

      val clauses: Seq[Clause] = List(
        p0(a(1), x(0)) :- (a(0) === arr
          .const(0), a(1) === arr
          .store(a(0), x(0), 5), x(0) >= 0), // a[x0] = 5
        p1(x(1)) :- (p0(a(0), x(0)), x(1) === arr
          .select(a(0), x(0))), // x1 = a[x0], i.e., 5
        p1(x(0) - 1) :- (p1(x(0)), x(0) > 0),
        p2(x(0)) :- (p1(x(0)), x(0) <= 0),
        (x(0) >= 0) :- p2(x(0))
      )

      val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
      println(symex.solve())
    }
  }
}

object SymexExample2Unsat extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._
  println("Running example 2 (Expected: UNSAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val arr = ExtArray(Seq(Sort.Integer), Sort.Integer)
      val p0  = createRelation("p0", List(arr.sort, Sort.Integer))
      val p1  = createRelation("p1", List(Sort.Integer))
      val p2  = createRelation("p2", List(Sort.Integer))
      val x   = createConstants("x", 1 to 10)
      val a   = createConstants("a", 1 to 10, arr.sort)

      val clauses: Seq[Clause] = List(
        p0(a(1), x(0)) :- (a(0) === arr
          .const(0), a(1) === arr
          .store(a(0), x(0), 5), x(0) >= 0), // a[x0] = 5
        p1(x(1)) :- (p0(a(0), x(0)), x(1) === arr
          .select(a(0), x(0))), // x1 = a[x0], i.e., 5
        p1(x(0) - 1) :- (p1(x(0)), x(0) >= 0),
        p2(x(0)) :- (p1(x(0)), x(0) <= 0),
        (x(0) >= 0) :- p2(x(0))
      )

      val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
      println(symex.solve())
    }
  }
}
