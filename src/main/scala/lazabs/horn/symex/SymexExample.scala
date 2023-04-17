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

import ap.parser.{IAtom, IFormula}
import ap.terfor.preds.Predicate
import ap.theories.ExtArray
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.Util.Dag

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
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object DFSExample1_1Unsat extends App {

  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running example 1_1 (Expected: UNSAT)")

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
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object DFSExample1_2Unsat extends App {

  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running example 1_2 (Expected: UNSAT)")

  SimpleAPI.withProver { p =>
    import p._
    {
      val p0 = createRelation("p0", List(Sort.Integer))
      val p1 = createRelation("p1", List(Sort.Integer))
      val p2 = createRelation("p2", List(Sort.Integer))
      val x  = createConstant("x")
      val x2 = createConstant("x'")

      val clauses: Seq[Clause] = List(
        p0(x) :- true,
        p1(x) :- (p0(x), x >= 1),
        p0(x - 1) :- p1(x),
        p2(x) :- (p0(x), x <= 0),
        (x >= 0) :- p2(x)
      )
      val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object DFSExample2Sat extends App {
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
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object DFSArrayExample extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("An array example")
  SimpleAPI.withProver { p =>
    import p._
    {
      val arr = ExtArray(Seq(Sort.Integer), Sort.Integer)
      val p0  = createRelation("p0", List(arr.sort, Sort.Integer))
      val p1  = createRelation("p1", List(arr.sort, Sort.Integer))
      val x   = createConstant("x")
      val a1   = createConstant("a1", arr.sort)
      val a2   = createConstant("a2", arr.sort)


      val clauses: Seq[Clause] = List(
        p0(arr.const(x), x) :- (x > 10),
        p0(a2, x-1) :- (p0(a1, x), x > 0, a2 === arr.store(a1, x, arr.select(a1,x+1)-1)), // x1 = a[x0], i.e., 5
        p1(a1, x) :- (p0(a1, x), x <= 0),
        (arr.select(a1, x) === x) :- p1(a1, x))

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object DFSExample2Unsat extends App {
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
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object DFSExample3NonTermination extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running example 3 (Expected: Non-termination)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val x     = createConstant("x")
      val old_x = createConstant("old_x")
      val p1    = createRelation("p", List(Sort.Integer, Sort.Integer))

      val clauses: Seq[Clause] = List(
        p1(x, old_x) :- (x === old_x),
        p1(x, old_x) :- p1(x - 1, old_x),
        false :- (p1(x, old_x), x =/= old_x)
      )

      val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object BFSExample1 extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running breadth-first example 1 (Expected: UNSAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val x = createConstant("x")
      val n = createConstant("n")
      val p = createRelation("p", List(Sort.Integer, Sort.Integer))

      // This example is easily shown to be unsafe (by only resolving the first
      // clause with the last assertion), but naive depth-first exploration
      // gets stuck in exploring the middle recursive clause.
      // Breadth-first search does not have this issue.
      val clauses: Seq[Clause] = List(
        p(x, n) :- (x === 0, n >= 0),
        p(x + 1, n) :- (p(x, n), x <= n),
        false :- (p(x, n), x >= n)
      )

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object BFSExample11 extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running breadth-first example 1 (Expected: UNSAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val p0 = createRelation("p0", List(Sort.Integer))
      val x  = createConstant("x")

      val clauses: Seq[Clause] = List(
        (x === 42) :- p0(x)
      )

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object BFSNonlinearExample1 extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running nonlinear-example 1 (Expected: SAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val x = createConstant("x")
      val y = createConstant("y")
      val p = createRelation("p", List(Sort.Integer))
      val q = createRelation("q", List(Sort.Integer))

      val clauses: Seq[Clause] = List(
        p(x) :- (x === 20),
        q(y) :- (y === 22),
        false :- (p(x), q(y), (x + y =/= 42))
      )

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object BFSNonlinearExample2 extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running nonlinear-example 1 (Expected: UNSAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val x = createConstant("x")
      val y = createConstant("y")
      val p = createRelation("p", List(Sort.Integer))
      val q = createRelation("q", List(Sort.Integer))

      val clauses: Seq[Clause] = List(
        p(x) :- (x === 20),
        q(y) :- (y === 22),
        false :- (p(x), q(y), (x + y === 42))
      )

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object BFSNonlinearExample3 extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running nonlinear-example 3 (Expected: SAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val x  = createConstant("x")
      val y  = createConstant("y")
      val p  = createRelation("p", List(Sort.Integer))
      val p1 = createRelation("p1", List(Sort.Integer))
      val q  = createRelation("q", List(Sort.Integer))

      val clauses: Seq[Clause] = List(
        p(x) :- (x === 20),
        p1(x) :- p(x),
        q(x + 2) :- p1(x),
        false :- (p(x), q(y), (x + y =/= 42))
      )

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object BFSNonlinearExample4 extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running nonlinear-example 4 (Expected: UNSAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val x  = createConstant("x")
      val y  = createConstant("y")
      val p  = createRelation("p", List(Sort.Integer))
      val p1 = createRelation("p1", List(Sort.Integer))
      val q  = createRelation("q", List(Sort.Integer))

      val clauses: Seq[Clause] = List(
        p(x) :- (x === 20),
        p1(x) :- p(x),
        q(x + 1) :- p1(x),
        false :- (p(x), q(y), (x + y =/= 42))
      )

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object BFSNonlinearExample5 extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  // tricera/regression-tests/horn-contracts/contract1.hcc

  println("Running nonlinear-example 5 (Expected: UNSAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val x  = createConstant("x")
      val y  = createConstant("y")
      val f1 = createRelation("f1", List(Sort.Integer))
      val f2 = createRelation("f2", List(Sort.Integer, Sort.Integer))

      val clauses: Seq[Clause] = List(
        f1(10) :- true,
        f2(x, y) :- (f1(x), f2(x - 1, y - 1), x > 0),
        f2(x, y) :- (f1(x), x <= 0, 0 === y),
        f1(x) :- (f1(x + 1), x >= 0),
        false :- (f2(10, y), y <= 0)
      )

      // this should produce a solution for f2: _1 = _0 = n where n = -10..0

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object BFSFibonacci extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  // tricera/regression-tests/horn-contracts/fib.hcc

  println("Running BFS fibonacci example (Expected: UNSAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val x     = createConstant("x")
      val c     = createConstant("c")
      val c1    = createConstant("c1")
      val c2    = createConstant("c2")
      val n     = createConstant("n")
      val n_old = createConstant("n_old")
      val p0    = createRelation("p0", List())
      val p1    = createRelation("p1", List(Sort.Integer))
      val f0    = createRelation("f0", List(Sort.Integer, Sort.Integer))
      val f1 =
        createRelation("f1", List(Sort.Integer, Sort.Integer, Sort.Integer))
      val f3     = createRelation("f3", List(Sort.Integer, Sort.Integer))
      val f4     = createRelation("f4", List(Sort.Integer, Sort.Integer))
      val f5     = createRelation("f5", List(Sort.Integer, Sort.Integer))
      val f6     = createRelation("f6", List(Sort.Integer, Sort.Integer))
      val f_pre  = createRelation("f_pre", List(Sort.Integer))
      val f_post = createRelation("f_post", List(Sort.Integer, Sort.Integer))

      /*
      int fib(int n) {
        if(n == 0)
          return 0;
        else if (n == 1)
          return 1;
        else return fib(n - 1) + fib(n - 2);
      }

      void main()
      {
        int x = fib(6);
        // 0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, ...
        assert(x == 0); // unsafe, cex should show that x is 8
      }
       */

      val clauses: Seq[Clause] = List(
        p0() :- true,
        p1(c) :- (p0(), f_post(4, c)),
        f0(n, n) :- (f_pre(n)),
        f3(n, n_old) :- (f0(n, n_old), n === 0),
        f4(n, n_old) :- (f0(n, n_old), n =/= 0),
        f1(n, n_old, 0) :- (f3(n, n_old)),
        f5(n, n_old) :- (f4(n, n_old), n === 1),
        f6(n, n_old) :- (f4(n, n_old), n =/= 1),
        f1(n, n_old, 1) :- (f5(n, n_old)),
        f1(n, n_old, c1 + c2) :- (f6(n, n_old), f_post(n - 1, c1), f_post(n - 2,
                                                                          c2)),
        f_post(n_old, c) :- (f1(n, n_old, c)),
        f_pre(n - 1) :- (f6(n, n_old)),
        f_pre(n - 2) :- (f6(n, n_old), f_post(n - 1, c)),
        f_pre(6) :- (p0()),
        false :- (p1(x), x =/= 0)
      )

      // Tests the case with two body literals with
      // the same predicate (f_post) at different occurrences.

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}
object BFSTakeuchi extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  // tricera/regression-tests/horn-contracts/tak.hcc

  println("Running BFS fibonacci example (Expected: SAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val x        = createConstant("x")
      val y        = createConstant("y")
      val z        = createConstant("z")
      val x_old    = createConstant("x_old")
      val y_old    = createConstant("y_old")
      val z_old    = createConstant("z_old")
      val res      = createConstant("res")
      val _res6    = createConstant("res6")
      val _res1    = createConstant("res1")
      val _res2    = createConstant("res2")
      val _res3    = createConstant("res3")
      val _res4    = createConstant("res4")
      val _res5    = createConstant("res5")
      val __eval8  = createConstant("eval8")
      val __eval14 = createConstant("eval14")
      val __eval20 = createConstant("eval20")

      val main0    = createRelation("main0", 3)
      val main1    = createRelation("main1", 3)
      val main2    = createRelation("main2", 4)
      val tak_pre  = createRelation("tak_pre", 3)
      val tak_post = createRelation("tak_post", 4)
      val tak0     = createRelation("tak0", 6)
      val tak1     = createRelation("tak1", 7)
      val tak3     = createRelation("tak3", 6)
      val tak4     = createRelation("tak4", 6)
      val tak5     = createRelation("tak5", 9)

      val clauses: Seq[Clause] = List(
        main2(x, y, z, _res6) :- (main1(x, y, z), tak_post(x, y, z, _res6)),
        main1(x, y, z) :- (main0(x, y, z), x - y >= 1 & z >= y),
        main0(x, y, z) :- true,
        tak0(x, y, z, x, y, z) :- (tak_pre(x, y, z)),
        tak3(x, y, z, x_old, y_old, z_old) :-
          (tak0(x, y, z, x_old, y_old, z_old), x - y >= 1),
        tak4(x, y, z, x_old, y_old, z_old) :-
          (tak0(x, y, z, x_old, y_old, z_old), x - y < 1),
        tak5(x, y, z, x_old, y_old, z_old, _res2, _res3, _res4) :-
          (tak3(x, y, z, x_old, y_old, z_old),
          tak_post(x - 1, y, z, _res2), tak_post(y - 1, z, x, _res3),
          tak_post(z - 1, x, y, _res4)),
        tak1(x, y, z, x_old, y_old, z_old, _res5) :-
          (tak5(x, y, z, x_old, y_old, z_old, __eval8, __eval14, __eval20),
          tak_post(__eval8, __eval14, __eval20, _res5)),
        tak1(x, y, z, x_old, y_old, z_old, y) :-
          (tak4(x, y, z, x_old, y_old, z_old)),
        tak_post(x_old, y_old, z_old, _res1) :-
          (tak1(x, y, z, x_old, y_old, z_old, _res1)),

        tak_pre(x - 1, y, z) :- (tak3(x, y, z, x_old, y_old, z_old)),

        tak_pre(y - 1, z, x) :- (tak3(x, y, z, x_old, y_old, z_old),
        tak_post(x - 1, y, z, _res2)),

        tak_pre(z - 1, x, y) :- (tak3(x, y, z, x_old, y_old, z_old),
        tak_post(x - 1, y, z, _res2), tak_post(y - 1, z, x, _res3)),

        tak_pre(__eval8, __eval14, __eval20) :-
          (tak5(x, y, z, x_old, y_old, z_old, __eval8, __eval14, __eval20)),

        tak_pre(x, y, z) :- (main1(x, y, z)),
        false :- (main2(x, y, z, res), res != z)
      )

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object BFSWithNoDepth1 extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running breadth-first example with no max depth (expected: UNSAT)")
  SimpleAPI.withProver { p =>
    import p._
    {
      val p0 = createRelation("p0", List(Sort.Integer))
      val x  = createConstant("x")

      val clauses: Seq[Clause] = List(
          p0(x)   :- (x === 0),
          p0(x+1) :- p0(x),
          false   :- (p0(x), x > 20)
        )

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses, None)
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object BFSWithDepth1 extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running breadth-first example with max depth 10 (expected: SAT (unsound))")
  SimpleAPI.withProver { p =>
    import p._
    {
      val p0 = createRelation("p0", List(Sort.Integer))
      val x  = createConstant("x")

      val clauses: Seq[Clause] = List(
        p0(x)   :- (x === 0),
        p0(x+1) :- p0(x),
        false   :- (p0(x), x > 20)
        )

      val symex = new BreadthFirstForwardSymex[HornClauses.Clause](clauses, Some(10))
      symex.printInfo = true
      Util.printRes(symex.solve())
    }
  }
}

object Util {
  def printRes(res: Either[Map[Predicate, IFormula], Dag[(IAtom, Clause)]]) = {
    res match {
      case Left(sln) =>
        println("\nSAT\n\nSolution")
        sln.foreach {
          case (pred, formula) => println(pred + ": " + formula)
        }
      case Right(cex) =>
        println("\nUNSAT\n\nCounterexample")
        cex.prettyPrint
    }
  }
}
