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

  println("Running example 1 (expected: Sat")

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
      symex.solve()
    }
  }
}

object SymexExample1Unsat extends App {

  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._

  println("Running example 1 (Expected: Unsat)")

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
        p1(x) :- (p0(x), x >= 0),
        p0(x - 1) :- p1(x),
        p2(x) :- (p0(x), x <= 0),
        (x >= 0) :- p2(x)
      )
      val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.solve()
    }
  }
}

object SymexExample2Sat extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._
  println("Running example 2 (Expected: Sat)")
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
        (x(0) >= 0) :- p2(x(0)) // should be sat
      )

      val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.solve()
    }
  }
}

object SymexExample2Unsat extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._
  println("Running example 2 (Expected: Unsat)")
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
        (x(0) >= 0) :- p2(x(0)) // should be sat
      )

      val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
      symex.solve()
    }
  }
}
