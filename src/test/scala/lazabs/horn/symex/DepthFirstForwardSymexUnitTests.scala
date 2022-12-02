package lazabs.horn.symex

import org.scalatest.flatspec.AnyFlatSpec
import ap.parser.IExpression.Sort
import lazabs.horn.bottomup.HornClauses
import ap.api.SimpleAPI
import ap.parser._
import IExpression._
import HornClauses._
import ap.theories.ExtArray
import lazabs.horn.preprocessor.HornPreprocessor.{CounterExample, Solution}

class DepthFirstForwardSymexUnitTests extends AnyFlatSpec {

////////////////////////////////////////////////////////////////////////////////
// Configuration
  Symex.printInfo = false
////////////////////////////////////////////////////////////////////////////////

  SimpleAPI.withProver { p =>
    import p._
    {
      "Simple loop - 1" should "be SAT" in {
        assert(scope {
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
        } isSat)
      }

      "Simple loop - 2" should "be UNSAT" in {
        assert(scope {
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
        } isUnsat)
      }

      "Simple loop with arrays - 1" should "be SAT" in {
        assert(scope {
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
          symex.solve()
        } isSat)
      }

      "Simple loop with arrays - 2" should "be UNSAT" in {
        assert(scope {
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
          symex.solve()
        } isUnsat)
      }

      // A few corner cases
      "Single fact" should "be SAT" in {
        assert(scope {
          val p0 = createRelation("p0", List(Sort.Integer))
          val x  = createConstant("x")

          val clauses: Seq[Clause] = List(
            p0(x) :- (x === 42)
          )

          val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
          symex.solve()
        } isSat)
      }

      "Two facts" should "be SAT" in {
        assert(scope {
          val p0 = createRelation("p0", List(Sort.Integer))
          val p1 = createRelation("p1", List(Sort.Integer))
          val x  = createConstant("x")

          val clauses: Seq[Clause] = List(
            p0(x) :- (x === 42),
            p1(x) :- (x === 3)
          )

          val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
          symex.solve()
        } isSat)
      }

      "Single fact + assertion" should "be SAT" in {
        assert(scope {
          val p0 = createRelation("p0", List(Sort.Integer))
          val x  = createConstant("x")

          val clauses: Seq[Clause] = List(
            p0(x) :- (x === 42),
            (x === 42) :- p0(x)
          )
          val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
          symex.solve()
        } isSat)
      }

      "Single fact + unsafe assertion" should "be UNSAT" in {
        assert(scope {
          val p0 = createRelation("p0", List(Sort.Integer))
          val x  = createConstant("x")

          val clauses: Seq[Clause] = List(
            p0(x) :- (x === 42),
            (x =/= 42) :- p0(x)
          )
          val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
          symex.solve()
        } isUnsat)
      }

      "Single assertion with one literal" should "be UNSAT" in {
        assert(scope {
          val p0 = createRelation("p0", List(Sort.Integer))
          val x  = createConstant("x")

          val clauses: Seq[Clause] = List(
            (x === 42) :- p0(x)
          )
          val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
          symex.solve()
        } isUnsat)
      }

      "Single assertion with no literals" should "be UNSAT" in {
        assert(scope {
          val x = createConstant("x")

          val clauses: Seq[Clause] = List(
            (x === 42) :- true
          )
          val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
          symex.solve()
        } isUnsat)
      }

      "Single safe assertion with body literal" should "be SAT" in {
        assert(scope {
          val x  = createConstant("x")
          val p0 = createRelation("p0", List(Sort.Integer))

          val clauses: Seq[Clause] = List(
            (x === 42) :- (p0(x), x === 42)
          )
          val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
          symex.solve()
        } isSat)
      }

      "Two facts one unsafe goal" should "be UNSAT" in {
        assert(scope {
          val x = createConstant("x")
          val p = createRelation("p", List(Sort.Integer))

          val clauses: Seq[Clause] = List(
            p(x) :- (x < 0), // resolution with this is unsat
            p(x) :- (x > 0), // resolution with this is sat
            false :- (p(x), x < 0)
          )
          val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
          symex.solve()
        } isUnsat)
      }

      "Two facts (swapped) one unsafe goal" should "be UNSAT" in {
        assert(scope {
          val x = createConstant("x")
          val p = createRelation("p", List(Sort.Integer))

          val clauses: Seq[Clause] = List(
            p(x) :- (x > 0), // resolution with this is sat
            p(x) :- (x < 0), // resolution with this is unsat
            false :- (p(x), x < 0)
          )
          val symex = new DepthFirstForwardSymex[HornClauses.Clause](clauses)
          symex.solve()
        } isUnsat)
      }
    }
  }

  implicit class ResultEvaluator(result: Either[Solution, CounterExample]) {
    def isSat   = result.isLeft
    def isUnsat = !isSat
  }

}
