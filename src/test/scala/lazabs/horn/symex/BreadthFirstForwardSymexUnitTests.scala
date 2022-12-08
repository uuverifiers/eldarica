package lazabs.horn.symex

import ap.parser.IExpression.Sort
import lazabs.horn.bottomup.HornClauses
import ap.api.SimpleAPI
import ap.parser._
import IExpression._
import HornClauses._
import ap.theories.ExtArray
import org.scalatest.freespec.AnyFreeSpec

// todo: add non-linear test cases
class BreadthFirstForwardSymexUnitTests
    extends AnyFreeSpec
    with SymexResultMatchers {

  Symex.printInfo = false
  SimpleAPI.withProver { p =>
    import p._
    {
      "Simple tests" - {
        "Bounded loops" - {
          "Safe" in {
            scope {
              val p0 = createRelation("p0", List(Sort.Integer))
              val p1 = createRelation("p1", List(Sort.Integer))
              val p2 = createRelation("p2", List(Sort.Integer))
              val x  = createConstant("x")

              val clauses: Seq[Clause] = List(
                p0(x) :- (x > 2),
                p1(x) :- (p0(x), x > 0),
                p0(x - 1) :- p1(x),
                p2(x) :- (p0(x), x <= 0),
                (x >= 0) :- p2(x)
              )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)

              symex.solve()
            } should beSat
          }
          "Unsafe 1" in {
            scope {
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

              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)

              symex.solve()
            } should beUnsat
          }

          "Unsafe 2" in {
            scope {
              val x = createConstant("x")
              val n = createConstant("n")
              val p = createRelation("p", List(Sort.Integer, Sort.Integer))

              // This example is easily shown to be unsafe (by only resolving the first

              // clause with the last assertion), but naive depth-first exploration
              // gets stuck in exploring the middle recursive clause.
              // Breadth-first search does not have this issue.
              val clauses: Seq[Clause] = List(
                p(x, n) :- (x === 0, n > 0),
                p(x + 1, n) :- (p(x, n), x <= n),
                false :- (p(x, n), x >= n)
              )

              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beUnsat
          }

        }
        "Bounded loops with arrays" - {
          "Safe" in {
            scope {
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

              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)

              symex.solve()
            } should beSat
          }
          "Unsafe" in {
            scope {
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

              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)

              symex.solve()
            } should beUnsat
          }
        }
        "Unbounded loops" - {
          "Unsafe" in {
            scope {
              val p0 = createRelation("p0", List(Sort.Integer))
              val p1 = createRelation("p1", List(Sort.Integer))
              val p2 = createRelation("p2", List(Sort.Integer))
              val x  = createConstant("x")

              val clauses: Seq[Clause] = List(
                p0(x) :- true,
                p1(x) :- (p0(x), x >= 1),
                p0(x - 1) :- p1(x),
                p2(x) :- (p0(x), x <= 0),
                (x >= 0) :- p2(x)
              )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beUnsat
          }
        }
      }
      "Corner cases" - {
        "Single fact (no assertion)" - {
          "Safe" in {
            scope {
              val p0 = createRelation("p0", List(Sort.Integer))
              val x  = createConstant("x")

              val clauses: Seq[Clause] = List(
                p0(x) :- (x === 42)
              )

              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beSat
          }
        }
        "Single fact + one assertion" - {
          "Safe" in {
            scope {
              val p0 = createRelation("p0", List(Sort.Integer))
              val x  = createConstant("x")

              val clauses: Seq[Clause] = List(
                p0(x) :- (x === 42),
                (x === 42) :- p0(x)
              )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beSat
          }
          "Unsafe" in {
            scope {
              val p0 = createRelation("p0", List(Sort.Integer))
              val x  = createConstant("x")

              val clauses: Seq[Clause] = List(
                p0(x) :- (x === 42),
                (x =/= 42) :- p0(x)
              )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beUnsat
          }
        }
        "Two facts" - {
          "Safe" in {
            scope {
              val p0 = createRelation("p0", List(Sort.Integer))
              val p1 = createRelation("p1", List(Sort.Integer))
              val x  = createConstant("x")

              val clauses: Seq[Clause] = List(
                p0(x) :- (x === 42),
                p1(x) :- (x === 3)
              )

              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beSat
          }
        }
        "Two facts one goal" - {
          "Unsafe" in {
            scope {
              val x = createConstant("x")
              val p = createRelation("p", List(Sort.Integer))

              val clauses: Seq[Clause] = List(
                p(x) :- (x < 0), // resolution with this is unsat
                p(x) :- (x > 0), // resolution with this is sat
                false :- (p(x), x < 0)
              )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beUnsat
          }
          "Unsafe (swapped facts)" in {
            scope {
              val x = createConstant("x")
              val p = createRelation("p", List(Sort.Integer))

              val clauses: Seq[Clause] = List(
                p(x) :- (x > 0), // resolution with this is sat
                p(x) :- (x < 0), // resolution with this is unsat
                false :- (p(x), x < 0)
              )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beUnsat
          }
        }
        "Single goal" - {
          "Safe" in {
            scope {
              val x  = createConstant("x")
              val p0 = createRelation("p0", List(Sort.Integer))

              val clauses: Seq[Clause] = List(
                (x === 42) :- (p0(x), x === 42)
              )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beSat
          }
          "Unsafe" in {
            scope {
              val p0 = createRelation("p0", List(Sort.Integer))
              val x  = createConstant("x")

              val clauses: Seq[Clause] = List(
                (x === 42) :- p0(x)
              )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beUnsat
          }
        }
        "Single assertion with no literals" - {
          "Unsafe" - {
            scope {
              val x = createConstant("x")

              val clauses: Seq[Clause] = List(
                (x === 42) :- true
              )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beUnsat
          }
        }
      }
    }
  }
}
