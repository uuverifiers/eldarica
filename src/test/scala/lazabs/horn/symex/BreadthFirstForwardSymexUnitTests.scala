package lazabs.horn.symex

import ap.parser.IExpression.Sort
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.CHCResultMatchers
import ap.api.SimpleAPI
import ap.parser._
import IExpression._
import HornClauses._
import ap.theories.ExtArray
import org.scalatest.freespec.AnyFreeSpec

// todo: add non-linear test cases
class BreadthFirstForwardSymexUnitTests
    extends AnyFreeSpec
    with CHCResultMatchers {

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
        "Unbounded loops with depth" - {
          "Safe (underapproximate / unsound)" in {
            scope{
              val p0 = createRelation("p0", List(Sort.Integer))
              val x  = createConstant("x")

              val clauses : Seq[Clause] = List(
                p0(x) :- (x === 0),
                p0(x + 1) :- p0(x),
                false :- (p0(x), x > 20)
                )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses, Some(10))
              symex.solve()
            } should beSat
          }
          "Unsafe" in {
            scope{
              val p0 = createRelation("p0", List(Sort.Integer))
              val x  = createConstant("x")

              val clauses : Seq[Clause] = List(
                p0(x) :- (x === 0),
                p0(x + 1) :- p0(x),
                false :- (p0(x), x > 20)
                )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses, Some(25))
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
          "Safe 1" in {
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
          "Safe 2" in {
            scope {
              val p0 = createRelation("p0", List(Sort.Integer))
              val x  = createConstant("x")

              val clauses: Seq[Clause] = List(
                (x === 42) :- p0(x)
              )
              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beSat
          }
        }
        "Single assertion with no literals" - {
          "Unsafe" in {
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
        "Two body literals with same predicate" - {
          "Unsafe" in {
            scope {
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
                createRelation("f1",
                               List(Sort.Integer, Sort.Integer, Sort.Integer))
              val f3    = createRelation("f3", List(Sort.Integer, Sort.Integer))
              val f4    = createRelation("f4", List(Sort.Integer, Sort.Integer))
              val f5    = createRelation("f5", List(Sort.Integer, Sort.Integer))
              val f6    = createRelation("f6", List(Sort.Integer, Sort.Integer))
              val f_pre = createRelation("f_pre", List(Sort.Integer))
              val f_post =
                createRelation("f_post", List(Sort.Integer, Sort.Integer))

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
                f1(n, n_old, c1 + c2) :- (f6(n, n_old), f_post(n - 1, c1), f_post(
                  n - 2,
                  c2)),
                f_post(n_old, c) :- (f1(n, n_old, c)),
                f_pre(n - 1) :- (f6(n, n_old)),
                f_pre(n - 2) :- (f6(n, n_old), f_post(n - 1, c)),
                f_pre(6) :- (p0()),
                false :- (p1(x), x =/= 0)
              )

              // Tests the case with two body literals with
              // the same predicate (f_post) at different occurrences.

              val symex =
                new BreadthFirstForwardSymex[HornClauses.Clause](clauses)
              symex.solve()
            } should beUnsat
          }
        }
      }
      "Timeout tests" - {
        "Bitvectors" - {
          import ap.theories.bitvectors.ModuloArithmetic._

          "Unsafe" in {
            scope {
              val bv64 = UnsignedBVSort(64)
              val bv128 = UnsignedBVSort(128)
              val p = createRelation("p", List(bv64))
              val q = createRelation("q", List(bv128))
              val r = createRelation("r", List(bv128))
              val x  = createConstant("x", bv64)
              val y  = createConstant("y", bv128)

              val clauses : Seq[Clause] = List(
                p(x)  :- true,
                q(y)  :- (p(x), y === bvmul(zero_extend(64, x), zero_extend(64, x))),
                r(y)  :- (q(y), bv_extract(63, 0, y) === bv(64, 0)),  // (1)
                r(y)  :- (q(y), bv_extract(63, 0, y) =/= bv(64, 0)),  // (2)
                false :- (r(y), bv_extract(127, 120, y) =/= bv(8, 0)) // (3)
              )
              /**
               * Princess gets stuck when checking the constraint of (1) + (3),
               * however (2) + (3) works. Timing out and requesting the former
               * should lead to a result.
               */

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
