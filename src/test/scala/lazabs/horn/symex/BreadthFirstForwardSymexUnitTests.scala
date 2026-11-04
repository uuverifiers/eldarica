package lazabs.horn.symex

import ap.parser.IExpression.Sort
import lazabs.GlobalParameters
import lazabs.horn.bottomup.{HornClauses, NormClause}
import lazabs.horn.CHCResultMatchers
import ap.api.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
import ap.parser._
import ap.terfor.conjunctions.Conjunction
import IExpression._
import HornClauses._
import Symex.{InconclusiveException, SymexException}
import ap.theories.ExtArray
import ap.theories.ModuloArithmetic.{UnsignedBVSort, extract}
import org.scalatest.freespec.AnyFreeSpec

// todo: add non-linear test cases
class BreadthFirstForwardSymexUnitTests
    extends AnyFreeSpec
    with CHCResultMatchers
    with SymexResultVerification {

  class GivingUpSymex(clauses : Seq[Clause], givingUp : Set[Clause])
      extends BreadthFirstForwardSymex[Clause](clauses) {
    private var resolvedClause : Option[Clause] = None
    private var checks = 0

    override protected def hyperResolve(nucleus   : NormClause,
                                        electrons : Seq[UnitClause])
        : UnitClause = {
      resolvedClause = Some(normClauseToCC(nucleus))
      super.hyperResolve(nucleus, electrons)
    }

    override private[symex] def checkFeasibility(constraint : Conjunction,
                                                 budgetMs   : Option[Long])
        : FeasibilityCheckResult = {
      checks += 1
      assert(checks <= 100, "the search does not end")
      val clause = resolvedClause
      resolvedClause = None
      clause match {
        case Some(c) if givingUp contains c =>
          FeasibilityCheckResult.Undecided(ProverStatus.OutOfMemory)
        case _ =>
          super.checkFeasibility(constraint, budgetMs)
      }
    }
  }

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

              solveAndVerify(symex)
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

              solveAndVerify(symex)
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
              solveAndVerify(symex)
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

              solveAndVerify(symex)
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

              solveAndVerify(symex)
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
              solveAndVerify(symex)
            } should beUnsat
          }
        }
        "Unbounded loops with depth" - {
          "Unsafe beyond the bound (unknown, candidate solution)" in {
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
              val e = the [InconclusiveException] thrownBy symex.solve()

              val candidate = e.candidateSolution.get()(p0)
              def candidateHolds(value : Int) : Boolean = scope {
                !! (subst(candidate, List(i(value)), 0))
                ??? == ProverStatus.Sat
              }
              assert(candidateHolds(9) && !candidateHolds(10))
            }
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
              solveAndVerify(symex)
            } should beUnsat
          }
        }
      }
      "Counterexamples" - {
        "Valid counterexample (unsat)" in {
          scope {
            val p0 = createRelation("p0", List(Sort.Integer))
            val x  = createConstant("x")

            val clauses : Seq[Clause] = List(
              p0(0) :- true,
              p0(x + 1) :- p0(x),
              false :- (p0(x), x >= 2)
            )
            val result =
              solveAndVerify(new BreadthFirstForwardSymex[Clause](clauses))
            result should beUnsat
            assert(result.right.get().iterator.map(_._1).toList ==
                     List(IAtom(FALSE, Nil), p0(2), p0(1), p0(0)))
          }
        }
        "Derivations not kept: no counterexample (unsat)" in {
          scope {
            val p0 = createRelation("p0", List(Sort.Integer))
            val x  = createConstant("x")

            val clauses : Seq[Clause] = List(
              p0(0) :- true,
              p0(x + 1) :- p0(x),
              false :- (p0(x), x >= 2)
            )
            val result = new BreadthFirstForwardSymex[Clause](
              clauses, keepDerivations = false).solve()
            result should beUnsat
            the [SymexException] thrownBy result.right.get()
          }
        }
      }
      "Solutions" - {
        "State over bit-vector extracts (sat), " +
        "with a quantifier-free solution" in {
          scope {
            val p0 = createRelation(
              "p0", List(UnsignedBVSort(8), UnsignedBVSort(8)))
            val Seq(x, y) =
              for (name <- Seq("x", "y"))
              yield createConstant(name, UnsignedBVSort(8))

            val clauses : Seq[Clause] = List(
              p0(x, y) :- (extract(3, 0, x) === extract(3, 0, y)),
              false :- (p0(x, y), extract(3, 0, x) =/= extract(3, 0, y))
            )
            val result =
              solveAndVerify(new BreadthFirstForwardSymex[Clause](clauses))
            result should beSat
            QuantifierCountVisitor(result.left.get()(p0)) shouldBe 0
          }
        }
      }

      "Timeouts" - {
        "A check that does not end is stopped when the run times out" in {
          scope {
            val Seq(x, y, z) =
              for (name <- Seq("x", "y", "z")) yield createConstant(name)

            val clauses : Seq[Clause] = List(
              false :- (x ** x ** x + y ** y ** y === z ** z ** z &
                          x > 0 & y > 0 & z > 0)
            )
            val symex = new BreadthFirstForwardSymex[Clause](clauses)
            val params = GlobalParameters.get.clone
            params.timeoutChecker = () => throw lazabs.Main.TimeoutException
            GlobalParameters.withValue(params) {
              the [Exception] thrownBy symex.checkFeasibility(
                symex.normClauses.head._1.constraint, budgetMs = None
              ) shouldBe lazabs.Main.TimeoutException
            }
            symex.shutdown
          }
        }
      }

      "Undecided checks" - {
        "Undecided state above a counterexample (unsat)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val q = createRelation("q", List(Sort.Integer))
            val x = createConstant("x")

            val givenUpState : Clause = q(x) :- p(x)
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 0),
              givenUpState,
              false :- q(x)
            )
            val symex = new GivingUpSymex(clauses, Set(givenUpState))
            solveAndVerify(symex)
          } should beUnsat
        }
        "Undecided empty goal, no other refutation (unknown)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val x = createConstant("x")

            val givenUpGoal : Clause = false :- (p(x), x >= 0)
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 0),
              givenUpGoal
            )
            val symex = new GivingUpSymex(clauses, Set(givenUpGoal))
            val e = the [InconclusiveException] thrownBy symex.solve()
            e.candidateSolution shouldBe empty
          }
        }
        "Unchecked state keeps its unconnected conjuncts (sat)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val q = createRelation("q", List(Sort.Integer))
            val x = createConstant("x")
            val c = createConstant("c")
            val d = createConstant("d")

            // c * d = 1 has no solution with c, d >= 2
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 0 & mult(c, d) === 1 & c >= 2 & d >= 2),
              q(x) :- p(x),
              false :- q(x)
            )
            val params = GlobalParameters.get.clone
            params.symexStateChecks = GlobalParameters.SymexStateChecks.None
            GlobalParameters.withValue(params) {
              solveAndVerify(new BreadthFirstForwardSymex[Clause](clauses))
            }
          } should beSat
        }
      }
      "Choice order" - {
        "Under guided order, the assertion is resolved first " +
        "(unsat in one step)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val x = createConstant("x")

            val clauses : Seq[Clause] = List(
              p(x) :- (x === 0),
              p(x + 1) :- p(x),
              false :- (p(x), x === 0)
            )
            val symex = new BreadthFirstForwardSymex[Clause](clauses)
            solveAndVerify(symex) should beUnsat
            symex.statistics.statesDerived shouldBe 1
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
              solveAndVerify(symex)
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
              solveAndVerify(symex)
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
              solveAndVerify(symex)
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
              solveAndVerify(symex)
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
              solveAndVerify(symex)
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
              solveAndVerify(symex)
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
              solveAndVerify(symex)
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
              solveAndVerify(symex)
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
              solveAndVerify(symex)
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
              solveAndVerify(symex)
            } should beUnsat
          }
        }
      }
    }
  }
}
