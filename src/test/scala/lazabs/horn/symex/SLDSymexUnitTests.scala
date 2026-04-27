package lazabs.horn.symex

import ap.parser.IExpression._
import ap.api.SimpleAPI
import ap.theories.ExtArray
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.CHCResultMatchers
import org.scalatest.freespec.AnyFreeSpec

class SLDSymexUnitTests extends AnyFreeSpec with CHCResultMatchers {

  SimpleAPI.withProver { p =>
    import p._
    {
      "Linear CHCs" - {
        "Simple fact + assertion (sat)" in {
          scope {
            val inv = createRelation("inv", List(Sort.Integer))
            val x   = createConstant("x")
            val clauses : Seq[Clause] = List(
              inv(x) :- (x === 0),
              (x >= 0) :- inv(x)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beSat
        }

        "Simple fact + assertion (unsat)" in {
          scope {
            val inv = createRelation("inv", List(Sort.Integer))
            val x   = createConstant("x")
            val clauses : Seq[Clause] = List(
              inv(x) :- (x === 42),
              (x =/= 42) :- inv(x)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beUnsat
        }

        "Bounded loop (sat)" in {
          scope {
            val inv = createRelation("inv", List(Sort.Integer))
            val x   = createConstant("x")
            val clauses : Seq[Clause] = List(
              inv(x) :- (x === 0),
              inv(x + 1) :- (inv(x), x < 10),
              (x <= 10) :- inv(x)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beSat
        }

        "Bounded loop (unsat)" in {
          scope {
            val inv = createRelation("inv", List(Sort.Integer))
            val x   = createConstant("x")
            val clauses : Seq[Clause] = List(
              inv(x) :- (x === 0),
              inv(x + 1) :- (inv(x), x < 10),
              (x <= 9) :- inv(x)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beUnsat
        }

        "Two predicates chain (unsat)" in {
          scope {
            val p0 = createRelation("p0", List(Sort.Integer))
            val p1 = createRelation("p1", List(Sort.Integer))
            val x  = createConstant("x")
            val clauses : Seq[Clause] = List(
              p0(x) :- (x === 5),
              p1(x + 1) :- p0(x),
              false :- (p1(x), x > 5)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beUnsat
        }

        "Depth-bounded (sat, underapproximate)" in {
          scope {
            val inv = createRelation("inv", List(Sort.Integer))
            val x   = createConstant("x")
            val clauses : Seq[Clause] = List(
              inv(x) :- (x === 0),
              inv(x + 1) :- inv(x),
              false :- (inv(x), x > 100)
            )
            new SLDSymex[Clause](clauses, Some(10)).solve()
          } should beSat
        }

        "Depth-bounded (unsat)" in {
          scope {
            val inv = createRelation("inv", List(Sort.Integer))
            val x   = createConstant("x")
            val clauses : Seq[Clause] = List(
              inv(x) :- (x === 0),
              inv(x + 1) :- inv(x),
              false :- (inv(x), x > 5)
            )
            new SLDSymex[Clause](clauses, Some(20)).solve()
          } should beUnsat
        }
      }

      "Non-linear CHCs" - {
        "Two facts, non-linear assertion (sat)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val q = createRelation("q", List(Sort.Integer))
            val x = createConstant("x")
            val y = createConstant("y")
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 0),
              q(x) :- (x === 1),
              false :- (p(x), q(y), x === y)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beSat
        }

        "Two facts, non-linear assertion (unsat)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val q = createRelation("q", List(Sort.Integer))
            val x = createConstant("x")
            val y = createConstant("y")
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 5),
              q(x) :- (x === 5),
              false :- (p(x), q(y), x === y)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beUnsat
        }

        "Recursive + non-linear (unsat)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val q = createRelation("q", List(Sort.Integer))
            val x = createConstant("x")
            val y = createConstant("y")
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 0),
              p(x + 1) :- (p(x), x < 5),
              q(x) :- (x === 0),
              q(x + 1) :- (q(x), x < 5),
              false :- (p(x), q(y), x > 4, y > 4)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beUnsat
        }

        "Same predicate twice in body (unsat)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val x = createConstant("x")
            val y = createConstant("y")
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 3),
              p(x) :- (x === 7),
              false :- (p(x), p(y), x < y)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beUnsat
        }

        "Same predicate twice in body (sat)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val x = createConstant("x")
            val y = createConstant("y")
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 3),
              false :- (p(x), p(y), x =/= y)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beSat
        }
      }

      "Corner cases" - {
        "Empty body assertion (unsat)" in {
          scope {
            val inv = createRelation("inv", List(Sort.Integer))
            val x   = createConstant("x")
            val clauses : Seq[Clause] = List(
              inv(x) :- (x === 0),
              false :- true
            )
            new SLDSymex[Clause](clauses).solve()
          } should beUnsat
        }

        "No assertion (sat)" in {
          scope {
            val inv = createRelation("inv", List(Sort.Integer))
            val x   = createConstant("x")
            val clauses : Seq[Clause] = List(
              inv(x) :- (x === 0)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beSat
        }

        "Multiple assertions, one fails (unsat)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val x = createConstant("x")
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 5),
              (x >= 0) :- p(x),
              (x < 5) :- p(x)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beUnsat
        }

        "Non-linear with array store residuals (unsat)" in {
          scope {
            // Mirrors BallRajamani-SPIN2000-Fig1: the assertion
            // has a store predicate that becomes a residual
            // at an occurrence that normalization must avoid
            val arr = ExtArray(Seq(Sort.Integer), Sort.Integer)
            val p   = createRelation("p",
              List(arr.sort, arr.sort, Sort.Integer,
                   Sort.Integer, Sort.Integer))
            val a  = createConstant("a", arr.sort)
            val b  = createConstant("b", arr.sort)
            val sk = createConstant("sk", arr.sort)
            val c  = createConstant("c")
            val d  = createConstant("d")
            val e  = createConstant("e")
            val f  = createConstant("f")
            val i  = createConstant("i")
            val clauses : Seq[Clause] = List(
              p(a, b, 0, d, i) :-
                (b === arr.store(a, i, d)),
              p(a, b, d, c, i) :-
                (p(a, b, c, d, i), d =/= 0),
              false :-
                (p(a, b, c, d, i), p(a, b, e, f, i),
                 c === e, c =/= 0,
                 d === 0, f === 0,
                 a === arr.store(sk, i, 0))
            )
            new SLDSymex[Clause](clauses).solve()
          } should beUnsat
        }

        "Non-linear clause body in rule (unsat)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val q = createRelation("q", List(Sort.Integer))
            val r = createRelation("r", List(Sort.Integer))
            val x = createConstant("x")
            val y = createConstant("y")
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 1),
              q(x) :- (x === 2),
              r(x) :- (p(x), q(y), x < y),
              false :- r(x)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beUnsat
        }
      }

      "Duplicate atom elimination" - {
        "eliminates when duplicate" in {
          // p(x), p(y) with x = y should reduce to p(x)
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val x = createConstant("x")
            val y = createConstant("y")
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 0),
              false :- (p(x), p(y), x === y)
            )
            val symex = new SLDSymex[Clause](clauses)
            symex.solve()
            assert(symex.goalClauseDB.allGoals.exists(
              _.atoms.size == 1),
              "duplicate atom elimination should produce " +
                "a single-atom goal")
          }
        }

        "preserves when not duplicate (unsat)" in {
          scope {
            val p = createRelation("p", List(Sort.Integer))
            val x = createConstant("x")
            val y = createConstant("y")
            val clauses : Seq[Clause] = List(
              p(x) :- (x === 3),
              p(x) :- (x === 7),
              false :- (p(x), p(y), x =/= y)
            )
            new SLDSymex[Clause](clauses).solve()
          } should beUnsat
        }
      }
    }
  }
}
