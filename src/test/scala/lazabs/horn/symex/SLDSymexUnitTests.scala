package lazabs.horn.symex

import ap.api.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
import ap.parser._
import ap.terfor.conjunctions.Conjunction
import lazabs.GlobalParameters
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.{CHCResultMatchers, HornWrapper}
import IExpression._
import HornClauses._
import Symex.{FeasibilityCheckResult, InconclusiveException, SymexException}
import org.scalatest.freespec.AnyFreeSpec

class SLDSymexUnitTests
    extends AnyFreeSpec
    with CHCResultMatchers {

  ap.util.Debug.enableAllAssertions(true)

  class GivingUpSymex(clauses : Seq[Clause])
      extends SLDSymex[Clause](clauses) {
    private var checks = 0

    override private[symex] def checkFeasibility(constraint : Conjunction,
                                                 budgetMs   : Option[Long])
        : FeasibilityCheckResult = {
      checks += 1
      assert(checks <= 100, "the search does not end")
      FeasibilityCheckResult.Undecided(ProverStatus.OutOfMemory)
    }
  }

  SimpleAPI.withProver { p =>
    import p._

    def holds(solution : IFormula, value : Int) : Boolean = scope {
      !! (subst(solution, List(i(value)), 0))
      ??? == ProverStatus.Sat
    }

    "Linear loop" - {
      "Safe (sat), with the greatest solution" in {
        scope {
          val pr = createRelation("p", List(Sort.Integer))
          val x  = createConstant("x")

          val clauses : Seq[Clause] = List(
            pr(x) :- (x === 0),
            pr(x + 1) :- pr(x),
            false :- (pr(x), x < 0)
          )
          val result = new SLDSymex[Clause](clauses).solve()
          result should beSat
          val solution = result.left.get()(pr)
          assert(holds(solution, 0) && holds(solution, 7) &&
                 !holds(solution, -1))
        }
      }
      "Unsafe (unsat)" in {
        scope {
          val pr = createRelation("p", List(Sort.Integer))
          val x  = createConstant("x")

          val clauses : Seq[Clause] = List(
            pr(x) :- (x === 0),
            pr(x + 1) :- pr(x),
            false :- (pr(x), x > 5)
          )
          new SLDSymex[Clause](clauses).solve()
        } should beUnsat
      }
      "Depth bound (unknown), with a candidate solution" in {
        scope {
          val pr = createRelation("p", List(Sort.Integer))
          val x  = createConstant("x")

          val clauses : Seq[Clause] = List(
            pr(x) :- (x === 0),
            pr(x + 1) :- pr(x),
            false :- (pr(x), x > 20)
          )
          val symex = new SLDSymex[Clause](clauses, maxDepth = Some(10))
          val e = the [InconclusiveException] thrownBy symex.solve()
          val candidate = e.candidateSolution.get()(pr)
          assert(holds(candidate, 10) && !holds(candidate, 11))
        }
      }
      "Goal union subsumed by two stored goals (sat)" in {
        scope {
          val pr = createRelation("p", List(Sort.Integer, Sort.Integer))
          val Seq(x, y) = for (name <- Seq("x", "y")) yield createConstant(name)

          // resolving the first goal gives false :- p(x, y), x >= 2 & y >= 1,
          // which only the two goals together subsume
          val clauses : Seq[Clause] = List(
            pr(x, y) :- (y === 0),
            pr(x + 1, y) :- pr(x, y),
            false :- (pr(x, y), x >= 3 & y >= 1),
            false :- (pr(x, y), x <= 2 & y >= 1)
          )
          new SLDSymex[Clause](clauses, maxDepth = Some(5)).solve()
        } should beSat
      }
    }

    "Non-linear clauses" - {
      "Safe (sat), without a solution for goals with two atoms" in {
        scope {
          val pr = createRelation("p", List(Sort.Integer))
          val qr = createRelation("q", List(Sort.Integer))
          val rr = createRelation("r", List(Sort.Integer))
          val Seq(x, y) = for (name <- Seq("x", "y")) yield createConstant(name)

          val clauses : Seq[Clause] = List(
            pr(x) :- (x >= 0),
            rr(y) :- (y >= 0),
            qr(x + y) :- (pr(x), rr(y)),
            false :- (qr(x), x < 0)
          )
          val result = new SLDSymex[Clause](clauses).solve()
          result should beSat
          assertThrows[SymexException] { result.left.get() }
        }
      }
      "Factoring stores two equal atoms as one (sat, with a solution)" in {
        scope {
          val pr = createRelation("p", List(Sort.Integer))
          val Seq(x, y) = for (name <- Seq("x", "y")) yield createConstant(name)

          val clauses : Seq[Clause] = List(
            pr(x) :- (x >= 0),
            false :- (pr(x), pr(y), x === y & x < 0)
          )
          val result = new SLDSymex[Clause](clauses).solve()
          result should beSat
          val solution = result.left.get()(pr)
          assert(holds(solution, 0) && !holds(solution, -1))
        }
      }
      "Unsafe through a factored goal (unsat)" in {
        scope {
          val pr = createRelation("p", List(Sort.Integer))
          val Seq(x, y) = for (name <- Seq("x", "y")) yield createConstant(name)

          val clauses : Seq[Clause] = List(
            pr(x) :- (x >= 0),
            false :- (pr(x), pr(y), x === y & x > 5)
          )
          new SLDSymex[Clause](clauses).solve()
        } should beUnsat
      }
      "Either selection rule (unsat), with a valid counterexample" in {
        scope {
          val pr = createRelation("p", List(Sort.Integer))
          val qr = createRelation("q", List(Sort.Integer))
          val rr = createRelation("r", List(Sort.Integer))
          val sr = createRelation("s", List(Sort.Integer))
          val Seq(x, y, z) =
            for (name <- Seq("x", "y", "z")) yield createConstant(name)

          // after q is resolved, p is selected under Newest and s under
          // Oldest, so one of the two selected atoms is not the first one
          val clauses : Seq[Clause] = List(
            pr(x) :- (x === 1),
            rr(y) :- (y === 2),
            sr(z) :- (z === 0),
            qr(x + y) :- (pr(x), rr(y)),
            false :- (qr(x), sr(z), x + z === 3)
          )
          for (selection <- GlobalParameters.SLDAtomSelection.values) {
            val result = new SLDSymex[Clause](clauses, None, selection).solve()
            result should beUnsat
            val params = GlobalParameters.get.clone
            params.verifySolCEX = true
            GlobalParameters.withValue(params) {
              HornWrapper.verifyCEX(result.right.get, clauses)
            }
          }
        }
      }
    }

    "Atom selection" - {
      // p unfolds without end, q fails at once
      def endlessChainBesideFailingAtom : Seq[Clause] = {
        val pr = createRelation("p", List(Sort.Integer))
        val qr = createRelation("q", List(Sort.Integer))
        val x  = createConstant("x")
        List(
          pr(x) :- (x < 0),
          pr(x) :- pr(x + 1),
          qr(x) :- (x === 0),
          qr(x) :- (x === -1),
          false :- (pr(x), qr(x), x > 0)
        )
      }
      "Newest (Prolog's rule) resolves the new p atom each time " +
      "(depth bound, unknown)" in {
        scope {
          val symex = new SLDSymex[Clause](endlessChainBesideFailingAtom,
                                           maxDepth = Some(5))
          assertThrows[InconclusiveException] { symex.solve() }
        }
      }
      "Oldest resolves q after one step (sat)" in {
        scope {
          new SLDSymex[Clause](endlessChainBesideFailingAtom,
                               maxDepth = Some(5),
                               GlobalParameters.SLDAtomSelection.Oldest)
            .solve()
        } should beSat
      }
    }

    "Undecided empty goal, no other refutation (unknown)" in {
      scope {
        val pr = createRelation("p", List(Sort.Integer))
        val x  = createConstant("x")

        val clauses : Seq[Clause] = List(
          pr(x) :- (x === 0),
          false :- (pr(x), x >= 0)
        )
        val e = the [InconclusiveException] thrownBy
          new GivingUpSymex(clauses).solve()
        e.candidateSolution shouldBe empty
      }
    }
  }
}
