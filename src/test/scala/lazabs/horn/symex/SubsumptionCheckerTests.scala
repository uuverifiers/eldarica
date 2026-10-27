package lazabs.horn.symex

import ap.api.SimpleAPI
import ap.parser.IExpression._
import ap.theories.bitvectors.ModuloArithmetic._
import lazabs.GlobalParameters
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.CHCResultMatchers
import org.scalatest.freespec.AnyFreeSpec

class SubsumptionCheckerTests
    extends AnyFreeSpec
    with CHCResultMatchers {

  import HornClauses._

  ap.util.Debug.enableAllAssertions(true)

  private def withTestTimeout[A](millis : Long)(comp : => A) : A = {
    val params   = lazabs.GlobalParameters.get
    val deadline = System.currentTimeMillis + millis
    val old      = params.timeoutChecker
    params.timeoutChecker = () => {
      if (System.currentTimeMillis > deadline)
        throw lazabs.Main.TimeoutException
    }
    try comp
    finally params.timeoutChecker = old
  }

  "Entailed states are dropped and the search terminates" in {
    // p(x) holds for x >= 0, 1, 2, ...
    // each new state entails the previous one, so with subsumption the
    // this should terminate (with sat)
    SimpleAPI.withProver { p =>
      import p._
      scope {
        val pr = createRelation("p", List(Sort.Integer))
        val x  = createConstant("x")

        val clauses : Seq[HornClauses.Clause] = List(
          pr(x) :- (x >= 0),
          pr(x + 1) :- pr(x),
          (x >= 0) :- pr(x)
        )
        withTestTimeout(10000) {
          new BreadthFirstForwardSymex(clauses).solve()
        }
      } should beSat
    }
  }

  // full checks, so that the order of the states does not depend on time
  private def solveWithDepth(clauses : Seq[HornClauses.Clause], depth : Int) = {
    val params = GlobalParameters.get.clone
    params.symexStateChecks = GlobalParameters.SymexStateChecks.Full
    GlobalParameters.withValue(params) {
      new BreadthFirstForwardSymex(clauses, maxDepth = Some(depth)).solve()
    }
  }

  // in each test, the depth bound ends the search inconclusive unless the
  // last state of p that the bound allows is found subsumed or a duplicate

  "Conjuncts unconnected to the arguments are dropped from feasible states" in {
    // the fact is stored with its unconnected conjunct, so only the second
    // derived state is a duplicate
    SimpleAPI.withProver { p =>
      import p._
      scope {
        val pr = createRelation("p", List(Sort.Integer))
        val x  = createConstant("x")
        val c  = createConstant("c", UnsignedBVSort(8))

        solveWithDepth(List(
          pr(x) :- (x === 0 & extract(0, 0, c) === bv(1, 0)),
          pr(x) :- (pr(x), extract(0, 0, c) === bv(1, 1)),
          false :- (pr(x), x > 0)), depth = 3)
      } should beSat
    }
  }

  "Locals defined by literals keep their names in larger states" in {
    // the local of y[7:4] in the second state is ordered after that of x[7:4]
    SimpleAPI.withProver { p =>
      import p._
      scope {
        val bv8 = UnsignedBVSort(8)
        val pr  = createRelation("p", List(bv8, bv8))
        val x   = createConstant("x", bv8)
        val y   = createConstant("y", bv8)

        solveWithDepth(List(
          pr(x, y) :- (extract(7, 4, x) <= 5),
          pr(x, y) :- (pr(x, y), extract(7, 4, y) <= 2),
          false :- (pr(x, y), extract(7, 4, x) >= 10)), depth = 2)
      } should beSat
    }
  }

  "A local with a second definition keeps the name of the first" in {
    // in the second state, y[3:0] defines the local of x[7:4] too, and the
    // local of z[7:4] is ordered after it
    SimpleAPI.withProver { p =>
      import p._
      scope {
        val bv8 = UnsignedBVSort(8)
        val pr  = createRelation("p", List(bv8, bv8, bv8))
        val x   = createConstant("x", bv8)
        val y   = createConstant("y", bv8)
        val z   = createConstant("z", bv8)

        solveWithDepth(List(
          pr(x, y, z) :- (extract(7, 4, x) <= 5),
          pr(x, y, z) :- (pr(x, y, z),
                          extract(7, 4, x) === extract(3, 0, y) &
                          extract(7, 4, z) <= 2),
          false :- (pr(x, y, z), extract(7, 4, x) >= 10)), depth = 2)
      } should beSat
    }
  }
}
