package lazabs.horn.symex

import ap.api.SimpleAPI
import ap.parser.IExpression._
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

  private def withSubsumption[A](comp : => A) : A = {
    val params = lazabs.GlobalParameters.get
    val old    = params.symexUseSubsumption
    params.symexUseSubsumption = true
    try comp
    finally params.symexUseSubsumption = old
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
        withSubsumption {
          withTestTimeout(10000) {
            new BreadthFirstForwardSymex(clauses).solve()
          }
        }
      } should beSat
    }
  }
}
