
package lazabs.horn.bottomup

import ap.SimpleAPI
import HornClauses._
import ap.parser._
import IExpression.Sort
import ap.terfor.{TermOrder, TerForConvenience}
import ap.terfor.conjunctions.Conjunction

object CEXMinerTest extends App {

  lazabs.GlobalParameters.get.assertions = true

  def expect[A](x : A, expected : A => Boolean) : A = {
    assert(expected(x))
    x
  }

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    val x    = createConstant("x")
    val y    = createConstant("y")
    val n    = createConstant("n")

    val I    = createRelation("I", Seq(Sort.Integer, Sort.Integer, Sort.Integer))

    val clauses = {
      import ap.parser.IExpression._
      List(
        I(0, 0, n) :- true,
        I(x + 1, y + 1, n) :- (I(x, y, n), y < n),
        I(x + 2, y + 1, n) :- (I(x, y, n), y < n),
        false :- (I(x, y, n), x > 2*n)
      )
    }

    val miner = new CounterexampleMiner (clauses,
                                         DagInterpolator.interpolatingPredicateGenCEXAndOr _)

  }

}
