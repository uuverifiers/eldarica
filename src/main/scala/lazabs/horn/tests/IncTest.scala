
package lazabs.horn.tests

import ap.SimpleAPI
import lazabs.horn.bottomup._
import HornClauses._
import ap.parser._
import IExpression.Sort
import ap.terfor.{TermOrder, TerForConvenience}
import ap.terfor.conjunctions.Conjunction

object IncTest extends App {

  lazabs.GlobalParameters.get.assertions = true

  println("Starting incremental test ...")

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    val x    = createConstant("x")
    val y    = createConstant("y")
    val n    = createConstant("n")

    val I    = createRelation("I", Seq(Sort.Integer, Sort.Integer, Sort.Integer))

    val Init = createRelation("Init", Seq(Sort.Integer))
    val f0   = createRelation("f0", Seq())
    val f1   = createRelation("f1", Seq())
    val f2   = createRelation("f2", Seq())

    val clauses = {
      import ap.parser.IExpression._
      List(
        I(0, 0, n) :- (f0(), Init(n)),
        I(x + 1, y + 1, n) :- (f1(), I(x, y, n), y < n),
        false :- (f2(), I(x, y, n), x > 2*n)
      )
    }

    val incSolver =
      new IncrementalHornPredAbs(clauses,
                                 Map(),
                                 Set(f0, f1, f2, Init),
                                 DagInterpolator.interpolatingPredicateGenCEXAndOr _)

    implicit val o = TermOrder.EMPTY
    import TerForConvenience._
    import Conjunction.{TRUE, FALSE}

    val r1 = incSolver.checkWithSubstitution(
              Map(
                Init -> TRUE, f0 -> TRUE, f1 -> TRUE, f2 -> TRUE
              ))
    println(r1)
    assert(r1.isRight)

    val r2 = incSolver.checkWithSubstitution(
          Map(
                Init -> (v(0) > 0), f0 -> TRUE, f1 -> TRUE, f2 -> TRUE
              ))
    println(r2)
    assert(r2.isLeft)

    val r3 = incSolver.checkWithSubstitution(
          Map(
                Init -> TRUE, f0 -> TRUE, f1 -> FALSE, f2 -> TRUE
              ))
    println(r3)
    assert(r3.isRight)

  }

}
