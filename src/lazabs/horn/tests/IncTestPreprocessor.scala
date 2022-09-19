
package lazabs.horn.tests

import ap.SimpleAPI
import lazabs.horn.bottomup._
import HornClauses._
import ap.parser._
import IExpression.Sort
import ap.terfor.{TermOrder, TerForConvenience}
import ap.terfor.conjunctions.Conjunction

import lazabs.horn.preprocessor.DefaultPreprocessor
import lazabs.horn.abstractions.EmptyVerificationHints

object IncTestPreprocessor extends App {

  lazabs.GlobalParameters.get.assertions = true

  println("Starting incremental test with preprocessing ...")

  SimpleAPI.withProver(enableAssert = true) { p =>
    import p._

    val x    = createConstant("x")
    val y    = createConstant("y")
    val n    = createConstant("n")

    val I    = createRelation("I", Seq(Sort.Integer, Sort.Integer, Sort.Integer))
    val I2   = createRelation("I2", Seq(Sort.Integer, Sort.Integer, Sort.Integer))
    val I3   = createRelation("I3", Seq(Sort.Integer, Sort.Integer, Sort.Integer))

    val Init = createRelation("Init", Seq(Sort.Integer))
    val f0   = createRelation("f0", Seq())
    val f1   = createRelation("f1", Seq())
    val f2   = createRelation("f2", Seq())

    val clauses = {
      import ap.parser.IExpression._
      List(
        I(0, 0, n) :- (f0(), Init(n)),
        I2(x, y, n) :- (I(x, y, n), y < n),
        I3(x, y, n) :- (I(x, y, n), y < 10),
        I(x + 1, y + 1, n) :- (f1(), I2(x, y, n)),
        false :- (f2(), I(x, y, n), x > 2*n)
      )
    }

    val preprocessor = new DefaultPreprocessor

    val (simplifiedClauses, simpPreHints, backTranslator) =
      preprocessor.process(clauses, EmptyVerificationHints,
                           Set(f0, f1, f2, Init))

    val incSolver =
      new IncrementalHornPredAbs(simplifiedClauses,
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
