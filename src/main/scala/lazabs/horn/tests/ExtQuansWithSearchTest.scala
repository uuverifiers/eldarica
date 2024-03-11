/**
 * Copyright (c) 2023 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package lazabs.horn.tests

import ap.parser._
import ap.theories._
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.bottomup._
import lazabs.horn.extendedquantifiers.{InstrumentationLoop, InstrumentationOperator}
import HornClauses._
import IExpression._
import ap.api.SimpleAPI
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.extendedquantifiers.instrumentationoperators.{BooleanInstrumentationOperator, GeneralInstrumentationOperator}
import lazabs.horn.extendedquantifiers.theories._
import lazabs.prover.PrincessWrapper.{expr2Formula, expr2Term}

object ExtQuansWithSearchTest extends App {
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)
  lazabs.GlobalParameters.get.assertions = true

  val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)

  def sum (a : ITerm, b : ITerm) : ITerm = a + b
  def invSum (a : ITerm, b : ITerm) : ITerm = a - b
  val extQuan = new ExtendedQuantifier("sum", ar, i(0), sum, Some(invSum), None, None)
  TheoryRegistry.register(extQuan)

  {
    val a1 = new SortedConstantTerm("a1", ar.sort)
    val a2 = new SortedConstantTerm("a2", ar.sort)
    val i = new ConstantTerm("i")

    val p = for (i <- 0 until 5) yield (new MonoSortedPredicate("p" + i,
      Seq(ar.sort, ar.sort, Sort.Integer)))

     //SELECT (read)
    val clauses = List(
      p(0)(a1, a2, i)     :- (i === 0),
      p(0)(a1, a2, i + 1) :- (p(0)(a1, a2, i), 3 === ar.select(a1, i),
                                               4 === ar.select(a2, i), i < 10),
      p(1)(a1, a2, i)     :- (p(0)(a1, a2, i), i >= 10),
      false               :- (p(1)(a1, a2, i),
                             extQuan.morphism(a1, 0, 10) =/= 30) // [0, 10)
      )

    val instOps : Map[AbstractExtendedQuantifier, InstrumentationOperator] =
      Map(
        extQuan -> new GeneralInstrumentationOperator(extQuan)
        )
    val instrLoop = new InstrumentationLoop(
      clauses, EmptyVerificationHints, instOps)

    instrLoop.result match {
      case Left(sln) =>
        println("SAFE")
        for((pred, f) <- sln) {
          println(s"$pred -> ${SimpleAPI.pp(f)}")
        }
      case Right(cex) =>
        println("UNSAFE")
        cex.prettyPrint
    }

    println(instrLoop.result)
  }
}

object ExtQuansForallTest extends App {
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)
  lazabs.GlobalParameters.get.assertions = true

  {
    val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)
    val reduceOp  : (ITerm, ITerm) => ITerm =
      (a : ITerm, b : ITerm) => expr2Term(expr2Formula(a) &&& expr2Formula(b))

    val a1 = new SortedConstantTerm("a1", ar.sort)
    val i = new ConstantTerm("i")

    val p = for (i <- 0 until 5) yield (new MonoSortedPredicate("p" + i,
                                                                Seq(ar.sort, Sort.Integer)))

    val arrAccess = ar.select(a1, i)
    val arrIndex = i
    val pred = arrAccess === i
    val predicate : (ITerm, ITerm) => ITerm =
      (access : ITerm, index : ITerm) => expr2Term(
        ExpressionReplacingVisitor(
          ExpressionReplacingVisitor(pred, arrAccess, access),
          arrIndex, index))
    val extQuan = new ExtendedQuantifierWithPredicate(
      name = "\\forall",
      arrayTheory = ar,
      identity = expr2Term(IBoolLit(true)),
      reduceOp = reduceOp,
      invReduceOp = None,
      predicate = predicate,
      rangeFormulaLo = Some((ghostLo : ITerm, lo : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostLo <= lo, ghostLo >=
                                                                  lo)),
      rangeFormulaHi = Some((ghostHi : ITerm, hi : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostHi >= hi, ghostHi <= hi)))
    TheoryRegistry register extQuan

    val clauses = List(
      p(0)(a1, i)     :- (i === 0),
      p(0)(a1, i + 1) :- (p(0)(a1, i), i === ar.select(a1, i), i < 3),
      p(1)(a1, i)     :- (p(0)(a1, i), i >= 3),
      false           :- (p(1)(a1, i),
        !expr2Formula(extQuan.morphism(a1, 0, 3))) // [0, 3)
      )

    val instOps : Map[AbstractExtendedQuantifier, InstrumentationOperator] =
      Map(
        extQuan -> new BooleanInstrumentationOperator(extQuan)
      )

    val instrLoop = new InstrumentationLoop(
      clauses, EmptyVerificationHints, instOps)

    instrLoop.result match {
      case Left(sln) =>
        println("SAFE")
        for((p, f) <- sln) {
          println(s"$p -> ${SimpleAPI.pp(f)}")
        }
      case Right(cex) =>
        println("UNSAFE")
        cex.prettyPrint
    }

    println(instrLoop.result)
  }
}

object ExtQuansExistsTestSafe extends App {
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)
  lazabs.GlobalParameters.get.assertions = true

  {
    val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)
    val reduceOp  : (ITerm, ITerm) => ITerm =
      (a : ITerm, b : ITerm) => expr2Term(expr2Formula(a) ||| expr2Formula(b))

    val a1 = new SortedConstantTerm("a1", ar.sort)
    val i = new ConstantTerm("i")

    val p = for (i <- 0 until 5) yield (new MonoSortedPredicate("p" + i,
                                                                Seq(ar.sort, Sort.Integer)))

    val arrAccess = ar.select(a1, i)
    val arrIndex = i
    val pred = arrAccess === 2
    val predicate : (ITerm, ITerm) => ITerm =
      (access : ITerm, index : ITerm) => expr2Term(
        ExpressionReplacingVisitor(
          ExpressionReplacingVisitor(pred, arrAccess, access),
          arrIndex, index))
    val extQuan = new ExtendedQuantifierWithPredicate(
      name = "\\exists",
      arrayTheory = ar,
      identity = expr2Term(IBoolLit(false)),
      reduceOp = reduceOp,
      invReduceOp = None,
      predicate = predicate,
      rangeFormulaLo = Some((ghostLo : ITerm, lo : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostLo <= lo, ghostLo >=
                                                                  lo)),
      rangeFormulaHi = Some((ghostHi : ITerm, hi : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostHi >= hi, ghostHi <= hi)))
    TheoryRegistry register extQuan

    val clauses = List(
      p(0)(a1, i)     :- (i === 0),
      p(0)(a1, i + 1) :- (p(0)(a1, i), i === ar.select(a1, i), i < 3),
      p(1)(a1, i)     :- (p(0)(a1, i), i >= 3),
      false           :- (p(1)(a1, i),
        !expr2Formula(extQuan.morphism(a1, 0, 3))) // [0, 3)
      )

    val instOps : Map[AbstractExtendedQuantifier, InstrumentationOperator] =
      Map(
        extQuan -> new BooleanInstrumentationOperator(extQuan)
      )

    val instrLoop = new InstrumentationLoop(
      clauses, EmptyVerificationHints, instOps)

    instrLoop.result match {
      case Left(sln) =>
        println("SAFE")
        for((p, f) <- sln) {
          println(s"$p -> ${SimpleAPI.pp(f)}")
        }
      case Right(cex) =>
        println("UNSAFE")
        cex.prettyPrint
    }

    println(instrLoop.result)
  }
}

object ExtQuansExistsTestUnsafe extends App {
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)
  lazabs.GlobalParameters.get.assertions = true

  {
    val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)
    val reduceOp  : (ITerm, ITerm) => ITerm =
      (a : ITerm, b : ITerm) => expr2Term(expr2Formula(a) ||| expr2Formula(b))

    val a1 = new SortedConstantTerm("a1", ar.sort)
    val i = new ConstantTerm("i")

    val p = for (i <- 0 until 5) yield (new MonoSortedPredicate("p" + i,
                                                                Seq(ar.sort, Sort.Integer)))

    val arrAccess = ar.select(a1, i)
    val arrIndex = i
    val pred = arrAccess === 4
    val predicate : (ITerm, ITerm) => ITerm =
      (access : ITerm, index : ITerm) => expr2Term(
        ExpressionReplacingVisitor(
          ExpressionReplacingVisitor(pred, arrAccess, access),
          arrIndex, index))
    val extQuan = new ExtendedQuantifierWithPredicate(
      name = "\\exists",
      arrayTheory = ar,
      identity = expr2Term(IBoolLit(false)),
      reduceOp = reduceOp,
      invReduceOp = None,
      predicate = predicate,
      rangeFormulaLo = Some((ghostLo : ITerm, lo : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostLo <= lo, ghostLo >=
                                                                  lo)),
      rangeFormulaHi = Some((ghostHi : ITerm, hi : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostHi >= hi, ghostHi <= hi)))
    TheoryRegistry register extQuan

    val clauses = List(
      p(0)(a1, i)     :- (i === 0),
      p(0)(a1, i + 1) :- (p(0)(a1, i), i === ar.select(a1, i), i < 3),
      p(1)(a1, i)     :- (p(0)(a1, i), i >= 3),
      false           :- (p(1)(a1, i),
        !expr2Formula(extQuan.morphism(a1, 0, 3))) // [0, 3)
      )

    val instOps : Map[AbstractExtendedQuantifier, InstrumentationOperator] =
      Map(
        extQuan -> new BooleanInstrumentationOperator(extQuan)
      )

    val instrLoop = new InstrumentationLoop(
      clauses, EmptyVerificationHints, instOps)

    instrLoop.result match {
      case Left(sln) =>
        println("SAFE")
        for((p, f) <- sln) {
          println(s"$p -> ${SimpleAPI.pp(f)}")
        }
      case Right(cex) =>
        println("UNSAFE")
        cex.prettyPrint
    }

    println(instrLoop.result)
  }
}

object ExtQuansNumofTestUnsafe extends App {
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)
  lazabs.GlobalParameters.get.assertions = true

  {
    val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)
    val reduceOp  : (ITerm, ITerm) => ITerm =
      (a : ITerm, b : ITerm) => ite(expr2Formula(b), a+++1, a)
      // expr2Term(expr2Formula(a) ||| expr2Formula(b))

    val a1 = new SortedConstantTerm("a1", ar.sort)
    val i = new ConstantTerm("i")

    val p = for (i <- 0 until 5) yield (new MonoSortedPredicate("p" + i,
                                                                Seq(ar.sort, Sort.Integer)))

    val arrAccess = ar.select(a1, i)
    val arrIndex = i
    val pred = arrAccess > 1 //should be 0
    val predicate : (ITerm, ITerm) => ITerm =
      (access : ITerm, index : ITerm) => expr2Term(
        ExpressionReplacingVisitor(
          ExpressionReplacingVisitor(pred, arrAccess, access),
          arrIndex, index))
    val extQuan = new ExtendedQuantifierWithPredicate(
      name = "\\numof",
      arrayTheory = ar,
      identity = 0,//expr2Term(IBoolLit(false)),
      reduceOp = reduceOp,
      invReduceOp = None,
      predicate = predicate,
      rangeFormulaLo = Some((ghostLo : ITerm, lo : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostLo <= lo, ghostLo >=
                                                                  lo)),
      rangeFormulaHi = Some((ghostHi : ITerm, hi : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostHi >= hi, ghostHi <= hi)))
    TheoryRegistry register extQuan

    val clauses = List(
      p(0)(a1, i)     :- (i === 0),
      p(0)(a1, i + 1) :- (p(0)(a1, i), i === ar.select(a1, i), i < 3),
      p(1)(a1, i)     :- (p(0)(a1, i), i >= 3),
      false           :- (p(1)(a1, i),
        !((extQuan.morphism(a1, 0, 3)) === 2)) // [0, 3)
      )

    val instOps : Map[AbstractExtendedQuantifier, InstrumentationOperator] =
      Map(
        extQuan -> new BooleanInstrumentationOperator(extQuan)
      )

    val instrLoop = new InstrumentationLoop(
      clauses, EmptyVerificationHints, instOps)

    instrLoop.result match {
      case Left(sln) =>
        println("SAFE")
        for((p, f) <- sln) {
          println(s"$p -> ${SimpleAPI.pp(f)}")
        }
      case Right(cex) =>
        println("UNSAFE")
        cex.prettyPrint
    }

    println(instrLoop.result)
  }
}

object ExtQuansNumofTestSafe extends App {
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)
  lazabs.GlobalParameters.get.assertions = true

  {
    val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)
    val reduceOp  : (ITerm, ITerm) => ITerm =
      (a : ITerm, b : ITerm) => ite(expr2Formula(b), a+++1, a)
      // expr2Term(expr2Formula(a) ||| expr2Formula(b))

    val a1 = new SortedConstantTerm("a1", ar.sort)
    val i = new ConstantTerm("i")

    val p = for (i <- 0 until 5) yield (new MonoSortedPredicate("p" + i,
                                                                Seq(ar.sort, Sort.Integer)))

    val arrAccess = ar.select(a1, i)
    val arrIndex = i
    val pred = arrAccess > 0
    val predicate : (ITerm, ITerm) => ITerm =
      (access : ITerm, index : ITerm) => expr2Term(
        ExpressionReplacingVisitor(
          ExpressionReplacingVisitor(pred, arrAccess, access),
          arrIndex, index))
    val extQuan = new ExtendedQuantifierWithPredicate(
      name = "\\numof",
      arrayTheory = ar,
      identity = 0,//expr2Term(IBoolLit(false)),
      reduceOp = reduceOp,
      invReduceOp = None,
      predicate = predicate,
      rangeFormulaLo = Some((ghostLo : ITerm, lo : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostLo <= lo, ghostLo >=
                                                                  lo)),
      rangeFormulaHi = Some((ghostHi : ITerm, hi : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostHi >= hi, ghostHi <= hi)))
    TheoryRegistry register extQuan

    val clauses = List(
      p(0)(a1, i)     :- (i === 0),
      p(0)(a1, i + 1) :- (p(0)(a1, i), i === ar.select(a1, i), i < 3),
      p(1)(a1, i)     :- (p(0)(a1, i), i >= 3),
      false           :- (p(1)(a1, i),
        !((extQuan.morphism(a1, 0, 3)) === 2)) // [0, 3)
      )

    val instOps : Map[AbstractExtendedQuantifier, InstrumentationOperator] =
      Map(
        extQuan -> new BooleanInstrumentationOperator(extQuan)
      )

    val instrLoop = new InstrumentationLoop(
      clauses, EmptyVerificationHints, instOps)

    instrLoop.result match {
      case Left(sln) =>
        println("SAFE")
        for((p, f) <- sln) {
          println(s"$p -> ${SimpleAPI.pp(f)}")
        }
      case Right(cex) =>
        println("UNSAFE")
        cex.prettyPrint
    }

    println(instrLoop.result)
  }
}



object ExtQuansForallAlienTermTestSafe extends App {
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)
  lazabs.GlobalParameters.get.assertions = true

  {
    val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)
    val reduceOp  : (ITerm, ITerm) => ITerm =
      (a : ITerm, b : ITerm) => expr2Term(expr2Formula(a) &&& expr2Formula(b))

    val a1 = new SortedConstantTerm("a1", ar.sort)
    val i = new ConstantTerm("i")
    val c = new ConstantTerm("c") // this is the alien term
    val c0 = new ConstantTerm("c")
    val c1 = new ConstantTerm("c")
    val c2 = new ConstantTerm("c")

    val p = for (i <- 0 until 5) yield (new MonoSortedPredicate("p" + i,
                                                                Seq(ar.sort, Sort.Integer, Sort.Integer)))

    val arrAccess = ar.select(a1, i)
    val arrIndex = i
    val pred = arrAccess === c // note the rhs is an alien term
    val predicate : (ITerm, ITerm) => ITerm =
      (access : ITerm, index : ITerm) => expr2Term(
        ExpressionReplacingVisitor(
          ExpressionReplacingVisitor(pred, arrAccess, access),
          arrIndex, index))
    val extQuan = new ExtendedQuantifierWithPredicate(
      name = "\\forall",
      arrayTheory = ar,
      identity = expr2Term(IBoolLit(true)),
      reduceOp = reduceOp,
      invReduceOp = None,
      predicate = predicate,
      rangeFormulaLo = Some((ghostLo : ITerm, lo : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostLo <= lo, ghostLo >=
                                                                  lo)),
      rangeFormulaHi = Some((ghostHi : ITerm, hi : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostHi >= hi, ghostHi <= hi)))
    TheoryRegistry register extQuan

    val clauses = List(
      p(0)(a1, i, c2)      :- (i === 0, c2 === 42),
      p(0)(a1, i + 1, c0) :- (p(0)(a1, i, c0), c0 === ar.select(a1, i), i < 3),
      p(1)(a1, i, c1)     :- (p(0)(a1, i, c1), i >= 3),
      false               :- (p(1)(a1, i, c),
        !expr2Formula(extQuan.morphism(a1, 0, 3, c))) // [0, 3)
      )

    /**
     * The result here is expected to be safe, if unsafe, that means alien
     * terms are not handled properly.
     * Multiple `c` terms with the same name is introduced, to reflect that
     * in the clauses these c's are not guaranteed to be the same term.
     */

    val instOps : Map[AbstractExtendedQuantifier, InstrumentationOperator] =
      Map(
        extQuan -> new BooleanInstrumentationOperator(extQuan)
      )

    val instrLoop = new InstrumentationLoop(
      clauses, EmptyVerificationHints, instOps)

    instrLoop.result match {
      case Left(sln) =>
        println("SAFE")
        for((p, f) <- sln) {
          println(s"$p -> ${SimpleAPI.pp(f)}")
        }
      case Right(cex) =>
        println("UNSAFE")
        cex.prettyPrint
    }

    println(instrLoop.result)
  }
}

object ExtQuansForallAlienTermTestUnsafe extends App {
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)
  lazabs.GlobalParameters.get.assertions = true

  {
    val ar = ExtArray(Seq(Sort.Integer), Sort.Integer)
    val reduceOp  : (ITerm, ITerm) => ITerm =
      (a : ITerm, b : ITerm) => expr2Term(expr2Formula(a) &&& expr2Formula(b))

    val a1 = new SortedConstantTerm("a1", ar.sort)
    val i = new ConstantTerm("i")
    val c = new ConstantTerm("c")
    val c0 = new ConstantTerm("c")
    val c1 = new ConstantTerm("c")
    val c2 = new ConstantTerm("c")
    val actualC = new ConstantTerm("c")  // this is the actual alien term

    val p = for (i <- 0 until 5) yield (new MonoSortedPredicate(
      "p" + i, Seq(ar.sort, Sort.Integer, Sort.Integer, Sort.Integer)))

    val arrAccess = ar.select(a1, i)
    val arrIndex = i
    val pred = arrAccess === actualC // note the rhs is an alien term
    val predicate : (ITerm, ITerm) => ITerm =
      (access : ITerm, index : ITerm) => expr2Term(
        ExpressionReplacingVisitor(
          ExpressionReplacingVisitor(pred, arrAccess, access),
          arrIndex, index))
    val extQuan = new ExtendedQuantifierWithPredicate(
      name = "\\forall",
      arrayTheory = ar,
      identity = expr2Term(IBoolLit(true)),
      reduceOp = reduceOp,
      invReduceOp = None,
      predicate = predicate,
      rangeFormulaLo = Some((ghostLo : ITerm, lo : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostLo <= lo, ghostLo >=
                                                                  lo)),
      rangeFormulaHi = Some((ghostHi : ITerm, hi : ITerm, p : ITerm) =>
                              ite(expr2Formula(p), ghostHi >= hi, ghostHi <= hi)))
    TheoryRegistry register extQuan

    val clauses = List(
      p(0)(a1, i, c, actualC)      :- (i === 0, c === 42, actualC === 3),
      p(0)(a1, i + 1, c0, actualC) :- (p(0)(a1, i, c0, actualC), c0 === ar.select(a1, i), i < 3),
      p(1)(a1, i, c1, actualC)     :- (p(0)(a1, i, c1, actualC), i >= 3),
      false                      :- (p(1)(a1, i, c2, actualC),
        !expr2Formula(extQuan.morphism(a1, 0, 3, actualC))) // [0, 3)
      )

    /**
     * The result here is expected to be unsafe, if safe, that means an assertion
     * making sure that the guessed alien term was not added while rewriting
     * aggregate. It might also be safe if the heuristic for guessing the
     * alien term is changed (i.e., not picking the first one with a matching
     * name).
     */

    val instOps : Map[AbstractExtendedQuantifier, InstrumentationOperator] =
      Map(
        extQuan -> new BooleanInstrumentationOperator(extQuan)
      )

    val instrLoop = new InstrumentationLoop(
      clauses, EmptyVerificationHints, instOps)

    instrLoop.result match {
      case Left(sln) =>
        println("SAFE")
        for((p, f) <- sln) {
          println(s"$p -> ${SimpleAPI.pp(f)}")
        }
      case Right(cex) =>
        println("UNSAFE")
        cex.prettyPrint
    }

    println(instrLoop.result)
  }
}
