/**
 * Copyright (c) 2021-2022 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.bottomup

import ap.Signature
import ap.basetypes.IdealInt
import ap.parser._
import ap.theories.TheoryCollector
import ap.terfor.{ConstantTerm, TerForConvenience}
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.types.Sort

import Util._
import DisjInterpolator.{AndOrNode, AndNode, OrNode}
import HornClauses.{ConstraintClause, Literal}

import lattopt._

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

object BoundAnalyzer {

  private val MaxBound = IdealInt("10000000000000000000000000")

}

class BoundAnalyzer[CC <% HornClauses.ConstraintClause]
      (iClauses : Seq[CC],
       predicateGenerator : Dag[AndOrNode[NormClause, Unit]] =>
        Either[Seq[(Predicate, Seq[Conjunction])],
               Dag[(IAtom, NormClause)]]) {
  import HornClauses.FALSE
  import TerForConvenience._
  import BoundAnalyzer._

  val allPreds = (HornClauses allPredicatesCC iClauses).toIndexedSeq.sortBy(_.name)

  val consideredArgs =
    (for (p <- allPreds.iterator) yield {
       val args =
         for ((s, n) <- (HornPredAbs predArgumentSorts p).zipWithIndex;
              if s == Sort.Integer)
         yield n
       p -> args
     }).toMap

  val lowerBounds, upperBounds = new MHashMap[(Predicate, Int), IdealInt]
  val lowerValues, upperValues = new MHashMap[(Predicate, Int), IdealInt]

//  println(allPreds)
//  println(consideredArgs)

  val nonAssertionClauses =
    for (c <- iClauses; if c.head.predicate != FALSE) yield c

  val boundPredicates =
    (for (p <- allPreds)
     yield (p -> new Predicate(p.name + "_bounds", p.arity))).toMap

  val boundClauses =
    for (p <- allPreds) yield {
      val boundP = boundPredicates(p)

      new ConstraintClause {
        val head = new Literal {
          val predicate = boundP
          val relevantArguments = for (n <- 0 until p.arity) yield n
        }
        val body = List(new Literal {
          val predicate = p
          val relevantArguments = for (n <- 0 until p.arity) yield n
        })
        val localVariableNum = 0

        def instantiateConstraint(headArguments : Seq[ConstantTerm],
                                  bodyArguments: Seq[Seq[ConstantTerm]],
                                  localVariables : Seq[ConstantTerm],
                                  sig : Signature) : Conjunction = {
          implicit val order = sig.order
          headArguments === bodyArguments(0)
        }
      }
    }

  type MergedCC = Either[CC, ConstraintClause]

  val allClauses : Seq[MergedCC] =
    (nonAssertionClauses map (Left(_))) ++ (boundClauses map (Right(_)))

  val solver =
    new IncrementalHornPredAbs(allClauses,
                               Map(),
                               boundPredicates.values.toSet,
                               predicateGenerator)

  for ((p, bounds) <- solver.baseContext.relationSymbolBounds;
       pred = p.pred;
       if allPreds contains pred) {
    val red  = ReduceWithConjunction(bounds, bounds.order)
    val args = consideredArgs(pred)

    for ((c, n) <- p.arguments.head.zipWithIndex)
      if (args contains n) {
        for (b <- red lowerBound c)
          lowerBounds.put((pred, n), b)
        for (b <- red upperBound c)
          upperBounds.put((pred, n), b)
      }
  }

//  println(lowerBounds)
//  println(upperBounds)

  private def getLowerTestValue(pred : Predicate, index : Int) : IdealInt = {
    var res = IdealInt.MINUS_ONE

    while (lowerValues.getOrElse((pred, index), res + 1) <= res)
      res = res * 2

    res
  }

  private def getUpperTestValue(pred : Predicate, index : Int) : IdealInt = {
    var res = IdealInt.ONE

    while (upperValues.getOrElse((pred, index), res - 1) >= res)
      res = res * 2

    res
  }

  private def addObservedValues(cex : Dag[(IAtom, MergedCC)]) : Unit =
    for ((atom, _) <- cex.iterator;
         pred = atom.pred;
         if allPreds contains pred) {
      val args = consideredArgs(pred)
      for ((IIntLit(value), n) <- atom.args.iterator.zipWithIndex;
           if args contains n) {
        if (value < lowerValues.getOrElse((pred, n), value + 1))
          lowerValues.put((pred, n), value)
        if (value > upperValues.getOrElse((pred, n), value - 1))
          upperValues.put((pred, n), value)
      }
    }

  implicit val order = solver.baseContext.sf.order

  private def withTimeout[A](comp : => A) : Unit = {
    val startTime = System.currentTimeMillis
    val TO = lazabs.GlobalParameters.get.boundsAnalysisTO

    lazabs.GlobalParameters.get.timeoutChecker = {
      () => if (System.currentTimeMillis - startTime > TO.toLong)
              throw lazabs.Main.TimeoutException
    }

    try {
      comp
    } catch {
      case lazabs.Main.TimeoutException =>
        Console.err.println(" timeout")
        // continue
    }
  }

  private def testBound(pred : Predicate, argIndex : Int,
                        testValue : IdealInt, upper : Boolean) = {
    Console.err.print("   testing " + testValue + " ...")

    val subst =
      (for (p <- allPreds)
       yield (boundPredicates(p) -> Conjunction.TRUE)).toMap + (
        boundPredicates(pred) ->
          (if (upper)
             (conj(v(argIndex) <= testValue))
           else
             (conj(v(argIndex) >= testValue))))

    solver.checkWithSubstitution(subst) match {
      case Left(_) => {
        Console.err.println(" is bound!")
        (if (upper) upperBounds else lowerBounds).put(
          (pred, argIndex), testValue)
      }
      case Right(cex) => {
        Console.err.println(" nope")
        addObservedValues(cex)
      }
    }
  }

  for (pred <- allPreds; argIndex <- consideredArgs(pred)) {
    if (lowerBounds contains ((pred, argIndex))) {
      Console.err.println(
        "Already have lower bound for " + pred.name + ", index " + argIndex)
    } else {
      Console.err.println(
        "Computing lower bound for " + pred.name + ", index " + argIndex)

      withTimeout {
        testBound(pred, argIndex, -MaxBound, false)
      }

      withTimeout {
        while (!(lowerBounds contains ((pred, argIndex))) &&
                 getLowerTestValue(pred, argIndex).abs <= MaxBound)
          testBound(pred, argIndex, getLowerTestValue(pred, argIndex), false)
      }
    }

    if (upperBounds contains ((pred, argIndex))) {
      Console.err.println(
        "Already have upper bound for " + pred.name + ", index " + argIndex)
    } else {
      Console.err.println(
        "Computing upper bound for " + pred.name + ", index " + argIndex)

      withTimeout {
        testBound(pred, argIndex, MaxBound, true)
      }

      withTimeout {
        while (!(upperBounds contains ((pred, argIndex))) &&
                 getUpperTestValue(pred, argIndex).abs <= MaxBound)
          testBound(pred, argIndex, getUpperTestValue(pred, argIndex), true)
      }
    }
  }

  for (pred <- allPreds) {
    println("Predicate " + pred.name)
    for (n <- consideredArgs(pred)) {
      println("  Argument " + n + ": " +
                ((lowerBounds get ((pred, n))).toSeq.map(_ => "lower-bounded") ++
                   (upperBounds get ((pred, n))).toSeq.map(_ => "upper-bounded")).mkString(", "))
    }
  }
//  println("upperBounds",upperBounds)
//  println("lowerBounds",lowerBounds)

}
