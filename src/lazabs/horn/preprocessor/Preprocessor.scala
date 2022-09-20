/**
 * Copyright (c) 2016-2022 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.preprocessor

import ap.parser._
import IExpression._

import lazabs.horn.bottomup.HornClauses
import lazabs.horn.global._
import lazabs.horn.bottomup.Util.{Dag, DagNode, DagEmpty}
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

object HornPreprocessor {

  type Solution          = Map[Predicate, IFormula]
  type CounterExample    = Dag[(IAtom, HornClauses.Clause)]
  type Clauses           = Seq[HornClauses.Clause]
  type VerificationHints = lazabs.horn.abstractions.VerificationHints

  import lazabs.horn.abstractions.VerificationHints._

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Simplify a counterexample by merging multiple occurrences of the
   * same state.
   */
  def simplify(cex : CounterExample) : CounterExample = {
    val seenStates = new MHashMap[IAtom, Int]

    def simplifyHelp(depth : Int, dag : CounterExample)
                    : (CounterExample, List[Int]) = dag match {
      case DagNode(pair@(atom, clause), children, next) => {
        val (newNext, shifts) = simplifyHelp(depth + 1, next)
        val newChildren = for (c <- children) yield (c + shifts(c - 1))
        val newShifts = (seenStates get atom) match {
          case None => {
            seenStates.put(atom, depth)
            0 :: shifts
          }
          case Some(d) =>
            (d - depth) :: shifts
        }
        (DagNode(pair, newChildren, newNext), newShifts)
      }
      case DagEmpty =>
        (DagEmpty, List())
    }

    simplifyHelp(0, cex)._1.elimUnconnectedNodes
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Verify that all atoms in the clause have arguments of correct sorts.
   */
  def typeCheck(clause : HornClauses.Clause) : Unit =
    for (a <- List(clause.head) ++ clause.body)
      typeCheck(a)

  /**
   * Verify that all atoms in all clauses have arguments of correct sorts.
   */
  def typeCheck(clauses : Iterable[HornClauses.Clause]) : Unit =
    for (clause <- clauses)
      typeCheck(clause)

  /**
   * Verify that all terms in a counterexample have correct sorts.
   */
  def typeCheck(cex : CounterExample) : Unit =
    for (p <- cex) typeCheck(p._1)

  /**
   * Verify that all arguments have correct sorts.
   */
  def typeCheck(a : IAtom) : Unit = {
    val sorts = predArgumentSorts(a.pred)
    for (((t, s), n) <- (a.args.iterator zip sorts.iterator).zipWithIndex)
      (Sort sortOf t, s) match {
        case (Sort.Numeric(_), Sort.Numeric(_)) => // ok
        case (Sort.AnyBool(_), Sort.AnyBool(_)) => // ok
        case (s2, s) if s2 != s =>
          throw new Exception("Argument " + n + " of " + a.pred +
                                " should have sort " + s + " but is " + t +
                                " of sort " + s2)
        case _ => // ok
      }
  }

  /////////////////////////////////////////////////////////////////////////////

  object NameFactory {
    def predNameFactory(clauses : Seq[HornClauses.Clause]) : NameFactory = {
      val preds = HornClauses allPredicates clauses
      new NameFactory(preds map (_.name))
    }
  }

  /**
   * Class to generate new, unique names of symbols.
   */
  class NameFactory(existingNames : Iterable[String]) {
    private val allNames = new MHashSet[String]
    allNames ++= existingNames

    private var cnt = 0

    def newName(base : String) : String = {
      val res = base + "_" + cnt
      cnt = cnt + 1
      if (allNames contains res) {
        newName(base)
      } else {
        allNames += res
        res
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Class for back-translating solutions of Horn constraints,
   * undoing any simplification that was done upfront.
   */
  abstract class BackTranslator {
    def translate(solution : Solution) : Solution
    def translate(cex : CounterExample) : CounterExample

    def translate(result : Either[Solution, CounterExample])
                 : Either[Solution, CounterExample] =
      result match {
        case Left(sol) => Left(translate(sol))
        case Right(cex) => Right(translate(cex))
      }
  }

  abstract class ExtendingBackTranslator(parent : BackTranslator)
           extends BackTranslator {
    def preTranslate(solution : Solution) : Solution
    def preTranslate(cex : CounterExample) : CounterExample

    def translate(solution : Solution) =
      parent.translate(preTranslate(solution))
    def translate(cex : CounterExample) =
      parent.translate(preTranslate(cex))
  }

  class ComposedBackTranslator(translators : Seq[BackTranslator])
        extends BackTranslator {
    def translate(solution : Solution) =
      (solution /: translators) { case (sol, t) => t translate sol }
    def translate(cex : CounterExample) = {
      if (lazabs.Main.assertions)
        typeCheck(cex)
      (cex /: translators) {
        case (cex, t) => {
          val newCEX = t translate cex
          if (lazabs.Main.assertions)
            typeCheck(newCEX)
          newCEX
        }
      }
    }
  }

  val IDENTITY_TRANSLATOR = new BackTranslator {
    def translate(solution : Solution) = solution
    def translate(cex : CounterExample) = cex
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Processors for upfront simplification of Horn clauses.
 */
trait HornPreprocessor {
  import HornPreprocessor._

  val name : String

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) =
    process(clauses, hints, Set())

  def process(clauses : Clauses, hints : VerificationHints,
              frozenPredicates : Set[Predicate])
             : (Clauses, VerificationHints, BackTranslator)

  def isApplicable(clauses : Clauses,
                   frozenPredicates : Set[Predicate]) : Boolean = true

}
