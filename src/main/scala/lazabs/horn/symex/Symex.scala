/**
 * Copyright (c) 2022-2026 Zafer Esen, Philipp Ruemmer. All rights reserved.
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
package lazabs.horn.symex

import ap.api.SimpleAPI.ProverStatus
import ap.SimpleAPI
import ap.parser._
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction
import ap.theories.{Theory, TheoryCollector}
import lazabs.horn.bottomup.{NormClause, RelationSymbol}
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.Util.Dag
import lazabs.horn.preprocessor.HornPreprocessor.Solution

import collection.mutable.{HashSet => MHashSet, HashMap => MHashMap}

object Symex {
  private[symex] object AC extends ap.util.Debug.ASSERTION_CATEGORY
  class SymexException(msg: String) extends Exception(msg)
}

abstract class Symex[CC](iClauses:    Iterable[CC])(
    implicit clause2ConstraintClause: CC => ConstraintClause
) extends ConstraintSimplifier {

  import Symex._

  var printInfo = false
  def printInfo(s : => String, newLine : Boolean = true) : Unit = {
    if (printInfo)
      print(s + (if (newLine) "\n" else ""))
  }

  val theories: Seq[Theory] = {
    val coll = new TheoryCollector
    coll addTheory ap.types.TypeTheory
    for (c <- iClauses)
      c collectTheories coll
    coll.theories
  }

  if (theories.nonEmpty)
    printInfo("Theories: " + (theories mkString ", ") + "\n")

  val preds: Seq[Predicate] =
    (for (c   <- iClauses.iterator;
          lit <- (Iterator single c.head) ++ c.body.iterator;
          p = lit.predicate)
      yield p).toSeq.distinct

  // We keep a prover initialized with all the symbols running, which we will
  // use to check the satisfiability of constraints.
  // Note that the prover must be manually shut down for clean-up.
  implicit val prover: SimpleAPI = SimpleAPI.spawn
  prover.addTheories(theories)
  prover.addRelations(preds)

  // Keeps track of all the terms and adds new symbols to the prover
  // must be initialized after normClauses are generated.
  implicit val symex_sf: SymexSymbolFactory =
    new SymexSymbolFactory(theories, prover)

  val relationSymbols: Map[Predicate, RelationSymbol] =
    (for (p <- preds) yield (p -> RelationSymbol(p))).toMap

  // translate clauses to internal form
  val normClauses: Seq[(NormClause, CC)] = (
    for (c <- iClauses) yield {
      lazabs.GlobalParameters.get.timeoutChecker()
      (NormClause(c, p => relationSymbols(p)), c)
    }
  ).toSeq

  val normClauseToCC: Map[NormClause, CC] = normClauses.toMap

  val clausesWithRelationInBody: Map[RelationSymbol, Seq[NormClause]] =
    (for (rel <- relationSymbols.values) yield {
      (rel,
       normClauses.filter(_._1.body.exists(brel => brel._1 == rel)).map(_._1))
    }).toMap

  val clausesWithRelationInHead: Map[RelationSymbol, Seq[NormClause]] =
    (for (rel <- relationSymbols.values) yield {
      (rel, normClauses.filter(_._1.head._1 == rel).map(_._1))
    }).toMap

  val predicatesAndMaxOccurrences: Map[Predicate, Int] = {
    val maxOccs = new MHashMap[Predicate, Int]
    for (pred <- preds)
      maxOccs += ((pred, 0))
    for ((clause, _) <- normClauses) {
      for ((rs, occ) <- clause.body ++ Seq(clause.head))
        if (occ > maxOccs(rs.pred))
          maxOccs(rs.pred) = occ
    }
    maxOccs.toMap
  }

  // this must be done before we can use the symbol factory during resolution
  symex_sf.initialize(predicatesAndMaxOccurrences.toSet)

  def solve(): Either[Solution, Dag[(IAtom, CC)]]

  /**
   * Shut-down the engine.
   */
  def shutdown: Unit = {
    prover.shutDown
  }

  private[symex] def checkFeasibility(constraint : Conjunction,
                                      timeoutMs  : Option[Long])
    : ProverStatus.Value = {
    if (constraint.isTrue) {
      ProverStatus.Sat
    } else if (constraint.isFalse) {
      ProverStatus.Unsat
    } else prover.scope {
      prover.addAssertionPreproc(constraint)
      timeoutMs match {
        case Some(millis) =>
          prover.checkSat(block = false)
          prover.getStatus(millis) match {
            case ProverStatus.Running => prover.stop
            case status               => status
          }
        case None => prover.???
      }
    }
  }

  private[symex] def isSatisfiable(proverStatus: ProverStatus.Value)
    : Option[Boolean] =
    proverStatus match {
      case ProverStatus.Valid | ProverStatus.Sat     => Some(true)
      case ProverStatus.Invalid | ProverStatus.Unsat => Some(false)
      case _                                         => None
    }
}
