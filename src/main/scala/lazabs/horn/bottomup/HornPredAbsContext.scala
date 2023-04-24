/**
 * Copyright (c) 2011-2021 Philipp Ruemmer. All rights reserved.
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

import ap.parser._
import ap.proof.ModelSearchProver
import ap.proof.theoryPlugins.PluginSequence
import ap.proof.tree.SeededRandomDataSource
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.theories.{Theory, TheoryCollector}
import ap.types.TypeTheory
import ap.parameters.{Param, GoalSettings}
import ap.util.Timeout

import scala.collection.mutable.{LinkedHashMap, ArrayBuffer}
import scala.util.Random

trait HornPredAbsContext[CC] {

  val rand : Random

  val theories : Seq[Theory]
  val sf : SymbolFactory

  val useHashing : Boolean

  val normClauses : Seq[(NormClause, CC)]

  val relationSymbols : Map[Predicate, RelationSymbol]
  val relationSymbolOccurrences : Map[RelationSymbol, Vector[(NormClause, Int, Int)]]

  protected def computeRSOccurrences = {
    val relationSymbolOccurrences =
      (for (rs <- relationSymbols.values)
         yield (rs -> new ArrayBuffer[(NormClause, Int, Int)])).toMap
    for ((c@NormClause(_, body, _), _) <- normClauses.iterator;
         ((rs, occ), i) <- body.iterator.zipWithIndex) {
      relationSymbolOccurrences(rs) += ((c, occ, i))
    }
    relationSymbolOccurrences mapValues (_.toVector)
  }

  val relationSymbolBounds : Map[RelationSymbol, Conjunction]
  val relationSymbolReducers : Map[RelationSymbol, ReduceWithConjunction]

  val goalSettings : GoalSettings

  val emptyProver : ModelSearchProver.IncProver

  private var hardValidityCheckNum = 0
  private var hardValidityCheckThreshold = 27
  private var hardValidityCheckNumSqrt = 3

  def isValid(prover : ModelSearchProver.IncProver) : Boolean =
    prover.isObviouslyValid ||
    Timeout.withChecker(lazabs.GlobalParameters.get.timeoutChecker) {
      hardValidityCheckNum = hardValidityCheckNum + 1
      if (hardValidityCheckNum == hardValidityCheckThreshold) {
        hardValidityCheckNum = 0
        hardValidityCheckThreshold = hardValidityCheckThreshold + 2
        hardValidityCheckNumSqrt = hardValidityCheckNumSqrt + 1
      }

      if (hasher.acceptsModels && (rand nextInt hardValidityCheckNumSqrt) == 0)
        (prover checkValidity true) match {
          case Left(m) =>
            if (m.isFalse) {
              true
            } else {
              hasher addModel m
              false
            }
          case Right(_) =>
            throw new Exception("Unexpected prover result")
        }
      else
        !prover.isObviouslyUnprovable &&
         ((prover checkValidity false) match {
            case Left(m) if (m.isFalse) => true
            case Left(_) => false
            case Right(_) =>
              throw new Exception("Unexpected prover result")
          })
    }
  
  val hasher : IHasher

  protected def createHasher =
    if (useHashing)
      new Hasher(sf.order, sf.reducerSettings)
    else
      InactiveHasher

  val clauseHashIndexes : Map[NormClause, Int]

  protected def computeClauseHashIndexes =
    (for ((clause, _) <- normClauses.iterator)
     yield (clause, hasher addFormula clause.constraint)).toMap

}

class DelegatingHornPredAbsContext[CC](underlying : HornPredAbsContext[CC])
      extends HornPredAbsContext[CC] {
  val rand                      = underlying.rand
  val theories                  = underlying.theories
  val sf                        = underlying.sf
  val useHashing                = underlying.useHashing
  val normClauses               = underlying.normClauses
  val relationSymbols           = underlying.relationSymbols
  val relationSymbolOccurrences = underlying.relationSymbolOccurrences
  val relationSymbolBounds      = underlying.relationSymbolBounds
  val relationSymbolReducers    = underlying.relationSymbolReducers
  val goalSettings              = underlying.goalSettings
  val emptyProver               = underlying.emptyProver
  val hasher                    = underlying.hasher
  val clauseHashIndexes         = underlying.clauseHashIndexes
}

////////////////////////////////////////////////////////////////////////////////

class HornPredAbsContextImpl[CC <% HornClauses.ConstraintClause]
                            (iClauses : Iterable[CC],
                             intervalAnalysis : Boolean = true,
                             intervalAnalysisIgnoredSyms : Set[Predicate] = Set())
      extends HornPredAbsContext[CC] {

  import HornPredAbs._

  val rand = new Random (98762521)

  // first find out which theories are relevant
  val theories = {
    val coll = new TheoryCollector
    coll addTheory TypeTheory
    for (c <- iClauses)
      c collectTheories coll
    coll.theories
  }

  if (!theories.isEmpty)
    println("Theories: " + (theories mkString ", "))

  val plugins =
    for (t <- theories; p <- t.plugin.toSeq) yield p

  val useHashing =
    (theories forall {
       case ap.types.TypeTheory                 => true
       case ap.theories.GroebnerMultiplication  => true
       case ap.theories.ModuloArithmetic        => true
       case _ : ap.theories.ADT                 => true
       case _                                   => false
     }) &&
    (theories exists {
       case ap.theories.GroebnerMultiplication  => true
       case ap.theories.ModuloArithmetic        => true
       case adt : ap.theories.ADT               => adt.isEnum contains false
       case _                                   => false
     })

  if (useHashing)
    println("State hashing enabled")

  implicit val sf = new SymbolFactory(theories)

  val relationSymbols = {
    val preds =
      (for (c <- iClauses.iterator;
            lit <- (Iterator single c.head) ++ c.body.iterator;
            p = lit.predicate)
       yield p).toSet
    (for (p <- preds) yield (p -> RelationSymbol(p))).toMap
  }

  // make sure that arguments constants have been instantiated
  for (c <- iClauses) {
    val preds = for (lit <- c.head :: c.body.toList) yield lit.predicate
    for (p <- preds.distinct) {
      val rs = relationSymbols(p)
      for (i <- 0 until (preds count (_ == p)))
        rs arguments i
    }
  }

  // translate clauses to internal form
  val (normClauses, relationSymbolBounds) = {
    val rawNormClauses = new LinkedHashMap[NormClause, CC]

    for (c <- iClauses) {
      lazabs.GlobalParameters.get.timeoutChecker()
      rawNormClauses.put(NormClause(c, (p) => relationSymbols(p)), c)
    }

    if (intervalAnalysis) {
      val res = new LinkedHashMap[NormClause, CC]

      // We introduce lower-bound clauses for the symbols not to be
      // considered in interval analysis

      val additionalClauses =
        for (p <- intervalAnalysisIgnoredSyms)
        yield NormClause(Conjunction.TRUE, List(), (relationSymbols(p), 0))

      val propagator =
        new IntervalPropagator (rawNormClauses.keys.toIndexedSeq ++
                                  additionalClauses,
                                sf.reducerSettings)

      for ((nc, oc) <- propagator.result)
        if (!(additionalClauses contains oc))
          res.put(nc, rawNormClauses(oc))

      (res.toSeq, propagator.rsBounds)
    } else {
      val emptyBounds =
        (for (rs <- relationSymbols.valuesIterator)
         yield (rs -> Conjunction.TRUE)).toMap
      (rawNormClauses.toSeq, emptyBounds)
    }
  }

  val relationSymbolReducers =
    (for (rs <- relationSymbols.valuesIterator) yield {
      val bounds = relationSymbolBounds.getOrElse(rs, Conjunction.TRUE)
      (rs, sf reducer (if (bounds.isFalse) Conjunction.TRUE else bounds))
     }).toMap

  println("Unique satisfiable clauses: " + normClauses.size)

  for ((num, clauses) <-
        (normClauses groupBy { c => c._1.body.size }).toList sortBy (_._1))
    println("   " + clauses.size + " clauses with " + num + " body literals")

  val relationSymbolOccurrences = computeRSOccurrences

  val goalSettings = {
    var gs = GoalSettings.DEFAULT
//    gs = Param.CONSTRAINT_SIMPLIFIER.set(gs, determineSimplifier(settings))
//    gs = Param.SYMBOL_WEIGHTS.set(gs, SymbolWeights.normSymbolFrequencies(formulas, 1000))
//    gs = Param.PROOF_CONSTRUCTION.set(gs, constructProofs)
    gs = Param.GARBAGE_COLLECTED_FUNCTIONS.set(gs, sf.functionalPreds)
    gs = Param.FUNCTIONAL_PREDICATES.set(gs, sf.functionalPreds)
//    gs = Param.PREDICATE_MATCH_CONFIG.set(gs, signature.predicateMatchConfig)
    gs = Param.THEORY_PLUGIN.set(gs, PluginSequence(plugins))
    gs = Param.REDUCER_SETTINGS.set(gs, sf.reducerSettings)
    gs = Param.RANDOM_DATA_SOURCE.set(gs, new SeededRandomDataSource(12354))
    gs
  }

  val emptyProver = {
    val order = sf.order restrict Set()
    var prover = ModelSearchProver emptyIncProver goalSettings
    for (t <- theories)
      prover = prover.assert(Conjunction.conj(t.axioms, order), order)
    prover
  }

  //////////////////////////////////////////////////////////////////////////////

  // Hashing/sampling to speed up implication checks

  val hasher = createHasher

  // Add clause constraints to hasher

  val clauseHashIndexes = computeClauseHashIndexes

}
