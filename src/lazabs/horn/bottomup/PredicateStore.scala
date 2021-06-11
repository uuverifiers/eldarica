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

import ap.PresburgerTools
import ap.parser._
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction

import scala.collection.mutable.ArrayBuffer

class PredicateStore[CC <% HornClauses.ConstraintClause]
                    (context : HornPredAbsContext[CC]) {

  import context._

  //////////////////////////////////////////////////////////////////////////////

  val predicates =
    (for (rs <- relationSymbols.values)
       yield (rs -> new ArrayBuffer[RelationSymbolPred])).toMap

  val predicateHashIndexes =
    (for (rs <- relationSymbols.values)
         yield (rs -> new ArrayBuffer[Stream[Int]])).toMap

  //////////////////////////////////////////////////////////////////////////////

  def addRelationSymbolPred(pred : RelationSymbolPred) : Unit = {
    assert(predicates(pred.rs).size == predicateHashIndexes(pred.rs).size &&
           pred.predIndex == predicates(pred.rs).size)

    predicates(pred.rs) +=
      pred
    predicateHashIndexes(pred.rs) +=
      (for (f <- pred.posInstances) yield (hasher addFormula f))
  }

  def addRelationSymbolPreds(preds : Seq[RelationSymbolPred]) : Unit =
    for (pred <- preds) addRelationSymbolPred(pred)

  def addHasherAssertions(clause : NormClause,
                          from : Seq[AbstractState]) = if (hasher.isActive) {
    hasher assertFormula clauseHashIndexes(clause)
    for ((state, (rs, occ)) <- from.iterator zip clause.body.iterator)
      for (pred <- state.preds) {
        val id = predicateHashIndexes(rs)(pred.predIndex)(occ)
        hasher assertFormula id
      }
  }

  def addPredicates(preds : Map[Predicate, Seq[IFormula]]) : Unit =
    for ((p, preds) <- preds) {
      val rs = relationSymbols(p)
      for ((f, predIndex) <- preds.iterator.zipWithIndex) {
        val intF = IExpression.subst(f, rs.argumentITerms.head.toList, 0)
        val (rawF, posF, negF) = rsPredsToInternal(intF)
        val pred = RelationSymbolPred(rawF, posF, negF, rs, predIndex)
        addRelationSymbolPred(pred)
      }
    }

  def elimQuansIfNecessary(c : Conjunction, positive : Boolean) : Conjunction =
    if (ap.terfor.conjunctions.IterativeClauseMatcher.isMatchableRec(
           if (positive) c else c.negate, Map())) {
      c
    } else {
      val newC = PresburgerTools.elimQuantifiersWithPreds(c)
      if (!ap.terfor.conjunctions.IterativeClauseMatcher.isMatchableRec(
              if (positive) newC else newC.negate, Map()))
        throw new Exception("Cannot handle general quantifiers in predicates at the moment")
      newC
    }

  def rsPredsToInternal(f : IFormula)
                     : (Conjunction, Conjunction, Conjunction) = {
    val rawF = sf.toInternalClausify(f)
    val posF = elimQuansIfNecessary(sf.preprocess(
                                      sf.toInternalClausify(~f)).negate, true)
    val negF = elimQuansIfNecessary(sf.preprocess(
                                      rawF), false)
    (rawF, posF, negF)
  }


}
