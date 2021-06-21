/**
 * Copyright (c) 2021 Philipp Ruemmer. All rights reserved.
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
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction

import Util._
import DisjInterpolator.{AndOrNode, AndNode, OrNode}

import scala.collection.mutable.ArrayBuffer

class PredicateMiner[CC <% HornClauses.ConstraintClause]
                    (predAbs : HornPredAbs[CC]) {

  import predAbs.{context, predStore}

  val allPredicates =
    for ((rs, preds) <- predStore.predicates.toIndexedSeq;
         pred <- preds.toIndexedSeq)
    yield pred

  def printPreds(preds : Seq[RelationSymbolPred]) : Unit = {
    val rses = preds.map(_.rs).distinct.sortBy(_.name)
    for (rs <- rses) {
      println("" + rs + ":")
      for (pred <- preds)
        if (pred.rs == rs)
          println("\t" + pred)
    }
  }

  {
    println("All predicates (" + allPredicates.size + "):")
    printPreds(allPredicates)
    println
    val minSet = minimizePredSet(allPredicates)
    println("Minimal predicate set (" + minSet.size + "):")
    printPreds(minSet)
    println
    val necSet = necessaryPredicates(allPredicates)
    println("Necessary predicates (" + necSet.size + "):")
    printPreds(necSet)
  }

  /**
   * Find a minimal sub-set of the given predicates that is sufficient
   * to show satisfiability of the problem. The method will try to
   * remove the first predicates in the sequence first.
   */
  def minimizePredSet(preds : Seq[RelationSymbolPred])
                    : Seq[RelationSymbolPred] = {
    var curPredicates = preds.toSet

    for (pred <- preds) {
      val testPreds = curPredicates - pred
      if (isSufficient(testPreds))
        curPredicates = testPreds
    }

    preds filter curPredicates
  }

  /**
   * Find the predicates within the given set of predicates that are
   * elements of every minimal sufficient set of predicates.
   */
  def necessaryPredicates(preds : Seq[RelationSymbolPred])
                        : Seq[RelationSymbolPred] = {
    val result = new ArrayBuffer[RelationSymbolPred]
    val allPreds = preds.toSet

    for (pred <- preds) {
      if (!isSufficient(allPreds - pred))
        result += pred
    }

    result.toSeq
  }

  /**
   * Check whether the given set of predicates is sufficient to show
   * satisfiability of the problem.
   */
  def isSufficient(preds : Iterable[RelationSymbolPred]) : Boolean = {
    val newPredStore = new PredicateStore(context)
    newPredStore addRelationSymbolPreds preds
    try {
      Console.withOut(HornWrapper.NullStream) {
        new CEGAR (context, newPredStore, exceptionalPredGen)
      }
      true
    } catch {
      case PredGenException => {
        false
      }
    }
  }

  private object PredGenException extends Exception

  private def exceptionalPredGen(d : Dag[AndOrNode[NormClause, Unit]]) 
                               : Either[Seq[(Predicate, Seq[Conjunction])],
                                        Dag[(IAtom, NormClause)]] =
   throw PredGenException

}
