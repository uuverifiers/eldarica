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
import lazabs.horn.abstractions.{VerificationHints, EmptyVerificationHints,
                                 AbsReader}
import VerificationHints._
import lazabs.horn.concurrency.ReaderMain

import lattopt._

import scala.collection.mutable.{ArrayBuffer, LinkedHashSet, LinkedHashMap,
                                 HashMap => MHashMap}

object PredicateMiner {
  object TemplateExtraction extends Enumeration {
    val Variables = Value
  }
}

/**
 * A class to analyse the predicates generated during a CEGAR run.
 */
class PredicateMiner[CC <% HornClauses.ConstraintClause]
                    (predAbs : HornPredAbs[CC]) {

  import PredicateMiner._
  import predAbs.{context, predStore}

  /**
   * All predicates that have been considered by CEGAR.
   */
  val allPredicates =
    for ((rs, preds) <- predStore.predicates.toIndexedSeq;
         pred <- preds.toIndexedSeq)
    yield pred

  /**
   * A lattice representing all sufficient subsets of predicates.
   */
  val predicateLattice =
    CachedFilteredLattice(PowerSetLattice.inverted(allPredicates),
                          isSufficient)

  def printPreds(preds : Seq[RelationSymbolPred]) : Unit = {
    val rses = preds.map(_.rs).distinct.sortBy(_.name)
    for (rs <- rses) {
      println("" + rs + ":")
      for (pred <- preds)
        if (pred.rs == rs)
          println("\t" + pred)
    }
  }

  private implicit val randomData = new SeededRandomDataSource(123)

  /**
   * An arbitrary minimal sufficient set of predicates.
   */
  lazy val minimalPredicateSet =
    allPredicates filter predicateLattice.getLabel(
      Algorithms.maximize(predicateLattice)(predicateLattice.bottom))

  /**
   * The necessary predicates: predicates which are contained in each
   * minimal sufficient set.
   */
  lazy val necessaryPredicates = necessaryPredicates2Help

  /**
   * The non-redundant predicates: the union of all minimal sufficient
   * predicate sets.
   */
  lazy val nonRedundantPredicates =
    allPredicates filter predicateLattice.getLabel(
      Algorithms.maximalFeasibleObjectMeet(predicateLattice)(predicateLattice.bottom))

  //////////////////////////////////////////////////////////////////////////////

  {
    implicit val randomData = new SeededRandomDataSource(123)
    val pl = predicateLattice

    println("All predicates (" + allPredicates.size + "):")
    printPreds(allPredicates)

    println
    println("Minimal predicate set (" + minimalPredicateSet.size + "):")
    printPreds(minimalPredicateSet)

    println
    println("Necessary predicates, contained in all minimal sufficient sets (" +
              necessaryPredicates.size + "):")
    printPreds(necessaryPredicates)

    println
    println("Non-redundant predicates, contained in some minimal sufficient set (" +
              nonRedundantPredicates.size + "):")
    printPreds(nonRedundantPredicates)

    println
    ReaderMain.printHints(
      extractTemplates(allPredicates, TemplateExtraction.Variables, 0))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Find a minimal sub-set of the given predicates that is sufficient
   * to show satisfiability of the problem. The method will try to
   * remove the first predicates in the sequence first.
   */
  protected def minimizePredSet(preds : Seq[RelationSymbolPred])
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
  protected def necessaryPredicatesHelp(preds : Seq[RelationSymbolPred])
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
   * Find the predicates that are elements of every minimal sufficient
   * set of predicates.
   * 
   * This method will use the predicate lattice for the computation.
   */
  protected def necessaryPredicates2Help : Seq[RelationSymbolPred] = {
    val result = new ArrayBuffer[RelationSymbolPred]

    for (pred <- allPredicates) {
      val obj = (for (x <- predicateLattice succ predicateLattice.bottom;
                      if !(predicateLattice.getLabel(x) contains pred))
                 yield x).next
      if (!predicateLattice.isFeasible(obj))
        result += pred
    }

    result.toSeq
  }

  /**
   * Check whether the given set of predicates is sufficient to show
   * satisfiability of the problem.
   */
  def isSufficient(preds : Iterable[RelationSymbolPred]) : Boolean = {
    print(".")
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

  //////////////////////////////////////////////////////////////////////////////

  def extractTemplates(preds : Iterable[RelationSymbolPred],
                       mode : TemplateExtraction.Value,
                       baseCost : Int)
                     : VerificationHints =
    VerificationHints.union(
      preds map { p => extractTemplates(p, mode, baseCost) })

  def extractTemplates(pred : RelationSymbolPred,
                       mode : TemplateExtraction.Value,
                       baseCost : Int)
                     : VerificationHints = {
    import IExpression._

    mode match {
      case TemplateExtraction.Variables => {
        val rs =
          pred.rs
        val symMap =
          (for ((c, n) <- rs.arguments.head.iterator.zipWithIndex)
           yield (c -> v(n, Sort sortOf c))).toMap

        val res = new LinkedHashSet[VerifHintElement]

        def extractVars(c : Conjunction, polarity : Int) : Unit = {
          val ac = c.arithConj

          for (lc <- ac.positiveEqs; c <- lc.constants)
            res += VerifHintTplEqTerm(symMap(c), baseCost + 1)

          for (lc <- ac.inEqs.iterator;
               (coeff, c : ConstantTerm) <- lc.iterator) {
            val t = symMap(c) *** (coeff.signum * polarity)
            res += VerifHintTplInEqTerm(t, baseCost)
          }

          for (d <- c.negatedConjs) extractVars(d, -polarity)
        }

        extractVars(pred.posInstances.head, 1)

        VerificationHints(Map(rs.pred -> res.toSeq))
      }
    }
  }

  /*
   Unfinished code for merging templates

  def mergePosNegTemplates(hints : LinkedHashSet[VerifHintElement]) : Unit = {
    val boundedTerms = new MHashMap[ITerm]
    for (el <- hints) el match {
      case VerifHintTplInEqTerm(ITimes(IdealInt.MINUS_ONE, t), _) =>
        boundedTerms += t
      case VerifHintTplInEqTerm(t, _) =>
        boundedTerms += t
      case _ =>
        // nothing
    }
  }

  def mergeTemplates(hints : VerificationHints) : VerificationHints = {
    val newPredHints =
      for ((pred, els) hints.predicateHints) yield {

      }
  }
   */

}
