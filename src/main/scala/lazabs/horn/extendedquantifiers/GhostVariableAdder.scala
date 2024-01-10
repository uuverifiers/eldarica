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
package lazabs.horn.extendedquantifiers

import ap.parser._
import ap.types.SortedConstantTerm
import lazabs.horn.extendedquantifiers.Util.ExtendedQuantifierApp
import lazabs.horn.preprocessor.HornPreprocessor.VerificationHints
import lazabs.horn.preprocessor.HornPreprocessor
import InstrumentationOperator.GhostVar

import scala.collection.mutable.{
  ArrayBuffer,
  HashMap => MHashMap,
  HashSet => MHashSet
}

object GhostVariableAdder {
  type GhostVariableTerms = Seq[Map[GhostVar, ITerm]]
  type GhostVariableInds  = Seq[Map[GhostVar, Int]]
}

/**
 * Class to introduce ghost variables to predicates
 * Adds a set of ghost variables for each extended quantifier application.
 */
class GhostVariableAdder(
  exqApps                      : Seq[ExtendedQuantifierApp],
  exqToInstrumentationOperator : Map[ExtendedQuantifier, InstrumentationOperator],
  numGhostRanges               : Int) extends SimpleArgumentExpander {

  import GhostVariableAdder._
  import HornPreprocessor.Clauses
  import IExpression._

  val name = s"adding $numGhostRanges sets of ghost variables"

  private val ghostVarsInPred = new MHashMap[Predicate, Seq[ConstantTerm]]

//  /**
//   * In each `Predicate`, for each `ExtendedQuantifier`, we add `numGhostRanges`
//   * [[InstrumentationOperator.ghostVars]].
//   */
//  private val predToGhostTermsPerExtendedQuantifier =
//    new MHashMap[Predicate, Map[ExtendedQuantifier, GhostVariableTerms]]

  /**
   * A map from each extended quantifier application to another map from
   * predicates to ghost variable argument indices in that predicate.
   * We need indices, because the only thing that doesn't change across clauses
   * is the argument indices of a predicate (unlike terms).
   */
  private val exqAppToGhostVars =
    new MHashMap[ExtendedQuantifierApp, Map[Predicate, GhostVariableInds]]

  private val expandedPredicates = new MHashSet[Predicate]

  /**
   * Expansion happens for predicate arguments, in this case for the one at
   * `argNum`. Since we want to expand each predicate once, and we know
   * beforehand how we want to expand, we run this expansion once by adding
   * expanded predicates to the set `expandedPredicates`.
   */
  def expand(pred : Predicate, argNum : Int, sort : Sort)
  : Option[(Seq[(ITerm, Sort, String)], Option[ITerm])] = {
    val ghostVars: Seq[(ITerm, Sort, String)] =
      (for ((exqApp, exqAppId) <- exqApps zipWithIndex) yield {
        val baseName      = exqApp.exTheory.morphism.name
        val instOp        = exqToInstrumentationOperator(exqApp.exTheory)

        val ghostVariableInds : GhostVariableInds = {
          val numGhostVars    = instOp.ghostVars.size

          for (numGhostRange <- 0 until numGhostRanges) yield {
            val numNonGhostVars = argNum
            val numPrevGhostVarsFromSameExqApp = numGhostRange * numGhostVars
            val numPrevGhostVarsFromOtherExqApps =
              numGhostRanges * numGhostVars * exqAppId
            val rangeStartInd =
              numNonGhostVars + numPrevGhostVarsFromSameExqApp +
              numPrevGhostVarsFromOtherExqApps + 1
            val ghostVarToInd : Map[GhostVar, Int] =
              instOp.ghostVars.zipWithIndex.map{
                case (ghostVar, ghostInd) =>
                  ghostVar -> (rangeStartInd + ghostInd)}.toMap
            ghostVarToInd
          }
        }

        /**
         * There might be previously added ghost variables for this predicate
         * for other exqApps (within this loop), extend existing records.
         */
        val prevMap: Map[Predicate, GhostVariableInds] =
          exqAppToGhostVars.getOrElse(exqApp, Map())
        val newMap: Map[Predicate, GhostVariableInds] =
          Map(pred -> ghostVariableInds) ++ prevMap
        exqAppToGhostVars.put(exqApp, newMap)

        for (_ <- 0 until numGhostRanges;
             ghostVar <- instOp.ghostVars) yield {
          val ghostTermName = s"${baseName}_${ghostVar.name}"
          (IConstant(new SortedConstantTerm(ghostTermName, ghostVar.sort)),
            ghostVar.sort,
            ghostTermName)
        }
      }).flatten
    ghostVarsInPred.put(pred, ghostVars.map(_._1.asInstanceOf[IConstant].c))

    expandedPredicates += pred

    Some((ghostVars, None))
  }

  override def setup(clauses          : Clauses,
                     frozenPredicates : Set[Predicate]) : Unit = {}

  // ghost variables will be added to all predicates
  override def isExpandableSort(s : Sort, p : Predicate) : Boolean =
    !(expandedPredicates contains p)

  override def postprocessSolution(p: Predicate, f: IFormula): IFormula = {
    ghostVarsInPred get p match {
      case Some(ghostVars) =>
//        val newConjuncts = for ((exq, allGhostTerms) <- predToGhostTermsPerExtendedQuantifier(p);
//                                ghostTerms <- allGhostTerms) yield {
          // TODO: adapt solutions for the refactor
          ???
          // exq.morphism(ghostTerms.arr, ghostTerms.lo, ghostTerms.hi) === ghostTerms.res
          // todo: anything to do using alien terms?
//        }
//        val quanF = quanConsts(IExpression.Quantifier.EX,
//                               ghostVars,
//                               and(Seq(f) ++ newConjuncts))
//        quanF
      ???
      //(new Simplifier) (quanF)
      case None => f
    }
  }

  val predMapping = new MHashMap[Predicate, Predicate]

  def processAndGetGhostVarMap(clauses:          Clauses,
                               hints:            VerificationHints,
                               frozenPredicates: Set[Predicate])
    : (Clauses,
       VerificationHints,
       HornPreprocessor.BackTranslator,
       Map[ExtendedQuantifierApp, Map[Predicate, GhostVariableInds]]) = {
    val (newClauses, newHints, backTranslator) =
      super.process(clauses, hints, frozenPredicates)
    val oldNewPredMap = (for ((newC, oldC) <- newClauses zip clauses) yield {
      val oldNewPredMapping = ((oldC.body
        .map(_.pred) ++ Seq(oldC.head.pred)) zip
        (newC.body.map(_.pred) ++ Seq(newC.head.pred)))
      oldNewPredMapping
    }).flatten.toMap

    /**
     * Since we have new predicates (we added arguments for ghost variables),
     * we create a new map using the new predicates.
     */
    val ghostVarMap = for ((exqInfo, map) <- exqAppToGhostVars) yield {
      val newMap: Map[Predicate, GhostVariableInds] =
        for ((oldPred, ghostVars) <- map) yield {
          (oldNewPredMap(oldPred), ghostVars)
        }
      exqInfo -> newMap
    }
    (newClauses,
     newHints,
     backTranslator,
     ghostVarMap.toMap)
  }
}
