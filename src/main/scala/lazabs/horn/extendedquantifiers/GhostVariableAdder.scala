/**
 * Copyright (c) 2022 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
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
import lazabs.horn.extendedquantifiers.Util.ExtendedQuantifierInfo
import lazabs.horn.preprocessor.HornPreprocessor.VerificationHints
import lazabs.horn.preprocessor.HornPreprocessor

import scala.collection.mutable.{
  ArrayBuffer,
  HashMap => MHashMap,
  HashSet => MHashSet
}

object GhostVariableAdder {
  case class AlienGhostVariableInds(v:      Int, vSet: Int)
  case class AlienGhostVariableTerms(v:     ITerm, vSet: ITerm)
  case class GhostVariableInds(lo:          Int,
                               hi:          Int,
                               res:         Int,
                               arr:         Int,
                               alienInds:   Seq[AlienGhostVariableInds])
  case class GhostVariableTerms(lo:         ITerm,
                                hi:         ITerm,
                                res:        ITerm,
                                arr:        ITerm,
                                alienTerms: Seq[AlienGhostVariableTerms])
}

/**
 * Class to introduce ghost variables to predicates
 * Adds a set of ghost variables for each extended quantifier.
 */
class GhostVariableAdder(extendedQuantifierInfos: Seq[ExtendedQuantifierInfo],
                         numGhostRanges:          Int)
    extends SimpleArgumentExpander {

  import GhostVariableAdder._
  import HornPreprocessor.Clauses
  import IExpression._

  val name = "adding " + numGhostRanges + " sets of ghost variables"

  private val ghostVarsInPred = new MHashMap[Predicate, Seq[ConstantTerm]]
  private val ghostVarInfosInPred =
    new MHashMap[Predicate, Map[ExtendedQuantifier, Seq[GhostVariableTerms]]]

  // these are used to propagate information about alien vars to later stages
  // can probably be done in a much cleaner way!
  private val alienVarToPredVar = new MHashMap[ITerm, ITerm]
  private val alienVarToOldPred = new MHashMap[ITerm, Predicate]
  private val alienVarToPredInd = new MHashMap[ITerm, Int]

  // a map from each extended quantifier to another map that is a map from
  // predicates to a sequence of ghost variable argument indices in that predicate
  private val extQuantifierToGhostVars =
    new MHashMap[ExtendedQuantifierInfo, Map[Predicate, Seq[GhostVariableInds]]]

  private val expandedPredicates = new MHashSet[Predicate]

  def expand(
      pred:   Predicate,
      argNum: Int,
      sort:   Sort): Option[(Seq[(ITerm, Sort, String)], Option[ITerm])] = {

    var offset = argNum
    val ghostVars: Seq[(ITerm, Sort, String)] =
      (for ((info, infoId) <- extendedQuantifierInfos zipWithIndex) yield {
        val baseName      = info.exTheory.fun.name
        val loName        = baseName + "_lo"
        val hiName        = baseName + "_hi"
        val resName       = baseName + "_res"
        val shadowArrName = baseName + "_arr"
        val arrayTheory   = info.exTheory.arrayTheory
        val indexSort     = arrayTheory.indexSorts.head

        val alienIndsToTerms = new MHashMap[Int, (IConstant, Sort, String)]

        val ghostVariableInds: Seq[GhostVariableInds] = {
          val numGhostVars            = 4
          val numGhostVarsPerAlienVar = 2
          val numAlienGhostVars =
            info.exTheory.alienConstantsInPredicate.length * numGhostVarsPerAlienVar

          val numAllGhostVars = numGhostVars + numAlienGhostVars // todo: refactor
          val arrayInds = for (numGhostRange <- 0 until numGhostRanges) yield {
            val shift = offset + numGhostRange * numAllGhostVars + numGhostRanges * numAllGhostVars * infoId
            val alienGhostVarInds =
              for ((c, i) <- info.exTheory.alienConstantsInPredicate zipWithIndex)
                yield {
                  val alienVarShift   = shift + numGhostVars + i * numGhostVarsPerAlienVar
                  val (vInd, vSetInd) = (alienVarShift + 1, alienVarShift + 2)
                  val sort            = ap.types.SortedConstantTerm.sortOf(c)
                  val name            = c.name + "_shad" // do not change this!
                  val vTerm =
                    (IConstant(new SortedConstantTerm(name + "_" + vInd, sort)),
                     sort,
                     name)
                  val vSetTerm =
                    (IConstant(
                       new SortedConstantTerm(name + "_set_" + vInd,
                                              Sort.Bool)),
                     Sort.Bool,
                     name + "_set")
                  alienIndsToTerms += (vInd      -> vTerm)
                  alienIndsToTerms += (vSetInd   -> vSetTerm)
                  alienVarToPredVar += (vTerm._1 -> IConstant(c))
                  alienVarToOldPred += (vTerm._1 -> pred)
                  alienVarToPredInd += (vTerm._1 -> vInd)
                  AlienGhostVariableInds(v = vInd, vSet = vSetInd)
                }
            GhostVariableInds(shift + 1,
                              shift + 2,
                              shift + 3,
                              shift + 4,
                              alienGhostVarInds)
          }
          arrayInds
        }

        val prevMap: Map[Predicate, Seq[GhostVariableInds]] =
          extQuantifierToGhostVars.getOrElse(info, Map())
        val newMap: Map[Predicate, Seq[GhostVariableInds]] =
          Map(pred -> ghostVariableInds) ++ prevMap
        extQuantifierToGhostVars.put(info, newMap)

        val resultSort = info.exTheory.predicate match {
          case Some(_) => ap.types.Sort.Bool
          case None    => arrayTheory.objSort
        }

        (for (ghostVarInds <- ghostVariableInds) yield {
          val loTerm =
            new SortedConstantTerm(loName + ghostVarInds.lo, indexSort)
          val hiTerm =
            new SortedConstantTerm(hiName + ghostVarInds.hi, indexSort)
          val resTerm =
            new SortedConstantTerm(resName + ghostVarInds.res, resultSort)
          val shadowArrTerm = new SortedConstantTerm(shadowArrName +
                                                       ghostVarInds.arr,
                                                     arrayTheory.sort)
          val regularGhostVars: Seq[(ITerm, Sort, String)] = Seq(
            (IConstant(loTerm), indexSort, loName),
            (IConstant(hiTerm), indexSort, hiName),
            (IConstant(resTerm), resultSort, resName),
            (IConstant(shadowArrTerm), arrayTheory.sort, shadowArrName)
          )
          val alienGhostVariableTerms = new ArrayBuffer[AlienGhostVariableTerms]
          val alienGhostVars: Seq[(ITerm, Sort, String)] = {
            (for (alienVarInds <- ghostVarInds.alienInds) yield {
              val vTerm    = alienIndsToTerms(alienVarInds.v)
              val vSetTerm = alienIndsToTerms(alienVarInds.vSet)
              alienGhostVariableTerms += AlienGhostVariableTerms(v = vTerm._1,
                                                                 vSet =
                                                                   vSetTerm._1)
              Seq(vTerm, vSetTerm)
            }).flatten
          }

          val newGhostVarTerms = Seq(
            GhostVariableTerms(lo = loTerm,
                               hi = hiTerm,
                               res = resTerm,
                               arr = shadowArrTerm,
                               alienTerms = alienGhostVariableTerms))
          val oldMap: Map[ExtendedQuantifier, Seq[GhostVariableTerms]] =
            ghostVarInfosInPred.getOrElse(pred, Map(info.exTheory -> Nil))
          val combinedGhostVarTerms: Seq[GhostVariableTerms] = oldMap(
            info.exTheory) ++ newGhostVarTerms
          val newMap = oldMap ++ Map(info.exTheory -> combinedGhostVarTerms)
          ghostVarInfosInPred += (pred -> newMap)
          regularGhostVars ++ alienGhostVars
        }).flatten
      }).flatten
    ghostVarsInPred.put(pred, ghostVars.map(_._1.asInstanceOf[IConstant].c))

    expandedPredicates += pred
    offset += ghostVars.length

    Some((ghostVars, None))
  }

  override def setup(clauses:          Clauses,
                     frozenPredicates: Set[Predicate]): Unit = {}

  // ghost variables will be added to all predicates
  override def isExpandableSort(s: Sort, p: Predicate): Boolean =
    !(expandedPredicates contains p)

  override def postprocessSolution(p: Predicate, f: IFormula): IFormula = {
    ghostVarsInPred get p match {
      case Some(ghostVars) =>
        val newConjuncts = for ((exq, allGhostTerms) <- ghostVarInfosInPred(p);
                                ghostTerms <- allGhostTerms) yield {
          exq.fun(ghostTerms.arr, ghostTerms.lo, ghostTerms.hi) === ghostTerms.res
          // todo: anything to do using alien terms?
        }
        val quanF = quanConsts(IExpression.Quantifier.EX,
                               ghostVars,
                               and(Seq(f) ++ newConjuncts))
        quanF
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
       Map[ExtendedQuantifierInfo, Map[Predicate, Seq[GhostVariableInds]]],
       Map[ITerm, ITerm]) = { // last argument is a map from added alien vars back to the terms they represent
    val (newClauses, newHints, backTranslator) =
      super.process(clauses, hints, frozenPredicates)
    val oldNewPredMap = (for ((newC, oldC) <- newClauses zip clauses) yield {
      val oldNewPredMapping = ((oldC.body
        .map(_.pred) ++ Seq(oldC.head.pred)) zip
        (newC.body.map(_.pred) ++ Seq(newC.head.pred)))
      oldNewPredMapping
    }).flatten.toMap

    val ghostVarMap = for ((exqInfo, map) <- extQuantifierToGhostVars) yield {
      val newMap: Map[Predicate, Seq[GhostVariableInds]] =
        for ((oldPred, ghostVars) <- map) yield {
          (oldNewPredMap(oldPred), ghostVars)
        }

      val alienVars = alienVarToPredVar.keys
      val allAtoms: Map[Predicate, Seq[IAtom]] =
        newClauses.flatMap(_.allAtoms).groupBy(_.pred)

      val newPairs = (for (alienVar <- alienVars) yield {
        val atomsWithSamePredAndGhostVar = allAtoms(
          oldNewPredMap(alienVarToOldPred(alienVar)))
        for (atom <- atomsWithSamePredAndGhostVar) yield {
          (atom.args(alienVarToPredInd(alienVar)) -> alienVarToPredVar(
            alienVar))
        }
      }).flatten

      newPairs.foreach {
        case (a, b) => alienVarToPredVar += (a -> b)
      }

      ////      val newExqInfo =
      ////        ExtendedQuantifierInfo(exqInfo.exTheory, exqInfo.funApp,
      ////          exqInfo.arrayTerm, exqInfo.loTerm, exqInfo.hiTerm,
      ////          exqInfo.bodyPreds.map(pred => oldNewPredMap(pred)))
      (exqInfo, newMap)
    }
    (newClauses,
     newHints,
     backTranslator,
     ghostVarMap.toMap,
     alienVarToPredVar.toMap)
  }
}
