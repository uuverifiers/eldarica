package lazabs.horn.extendedquantifiers

import ap.parser._
import ap.types.SortedConstantTerm
import lazabs.horn.extendedquantifiers.Util.ExtendedQuantifierInfo
import lazabs.horn.preprocessor.HornPreprocessor.VerificationHints
import lazabs.horn.preprocessor.{ArgumentExpander, HornPreprocessor}

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}

object GhostVariableAdder {
  case class GhostVariableInds (lo  : Int,
                                hi  : Int,
                                res : Int,
                                arr : Int)
  case class GhostVariableTerms (lo  : ITerm,
                                 hi  : ITerm,
                                 res : ITerm,
                                 arr : ITerm)
}

/**
 * Class to introduce ghost variables to predicates
 * Adds a set of ghost variables for each extended quantifier.
 */
class GhostVariableAdder(extendedQuantifierInfos : Seq[ExtendedQuantifierInfo])
  extends ArgumentExpander {

  import GhostVariableAdder._
  import HornPreprocessor.Clauses
  import IExpression._

  val name = "ghost variable adder"

  private val ghostVarsInPred = new MHashMap[Predicate, Seq[ConstantTerm]]

  // a map from each extended quantifier to another map that is a map from
  // predicates to a sequence of ghost variable argument indices in that predicate
  private val extQuantifierToGhostVars =
  new MHashMap[ExtendedQuantifierInfo, Map[Predicate, Seq[GhostVariableInds]]]

  private val expandedPredicates = new MHashSet[Predicate]

  def expand(pred: Predicate, argNum: Int, sort: Sort)
  : Option[(Seq[(ITerm, Sort, String)], Option[ITerm])] = {

    var offset = argNum
    val ghostVars : Seq[(ITerm, Sort, String)] =
      (for (info <- extendedQuantifierInfos) yield {
      val baseName = info.exTheory.fun.name // todo: support sets of ghost vars
      val loName  = baseName + "_lo"
      val hiName  = baseName + "_hi"
      val resName = baseName + "_res"
      val shadowArrName = baseName + "_arr"
      val arrayTheory = info.exTheory.arrayTheory
      val indexSort = arrayTheory.indexSorts.head

      val ghostVariableInds =
        GhostVariableInds(offset+1, offset+2, offset+3, offset+4)
      val prevMap : Map[Predicate, Seq[GhostVariableInds]] =
        extQuantifierToGhostVars.getOrElse(info, Map())
      val newMap : Map[Predicate, Seq[GhostVariableInds]] =
        Map(pred -> Seq(ghostVariableInds)) ++ prevMap
      extQuantifierToGhostVars.put(info, newMap)

      Seq(
        (IConstant(new SortedConstantTerm(loName, indexSort)), indexSort, loName),
        (IConstant(new SortedConstantTerm(hiName, indexSort)), indexSort, hiName),
        (IConstant(new SortedConstantTerm(resName, arrayTheory.objSort)), arrayTheory.objSort, resName),
        (IConstant(new SortedConstantTerm(shadowArrName, arrayTheory.sort)), arrayTheory.sort, shadowArrName))
    }).flatten

    ghostVarsInPred.put(pred, ghostVars.map(_._1.asInstanceOf[IConstant].c))

    expandedPredicates += pred
    offset += ghostVars.length

    Some((ghostVars, None))
  }

  override def setup(clauses: Clauses,
                     frozenPredicates : Set[Predicate]): Unit = {
  }

  // ghost variables will be added to all predicates
  override def isExpandableSort(s : Sort, p : Predicate): Boolean =
    !(expandedPredicates contains p)

  override def postprocessSolution(p : Predicate, f : IFormula) : IFormula = {
    ghostVarsInPred get p match {
      case Some(ghostVars) =>
        val quanF = quanConsts(IExpression.Quantifier.EX, ghostVars, f)
        (new Simplifier) (quanF)
      case None => f
    }
  }

  val predMapping = new MHashMap[Predicate, Predicate]

  def processAndGetGhostVarMap(clauses: Clauses,
              hints: VerificationHints,
              frozenPredicates: Set[Predicate]):
  (Clauses, VerificationHints, HornPreprocessor.BackTranslator,
    Map[ExtendedQuantifierInfo, Map[Predicate, Seq[GhostVariableInds]]]) = {
    val (newClauses, newHints, newFrozenPredicates) =
      super.process(clauses, hints, frozenPredicates)
    val oldNewPredMap = (for ((newC, oldC) <- newClauses zip clauses) yield {
      val oldNewPredMapping = ((oldC.body.map(_.pred) ++ Seq(oldC.head.pred)) zip
        (newC.body.map(_.pred) ++ Seq(newC.head.pred)))
      oldNewPredMapping
    }).flatten.toMap

    val ghostVarMap = for ((exqInfo, map) <- extQuantifierToGhostVars) yield {
      val newMap : Map[Predicate, Seq[GhostVariableInds]] =
        for((oldPred, ghostVars) <- map) yield {
          (oldNewPredMap(oldPred), ghostVars)
        }
      (exqInfo, newMap)
    }

    (newClauses, newHints, newFrozenPredicates, ghostVarMap.toMap)
  }

}
