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
import ap.parser.IExpression.ConstantTerm
import ap.parser._
import ap.terfor._
import ap.util.Debug
import ap.terfor.conjunctions.Conjunction
import ap.terfor.substitutions.ConstantSubst
import lazabs.horn.bottomup.{HornClauses, NormClause, RelationSymbol}
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.Util.{Dag, DagEmpty, DagNode}
import lazabs.horn.preprocessor.HornPreprocessor.Solution
import Symex.FeasibilityCheckResult

import collection.mutable.{HashMap => MHashMap}

/**
 * Base class of the forward engines: unit hyper-resolution from the facts
 * towards FALSE, with the derived unit clauses kept in a [[UnitClauseDB]].
 */
abstract class ForwardSymex[CC](iClauses : Iterable[CC])(
    implicit clause2ConstraintClause : CC => ConstraintClause)
    extends Symex(iClauses) {

  private val normClausesConvertedToUnitClauses =
    new MHashMap[NormClause, UnitClause]

  val (facts: Seq[UnitClause], factToNormClause: Map[UnitClause, NormClause]) = {
    val (facts, factToNormClause) =
      (for ((normClause, _) <- normClauses
            if normClause.body.isEmpty && normClause.head._1.pred != HornClauses.FALSE)
        yield {
          val cuc = toUnitClause(normClause)
          (cuc, (cuc, normClause))
        }).unzip
    (facts.distinct, factToNormClause.toMap)
  }

  val (goals: Seq[UnitClause], goalToNormClause: Map[UnitClause, NormClause]) = {
    val (goals, goalToNormClause) =
      (for ((normClause, _) <- normClauses
            if normClause.head._1.pred == HornClauses.FALSE && normClause.body.length == 1)
        yield {
          val cuc = toUnitClause(normClause)
          (cuc, (cuc, normClause))
        }).unzip
    (goals, goalToNormClause.toMap)
  }

  /**
   * Applies hyper-resolution using nucleus and electrons and returns the
   * resulting unit clause.
   * @note This implementation only infers positive CUCs.
   * @note "FALSE :- constraint" is considered a unit clause.
   * @todo Move out of this class.
   */
  protected def hyperResolve(nucleus:   NormClause,
                           electrons: Seq[UnitClause]): UnitClause = {

    assert(electrons.length == nucleus.body.length)

    val constraintFromElectrons =
      for (((rp, occ), ind) <- nucleus.body.zipWithIndex) yield {
        assert(rp == electrons(ind).rs)
        // todo: review if we need something like below
        //if ((electrons(ind)
        //      .constraintAtOcc(occ)
        //      .constants intersect nucleus.head._1.arguments.head.toSet) nonEmpty)
        //  electrons(ind).constraintAtOcc(occ + 1)
        //else
        electrons(ind).constraintAtOcc(occ)
      }

    val unsimplifiedConstraint =
      Conjunction.conj(constraintFromElectrons ++ Seq(nucleus.constraint),
                       symex_sf.order)

    val localSymbols =
      (unsimplifiedConstraint.constants -- nucleus.headSyms)
        .map(_.asInstanceOf[Term])

    val simplifiedConstraint =
      simplifyConstraint(unsimplifiedConstraint,
                         localSymbols,
                         reduceBeforeSimplification = true)

    newUnitClause(rs = nucleus.head._1,
                  constraint = simplifiedConstraint,
                  isPositive = true,
                  headOccInConstraint = nucleus.head._2)
  }

  val unitClauseDB = new UnitClauseDB(relationSymbols.values.toSet)

  // methods handling derivation of useless clauses (merge?)
  def handleForwardSubsumption(nucleus:   NormClause,
                               electrons: Seq[UnitClause]): Unit

  def handleNewUnitClause(clause: UnitClause): Unit

  def handleFalseConstraint(nucleus:   NormClause,
                            electrons: Seq[UnitClause]): Unit

  // whether stored subsumes clause, both of the same relation symbol
  protected def subsumes(stored : UnitClause, clause : UnitClause) : Boolean =
    stored.isPositive == clause.isPositive && // polarity must match
      symex_sf.reducer(clause.constraint)(stored.constraint).isTrue

  protected def buildSolution(): Solution = {
    for ((pred, rs) <- relationSymbols if pred != HornClauses.FALSE)
      yield {
        val predCucs = unitClauseDB.inferred(rs).getOrElse(Nil)
        val predSolution =
          disjunctionOverArgs(rs, predCucs.map(_.constraint))

        // todo: try to simplify after quantification

        (pred, solutionFormula(rs, predSolution))
      }
  }

  /**
   * Returns a counterexample DAG given the last derived unit clause as root,
   * i.e., FALSE :- TRUE.
   */
  protected def buildCounterExample(root: UnitClause): Dag[(IAtom, CC)] = {
    def computeAtoms(headAtom: IAtom, cuc: UnitClause): Dag[(IAtom, CC)] = {
      unitClauseDB.parentsOption(cuc) match {
        case None =>
          DagEmpty
        case Some((nucleus, electrons)) =>
          // try to get ground literals for parent electrons
          import prover._
          val childrenAtoms = scope {
            !!(asIFormula(nucleus.constraint))
            !!(headAtom.args === nucleus.headSyms)
            for ((electron, occ) <- electrons zip nucleus.body.map(_._2))
              !!(asIFormula(electron.constraintAtOcc(occ)))
            val pRes = ???
            assert(pRes == ProverStatus.Sat)
            withCompleteModel { comp =>
              for ((rs, occ) <- nucleus.body)
                yield
                  IAtom(rs.pred,
                        rs.arguments(occ).map(arg => comp.evalToTerm(arg)))
            }
          }
          val subDags: Seq[Dag[(IAtom, CC)]] = {
            for ((electron, atom) <- electrons zip childrenAtoms)
              yield computeAtoms(atom, electron)
          }

          val nextDag: Dag[(IAtom, CC)] =
            if (subDags isEmpty) DagEmpty
            else {
              var next: Dag[(IAtom, CC)] = DagEmpty
              for (subDag <- subDags.reverse if !subDag.isEmpty) {
                next = DagNode(subDag.head, Nil, next)
              }
              next
            }

          val dummyChildren = electrons.indices.map(_ + 1).toList
          val dag: Dag[(IAtom, CC)] =
            DagNode((headAtom, normClauseToCC(nucleus)), dummyChildren, nextDag)
          val resDag = dag
            .substitute((dummyChildren zip subDags).toMap)
            .elimUnconnectedNodes
            .collapseNodes
          resDag
        // substitute the subdags into the dag
        // todo: review, this seems to be inefficient?
      }
    }
    computeAtoms(IAtom(HornClauses.FALSE, Nil), root)
  }

  // true if cuc = "FALSE :- c" and c is satisfiable, false otherwise.
  // None if prover cannot decide
  private[symex] def hasContradiction(cuc         : UnitClause,
                                      checkResult : FeasibilityCheckResult)
    : Option[Boolean] =
    if ((cuc.rs.pred == HornClauses.FALSE) || (!cuc.isPositive))
      checkResult match {
        case FeasibilityCheckResult.Feasible   => Some(true)
        case FeasibilityCheckResult.Infeasible => Some(false)
        case _                                 => None
      }
    else
      Some(false)

  private def newUnitClause(rs:                  RelationSymbol,
                            constraint:          Conjunction,
                            isPositive:          Boolean,
                            headOccInConstraint: Int): UnitClause = {
    val differentOccArgsToRewrite = headOccInConstraint match {
      case 0        => Nil
      case otherOcc => rs.arguments(otherOcc)
    }
    val differentOccSubstMap: Map[ConstantTerm, ConstantTerm] =
      (differentOccArgsToRewrite zip rs
        .arguments(0)).toMap

    // sorted to keep the renaming independent of set iteration order
    val otherConstantsToRewrite =
      symex_sf.order.sort(
        constraint.constants -- (differentOccArgsToRewrite ++
          rs.arguments(headOccInConstraint)))
    val constantSubstMap: Map[ConstantTerm, ConstantTerm] =
      (otherConstantsToRewrite zip symex_sf
        .localSymbolsForPred(pred = rs.pred,
                             numSymbols = otherConstantsToRewrite.size,
                             occ = 0)).toMap

    val predLocalConstraint =
      ConstantSubst(differentOccSubstMap ++ constantSubstMap, symex_sf.order)(
        constraint)
    // resolving the disjunctions of a constraint can enable further
    // simplification. simplify again so that the stored constraint
    // is fully simplified
    val storedConstraint =
      simplifyConstraint(predLocalConstraint,
                         (predLocalConstraint.constants --
                            rs.arguments(0)).map(_.asInstanceOf[Term]).toSet,
                         reduceBeforeSimplification = true)
    // a stored constraint carries at most one atom per function application
    Debug.assertPost(Symex.AC, {
      val lits = storedConstraint.predConj.positiveLits
      lits.map(a => (a.pred, a.init)).distinct.size == lits.size
    })
    normalizedUnitClause(rs, storedConstraint, isPositive)
  }

  private def normalizedUnitClause(rs         : RelationSymbol,
                                   constraint : Conjunction,
                                   isPositive : Boolean) : UnitClause = {
    val normalized =
      ConstraintNormalizer.normalize(rs.arguments(0), constraint,
        n => (symex_sf.localSymbolsForPred(rs.pred, n, 0), symex_sf.order),
        Some(symex_sf.definedSymbolForPred(rs.pred, _)))
    new UnitClause(rs, normalized, isPositive)
  }

  protected def withoutConjunctsUnconnectedToArgs(
      clause      : UnitClause,
      checkResult : FeasibilityCheckResult) : UnitClause = {
    val constraint = withoutConjunctsUnconnectedToArgs(
      clause.constraint, clause.rs.arguments(0).toSet, checkResult)
    if (constraint eq clause.constraint) clause
    else normalizedUnitClause(clause.rs, constraint, clause.isPositive)
  }

  protected def toUnitClause(normClause: NormClause): UnitClause = {
    normClausesConvertedToUnitClauses get normClause match {
      case Some(unitClause) => unitClause
      case None =>
        val unitClause = normClause match {
          case NormClause(constraint, Nil, (rel, 0)) // a fact
              if rel.pred != HornClauses.FALSE =>
            newUnitClause(rel,
                          constraint,
                          isPositive = true,
                          headOccInConstraint = 0)
          case NormClause(constraint, Seq((rel, 0)), (headRel, 0))
              if headRel.pred == HornClauses.FALSE =>
            newUnitClause(rel,
                          constraint,
                          isPositive = false,
                          headOccInConstraint = 0)
          case _ =>
            throw new UnsupportedOperationException(
              "Trying to create a unit clause from a non-unit clause: " + normClause)
        }
        normClausesConvertedToUnitClauses += ((normClause, unitClause))
        unitClause
    }
  }
}
