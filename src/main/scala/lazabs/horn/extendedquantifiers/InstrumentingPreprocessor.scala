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

import ap.parser.IExpression.Predicate
import ap.parser._
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.preprocessor.HornPreprocessor._
import Util._
import ap.terfor.TerForConvenience.conj
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction
import ap.theories.TheoryRegistry
import lazabs.horn.bottomup.HornClauses

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap,
                                 HashSet => MHashSet}

object InstrumentingPreprocessor {
  case class InstrumentationResult(
    clauses                   : Clauses,
    branchPredicates          : Set[Predicate],
    searchSpace               : Seq[Seq[(Predicate, Conjunction)]])
  // single arity (int) predicates to select an instrumentation branch

  // given a k, returns a conjunction to initialize one of the instrumentation
  // predicates such that only one of the clauses will be selected
  // 0 selects no instrumentation, 1 -- n selects one of the n ways to instrument.
  def getConjunctionForBranch(k : Int) : Conjunction = {
    import IExpression._
    val order = TermOrder.EMPTY
    conj(InputAbsy2Internal(v(0) === i(k), order))(order)
  }
}

//trait ClauseInstrumenter {
//  def instrumentClauses (clauses : Clauses,
//                         extendedQuantifierInfos : Seq[ExtendedQuantifierInfo])
//  : (InstrumentationResult, BackTranslator)
//}

//trait ExtendedQuantifierFunAppRewriter {
//  def rewriteExtQuansFunApps(clauses : Clauses) : Clauses
//}

class InstrumentingPreprocessor(
  clauses                  : Clauses,
  hints                    : VerificationHints,
  frozenPredicates         : Set[Predicate],
  instrumentationOperators : Set[InstrumentationOperator],
  numGhostRanges           : Int)
{
  import InstrumentingPreprocessor._
  private val exqApps : Seq[ExtendedQuantifierApp] = gatherExtQuans(clauses)
  private val exqs : Set[ExtendedQuantifier] = exqApps.map(_.exTheory).toSet

  {
    val undefinedExqs = exqs.diff(instrumentationOperators.map(_.exq))
    if (undefinedExqs.nonEmpty) {
      throw new IllegalArgumentException(
        "Input set of clauses contains extended quantifier applications for " +
        "which an instrumentationn operator is not defined: {" +
        undefinedExqs.map(_.morphism.name).mkString(",") + "}.")
    }
  }

  private val exqToInstrumentationOperator
  : Map[ExtendedQuantifier, InstrumentationOperator] =
    instrumentationOperators.map(op => op.exq -> op).toMap

  private val translators = new ArrayBuffer[BackTranslator]
  private val branchPreds = new MHashSet[Predicate]

  exqs foreach TheoryRegistry.register

  // normalize the clauses
  // TODO: test and switch to the new normalizer
  private val normalizer = new Normalizer
  val (clausesNormalized, hintsNormalized, backTranslatorNormalized) =
  normalizer.process(clauses, hints, frozenPredicates)
  translators += backTranslatorNormalized

  // add ghost variables for each extended quantifier application
  private val ghostVariableAdder =
    new GhostVariableAdder(exqApps, exqToInstrumentationOperator, numGhostRanges)
  val (clausesGhost, hintsGhost, backTranslatorGhost, ghostVarMap) =
    ghostVariableAdder.processAndGetGhostVarMap(clausesNormalized, hintsNormalized, frozenPredicates)
  translators += backTranslatorGhost

  // intitialize the ghost variables
  private val ghostVariableInitializer =
    new GhostVariableInitializer(ghostVarMap, exqToInstrumentationOperator)
  private val (clausesGhostInit, hintsGhostInit, backTranslatorGhostInit) =
    ghostVariableInitializer.process(clausesGhost, hintsGhost, frozenPredicates)
  translators += backTranslatorGhostInit

  def process : (InstrumentationResult, VerificationHints, BackTranslator) = {

    val (instrumentationResult, instBackTranslator) =
      instrumentClauses(clausesGhostInit)

    (instrumentationResult, hintsGhostInit,
      new ComposedBackTranslator(instBackTranslator :: translators.reverse.toList))
  }

  private def instrumentClauses(clausesForInst : Clauses) :
  (InstrumentationResult, BackTranslator) = {
    val newClauses =
      new ArrayBuffer[Clause]

    val clauseBackMapping = new MHashMap[Clause, Clause]

    val numBranchesForPred = new MHashMap[Predicate, Int]

    for ((clause, clauseInd) <- clausesForInst.zipWithIndex) {
      if (clause.head.pred == HornClauses.FALSE) {
        newClauses += clause
        clauseBackMapping += ((clause, clause))
      }
      else {
        val instrumentationsForClause =
          for (extendedQuantifierInfo <- exqApps) yield {
            val clauseInstrumenter : ClauseInstrumenter =
              exqToInstrumentationOperator get extendedQuantifierInfo.exTheory match {
                case Some(instOp) => new ClauseInstrumenter(instOp)
                case None =>
                  throw new Exception("Could not find an instrumenter for the" +
                    " extended quantifier: " + extendedQuantifierInfo.exTheory.morphism.name)
              }
            clauseInstrumenter.instrument(clause,
              //getGhostVarInds(extendedQuantifierInfo, ghostVarMap),
              ghostVarMap(extendedQuantifierInfo),
              extendedQuantifierInfo)
          }
        // in each clause, the search space is the product of instrumentations for each extended quantifier
        val combinedInstrumentations =
          instrumentationsForClause.reduceOption((instrs1, instrs2) =>
            Instrumentation.product(instrs1, instrs2)).getOrElse(Nil)

        if (combinedInstrumentations.exists(inst =>
          inst != Instrumentation.emptyInstrumentation)) {
          // we need one branch predicate per instrumented clause
          val branchPredicate =
            new Predicate("Br_" + clauseInd, 1)

          numBranchesForPred += ((branchPredicate, combinedInstrumentations.length))
          branchPreds += branchPredicate

          // one new clause per instrumentation inst in combinedInstrumentations
          //  + n new assertion clauses for the n assertion conjuncts in inst
          for ((instrumentation, branchId) <- combinedInstrumentations zipWithIndex) {
            val newHeadArgs: Seq[ITerm] =
              for ((arg: ITerm, ind: Int) <- clause.head.args.zipWithIndex) yield {
                ind match {
                  case i if (instrumentation.headTerms get i).nonEmpty =>
                    instrumentation.headTerms(i)
                  case _ => arg
                }
              }
            val newHead = IAtom(clause.head.pred, newHeadArgs)
            val newBody = clause.body ++
              Seq(IAtom(branchPredicate, Seq(IExpression.i(branchId))))
            // todo: body terms for other body atoms might need to be changed too!

            var rewrittenConstraint = clause.constraint
            for((oldTerm, newTerm) <- instrumentation.rewriteConjuncts) {
              rewrittenConstraint = ExpressionReplacingVisitor(
                clause.constraint, replaced = oldTerm, replaceWith = newTerm)
            }

            val newConstraint = instrumentation.constraint &&& rewrittenConstraint

            // exclude any rewritten conjuncts from the constraints of assertion clauses
            val constraintForAssertions = {
              val conjuncts : Seq[IFormula] =
                LineariseVisitor(Transform2NNF(clause.constraint),
                                               IBinJunctor.And)
              // todo: refactor
              IExpression.and(
                conjuncts diff instrumentation.rewriteConjuncts.keys.toSeq)
            }

            val newClause = Clause(newHead, newBody, newConstraint)
            newClauses += newClause
            clauseBackMapping += ((newClause, clause))

            for (assertion <- instrumentation.assertions) {
              val assertionClause =
                Clause(IAtom(HornClauses.FALSE, Nil),
                             newBody, constraintForAssertions &&& ~assertion)
              newClauses += assertionClause
              clauseBackMapping += ((assertionClause, clause))
            }
          }
        } else {
          newClauses += clause
          clauseBackMapping += ((clause, clause))
        }
      }
    }

    val conjsForBranchPred : List[List[(Predicate, Conjunction)]] =
      (for ((pred, numBranches) <- numBranchesForPred) yield
          (for (i <- 0 until numBranches)
            yield ((pred, getConjunctionForBranch(i)))).toList).toList

    def generateSearchSpace(conjs: List[List[(Predicate, Conjunction)]]) :
      List[List[(Predicate, Conjunction)]] = {
      conjs match {
        case hd :: _ =>
          hd.flatMap(pair => generateSearchSpace(conjs.tail).map(pair :: _))
        case Nil =>
          List(Nil)
      }
    }

    val searchSpace : Seq[List[(Predicate, Conjunction)]] =
      generateSearchSpace(conjsForBranchPred)

    val result = InstrumentationResult(
      newClauses, branchPreds.toSet, searchSpace)

    val translator = new BackTranslator {
      def translate(solution : Solution) = solution -- branchPreds

      def translate(cex : CounterExample) =
        for (p <- cex) yield (p._1, clauseBackMapping(p._2))
    }

    (result, translator)

  }

}
