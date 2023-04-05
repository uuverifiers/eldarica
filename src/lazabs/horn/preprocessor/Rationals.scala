/**
 * Copyright (c) 2023 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.preprocessor

import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import HornClauses._
import lazabs.horn.bottomup.Util.{Dag, DagNode, DagEmpty}

import ap.parser._
import IExpression._
import ap.theories.rationals.Rationals
import ap.types.MonoSortedPredicate
import Sort.:::

import scala.collection.mutable.{HashMap => MHashMap}

object RationalDenomUnifier extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "unifying denominators"
  
  override def isApplicable(clauses : Clauses,
                            frozenPredicates : Set[Predicate]) : Boolean =
    frozenPredicates.isEmpty &&
    (clauses exists { clause => clause.theories contains Rationals })

  def process(clauses : Clauses, hints : VerificationHints,
              frozenPredicates : Set[Predicate])
             : (Clauses, VerificationHints, BackTranslator) = {

    val predMapping =
      (for (pred <- HornClauses.allPredicates(clauses).iterator) yield {
         val oldSorts = predArgumentSorts(pred)
         val newSorts = oldSorts ++ List(Sort.Integer)
         pred -> MonoSortedPredicate(pred.name, newSorts)
      }).toMap

    val denomConst = new ConstantTerm("denom")
    val denomTerm  = IConstant(denomConst)
    val denomInit  = denomTerm >= 1

    def liftAtom(a : IAtom) : IAtom =
      a.pred match {
        case HornClauses.FALSE => a
        case pred => IAtom(predMapping(pred), a.args ++ List(denomTerm))
      }

    val clausePairs =
      for (clause <- clauses) yield {
        val Clause(head, body, constraint) = clause
        val constraint2 =
          ~Rationals.iPreprocess(~constraint, null)._1
        val constraint3 =
          ExpressionReplacingVisitor(constraint2, Rationals.denom(), denomTerm)
        val constraint4 =
          constraint3 & denomInit
        val constraint5 =
          if (body.isEmpty)
            constraint4 & (denomTerm === Rationals.denom())
          else
            constraint4
        val newClause =
          Clause(liftAtom(head), body map liftAtom, constraint5)
        clause -> newClause
      }

    val newHints = hints.renamePredicates(predMapping)

    val clauseBackMapping =
      (for ((a, b) <- clausePairs.iterator) yield (b, a)).toMap
    val predBackMapping =
      (for ((a, b) <- predMapping.iterator) yield (b, a)).toMap

    val backTranslator = new BackTranslator {
      def translate(solution : Solution) =
        (for ((pred, sol) <- solution.iterator) yield {
           (predBackMapping get pred) match {
             case Some(oldPred) => {
               val oldSol = ExpressionReplacingVisitor(sol, v(pred.arity - 1),
                                                       Rationals.denom())
               oldPred -> oldSol
             }
             case None =>
               pred -> sol
           }
         }).toMap

      def translate(cex : CounterExample) =
        for (p <- cex) yield {
          val (atom@IAtom(pred, args), clause) = p
          val oldAtom = (predBackMapping get pred) match {
            case Some(oldPred) => IAtom(oldPred, args.init)
            case None          => atom
          }
          (oldAtom, clauseBackMapping(clause))
        }
    }

    (clausePairs.unzip._2, hints, backTranslator)
  }

}
