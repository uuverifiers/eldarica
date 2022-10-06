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

import ap.parser.IExpression._
import ap.parser._
import ap.types.MonoSortedPredicate
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.abstractions.VerificationHints.VerifHintElement
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.extendedquantifiers.Util._
import lazabs.horn.preprocessor.HornPreprocessor
import lazabs.horn.preprocessor.HornPreprocessor._

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

/**
 * Split clauses that have more than one select/store/extquant conjunct.
 */
class Normalizer extends HornPreprocessor {

  val name : String = "normalizing clauses for extended quantifier instrumentation"

  private val clauseBackMapping = new MHashMap[Clause, Clause]
  private val predBackMapping = new MHashMap[Predicate, Predicate]

  //todo: include extended quantifier conjuncts in normalization

  override def process(clauses : Clauses, hints : VerificationHints,
              frozenPredicates : Set[Predicate])
             : (Clauses, VerificationHints, BackTranslator) = {
    val newClauses = {
      val newClauses = new ArrayBuffer[Clause]

      for ((clause@Clause(head, body, constraint), id) <- clauses.zipWithIndex) {
        val conjuncts : Seq[IFormula] =
          LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)

        val selects = conjuncts filter isSelect
        val stores = conjuncts filter isStore
        val consts = conjuncts filter isConst
        val extQuans = conjuncts filter isAggregateFun


        val orderedStores : Seq[IFormula] = {
          val remainingStores = new collection.mutable.HashSet[IFormula]
          val orderedStores = new ArrayBuffer[IFormula]
          stores.foreach(remainingStores add)
          while(remainingStores nonEmpty) {
            val store = remainingStores.find {store =>
              val (Seq(a1), _) = getOriginalArrayTerm(store)
              (remainingStores - store).forall{store2 =>
                val (Seq(a2), _) = getNewArrayTerm(store2)
                a1 != a2
              }
            }.get // last store will always be "found", forall(emptySet) = true
            orderedStores += store
            remainingStores -= store
          }
          orderedStores
        } // todo: review

        // order is important below!
        val instrumentationConjuncts =
          consts ++ orderedStores ++ selects ++ extQuans

        val remainingConstraint =
          conjuncts diff instrumentationConjuncts

        val isGoalClause = clause.head.pred == HornClauses.FALSE
        val isFactClause = clause.body.isEmpty

        val numNewClauses =
          instrumentationConjuncts.length - 1 +
            (if ((isGoalClause || isFactClause) &&
              instrumentationConjuncts.nonEmpty) 1 else 0)

        if(numNewClauses <= 0) {
          newClauses += clause // no normalization needed
          clauseBackMapping.put(clause, clause)
        } else {
          // - consts should be in their own clauses and placed first (no ordering)
          // - stores should be split before the selects and they should be ordered
          //   within themselves
          // - reads (select + ext quans) should be split last, no ordering is needed
          // conjuncts that contain terms not in the new clause are removed
          // we add all intermediate arrays (created with const/store) to intermediate predicates
          // body atoms only appear in the first clause, and their args are added to all intermediate predicates
          // e.g., p :- a1 = const, a2 = store(a1), a3 = store(a2), select(a1), select(a2), c, body
          // rewritten as
          // p0(a1,<bodyArgs>)  :- a1 = const, body
          // p1(a1,...,a2)    :- a2 = store(a1), p0(a1,...), c
          // p2(a1,...,a2,a3) :- a3 = store(b), p1(a1,...,a2), c
          // p3(a1,...,a2,a3) :- select(a1), p2(a1,...,a2,a3), c
          // p :- select(b), p3(a1,a2,a3), c
          var clauseCount = 0

          for((conjunct, i) <-
                ((if (isFactClause) Seq(i(true)) else Nil) ++
                  instrumentationConjuncts ++
                  (if (isGoalClause) Seq(i(true)) else Nil)) zipWithIndex) {
            val newBody =
              if(clauseCount == 0) body else List(newClauses.last.head)
//            val (bodyArgs, bodySorts) =
//              collectArgsSortsFromAtoms(newBody)
//            val (arrayTerm, arraySort) = getNewArrayTerm(conjunct)
            val newHead =
              if (i == numNewClauses - 1 && isGoalClause) {
                val newHeadPred = new Predicate("false_" + id + "_" + clauseCount, 0)
                predBackMapping += ((newHeadPred, head.pred))
                IAtom(newHeadPred, Nil)
              } else if(i < numNewClauses) {
              //val (headArgs, headSorts) = collectArgsSortsFromAtoms(Seq(head))
              val newPredName =
                (if (body.nonEmpty) body.head.pred.name else "entry") + "_" +
                  head.pred.name + "_" + id + "_" + clauseCount
//              val (newHeadArgs, newHeadSorts) = {
//                (headArgs ++ bodyArgs ++ arrayTerm,
//                  headSorts ++ bodySorts ++ arraySort
//                )
//              }
              val (newHeadArgs, newHeadSorts) = {
                val headConstants =
                  SymbolCollector constantsSorted clause.head
                val allConstants : Seq[ConstantTerm] =
                  headConstants ++ (clause.constantsSorted diff headConstants)
                val newArgs : Seq[ConstantTerm] = allConstants
                (newArgs, newArgs.map(c => Sort.sortOf(IConstant(c))))
              }
              val newHeadPred =
                MonoSortedPredicate(newPredName, newHeadSorts)
              predBackMapping += ((newHeadPred, head.pred))
              IAtom(newHeadPred, newHeadArgs)
            } else {
              head
            }

            val newConstraint =
              if (i == numNewClauses && isGoalClause) {
                IExpression.i(true)
              } else and(remainingConstraint ++ Seq(conjunct))
            val newClause = Clause(newHead, newBody, newConstraint)
            newClauses += newClause
            clauseCount += 1
            clauseBackMapping.put(newClause, clause)
          }
        }
      }
      newClauses
    }

    val newPredicateHints : Map[Predicate, Seq[VerifHintElement]] =
      hints.predicateHints.flatMap{
        case (oldPred, hint) =>
          val affectedPreds = predBackMapping.filter{
            case (newP, oldP) =>  oldP == oldPred
          }
          Map(oldPred -> hint) ++ affectedPreds.map{
            case (newP, oldP) => (newP, hint)
          }
      }

    val newHints = VerificationHints(newPredicateHints)

    val translator = new BackTranslator {
      private val backMapping = clauseBackMapping.toMap

      def translate(solution : Solution) = {
        solution -- predBackMapping.keys
//        val newSol = new MHashMap[Predicate, IFormula]
//        for ((newPred, sol) <- solution.iterator)
//          (predBackMapping get newPred) match {
//            case Some(pred) if pred != HornClauses.FALSE => {
//              //val newSol = VariableSubstVisitor(sol, (subst, 1))
//              // todo: subst for sol
//              newSol += ((pred, sol))
//            }
//            case None =>
//              newSol += ((newPred, sol))
//          }
//        newSol.toMap
      }

      def translate(cex : CounterExample) =
        for (p <- cex) yield { // todo: review
          val (a, clause) = p
          (a, backMapping(clause))
        }
    }
    
    clauseBackMapping.clear

    (newClauses, newHints, translator)
  }

  //////////////////////////////////////////////////////////////////////////////

}
