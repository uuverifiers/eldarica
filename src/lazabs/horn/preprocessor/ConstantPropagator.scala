/**
 * Copyright (c) 2018 Philipp Ruemmer. All rights reserved.
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

import ap.parser._
import ap.basetypes.IdealInt

import lazabs.horn.bottomup.HornClauses

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 LinkedHashSet, ArrayBuffer}

/**
 * A simple implementation of forward constant propagation.
 */
object ConstantPropagator extends HornPreprocessor {
  import HornPreprocessor._
  import HornClauses.Clause
  import SymbolSplitter.ClausePropagator
  import IExpression.{Predicate, ConstantTerm}

  val name : String = "constant propagation"

  //////////////////////////////////////////////////////////////////////////////

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val allPreds = HornClauses allPredicates clauses
    
    val clauseSeq = clauses.toVector
    val clausesWithBodyPred =
      (for ((clause, n) <- clauseSeq.zipWithIndex; IAtom(p, _) <- clause.body)
       yield (p, n)) groupBy (_._1)

    val propagators =
      for (clause <- clauseSeq) yield new ClausePropagator(clause)

    val abstractValues = new MHashMap[Predicate, NonBottomAbstractElement]
    val clausesTodo = new LinkedHashSet[Int]

    // start with the clauses with empty body
    for ((Clause(_, Seq(), _), n) <- clauseSeq.iterator.zipWithIndex)
      clausesTodo += n

    while (!clausesTodo.isEmpty) {
      val nextID = clausesTodo.head
      clausesTodo -= nextID
      val Clause(head, body, _) = clauseSeq(nextID)
      val propagator = propagators(nextID)

      try {
        for (IAtom(p, args) <- body.iterator;
             constantArgs <- (abstractValues get p).iterator;
             (IConstant(c), Some(t)) <- args.iterator zip constantArgs.iterator)
          propagator.assign(c, t)

        propagator.propagate

        val headPred = head.pred
        val oldAbstractEl = abstractValues get headPred
        val newAbstractEl = Some(propagator constantArgs head)
        val jointEl = join(oldAbstractEl, newAbstractEl)

        if (jointEl != oldAbstractEl) {
          abstractValues.put(headPred, jointEl.get)
          for ((_, n) <- clausesWithBodyPred.getOrElse(headPred, List()))
            clausesTodo += n
        }
      } catch {
        case ClausePropagator.InconsistentAssignment => // nothing to do
      }

      propagator.reset
    }

    ////////////////////////////////////////////////////////////////////////////

//    println(abstractValues.toList mkString "\n")

    val clauseBackMapping = new MHashMap[Clause, Clause]

    var symbolCounter = 0
    def newConst = {
      val res = new ConstantTerm ("inlined" + symbolCounter)
      symbolCounter = symbolCounter + 1
      IExpression.i(res)
    }

    var changed = false

    val newClauses =
      for (clause <- clauses) yield {
        val Clause(head, body, constraint) = clause
        var newConstraint = constraint
      
        val newBody =
          for (a@IAtom(p, args) <- body) yield (abstractValues get p) match {
            case None => {
              // this clause can be deleted, it is not reachable
              newConstraint = newConstraint &&& false
              a
            }
            case Some(constantArgs) => {
              val newArgs =
                for ((a, ca) <- args zip constantArgs) yield ca match {
                  case None => a
                  case Some(t) => {
                    newConstraint = newConstraint &&& (a === t)
                    // in this case we can replace the old argument with a fresh
                    // constant, its value is determined anyway
                    newConst
                  }
                }
              IAtom(p, newArgs)
            }
          }

        val newClause =
          if (newConstraint eq constraint) {
            clause
          } else {
            changed = true
            Clause(head, newBody, newConstraint)
          }
          
        clauseBackMapping.put(newClause, clause)
        newClause
      }

    val translator =
      if (changed) {
        new BackTranslator {
          import IExpression._

          def translate(solution : Solution) =
            solution transform {
              case (pred, sol) => (abstractValues get pred) match {
                case None =>
                  sol
                case Some(constantArgs) => {
                  val subst =
                    (for ((arg, ind) <- constantArgs.iterator.zipWithIndex)
                     yield (arg getOrElse v(ind))).toList
                  val simpSol = SimplifyingVariableSubstVisitor(sol, (subst, 0))

                  and(for ((Some(t), ind) <- constantArgs.iterator.zipWithIndex)
                      yield SymbolSplitter.solutionEquation(ind, t)) &&&
                  simpSol
                }
              }
            }
          
          def translate(cex : CounterExample) =
            for (p <- cex) yield (p._1, clauseBackMapping(p._2))
        }
      } else {
        IDENTITY_TRANSLATOR
      }

    (newClauses, hints, translator)
  }

  //////////////////////////////////////////////////////////////////////////////

  private type NonBottomAbstractElement = Seq[Option[ITerm]]
  private type AbstractElement          = Option[NonBottomAbstractElement]

  private def join(a : AbstractElement, b : AbstractElement) : AbstractElement =
    a match {
      case None => b
      case Some(aArgs) => b match {
        case None => a
        case Some(bArgs) =>
          Some(for (p <- aArgs zip bArgs) yield p match {
                 case (s@Some(x), Some(y)) if x == y => s
                 case _                              => None
               })
      }
    }
}
