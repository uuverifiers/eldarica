/**
 * Copyright (c) 2026 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.Util.Dag
import lazabs.horn.bottomup.HornClauses
import HornClauses._

import ap.basetypes.IdealInt
import ap.parser._
import IExpression._
import ap.util.Seqs

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}

object EquationInliner {

  object InlineableEquation {
    def unapply(f : IFormula) : Option[(ITerm, ConstantTerm)] = f match {
      case Eq(t, s@IConstant(c)) =>
        if (ContainsSymbol.freeFromConstants(t, Set(c)) &&
            Sort.sortOf(t) == Sort.sortOf(s)) {
          Some((t, c))
        } else {
          None
        }
      case _ =>
        None
    }
  }

  class ConstantCounter extends CollectingVisitor[Int, Unit] {
    val occurrences = new MHashMap[ConstantTerm, Int]

    def apply(f : IExpression, inc : Int) : Unit = visitWithoutResult(f, inc)

    def postVisit(f : IExpression, inc : Int, subres : Seq[Unit]) : Unit =
      f match {
        case IConstant(c) => {
          occurrences.put(c, occurrences.getOrElse(c, 0) + inc)
          ()
        }
        case _ => ()
      }
  }

}

/**
 * Preprocessor implementing a limited kind of equation inlining; such inlining
 * often helps theory preprocessors.
 */
class EquationInliner extends HornPreprocessor {
  import HornPreprocessor._
  import EquationInliner._

  val name : String = "equation inlining"

  def process(clauses : Clauses, hints : VerificationHints,
              frozenPredicates : Set[Predicate])
             : (Clauses, VerificationHints, BackTranslator) = {
    val clauseMapping = new MHashMap[Clause, Clause]

    val newClauses =
      for (clause <- clauses; newClause = inlineEqs(clause)) yield {
        clauseMapping.put(newClause, clause)
        newClause
      }

    val translator = new BackTranslator {
      def translate(solution : Solution) = solution
      def translate(cex : CounterExample) =
        for (p <- cex) yield (p._1, clauseMapping(p._2))
    }

    (newClauses, hints, translator)
  }

  def inlineEqs(clause : Clause) : Clause = {
    val Clause(head, body, constraint) = clause

    val constCounter = new ConstantCounter
    val blockedConstants = new MHashSet[ConstantTerm]

    var updated = false

    blockedConstants ++= SymbolCollector.constants(head)
    for (a <- body)
      blockedConstants ++= SymbolCollector.constants(a)

    var conjuncts = LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)

    for (c <- conjuncts)
      constCounter(c, 1)

    var cont = true
    while (cont) {
      // Discover equations that can be inlined
      val equations = new MHashMap[ConstantTerm, ITerm]
      val blockedConstants2 = new MHashSet[ConstantTerm]

      val otherConjuncts = conjuncts.filter {
        case e@InlineableEquation(t, c)
            if constCounter.occurrences(c) <= 2 &&
               !blockedConstants(c) && !blockedConstants2(c) &&
               ContainsSymbol.freeFromConstants(t, equations.keySet.toSet) => {
          equations.put(c, t)
          blockedConstants2 ++= SymbolCollector.constants(e)
          false
        }
        case _ =>
          true
      }

      cont = !equations.isEmpty

      if (cont) {
        // Update the occurrence counts
        for ((c, t) <- equations) {
          constCounter.occurrences(c) match {
            case 1 => constCounter(t === c, -1)
            case 2 => constCounter.occurrences.put(c, 0)
            case _ => throw new Exception
          }
        }

        val subst = equations.toMap
        val newConjuncts = otherConjuncts.map(f => ConstantSubstVisitor(f, subst))

        conjuncts = newConjuncts
        updated = true
      }
    }

    if (updated)
      Clause(head, body, and(conjuncts))
    else
      clause
  }
}