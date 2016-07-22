/**
 * Copyright (c) 2011-2016 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.global._
import lazabs.horn.bottomup.Util.Dag

import ap.basetypes.IdealInt
import ap.parser._
import IExpression._
import lazabs.prover.PrincessWrapper
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

/**
 * Split clause bodies into separate disjuncts.
 */
class ClauseSplitter extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "splitting clause constraints"

  private val clauseBackMapping = new MHashMap[Clause, Clause]

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val newClauses = SimpleAPI.withProver { p =>
      // turn the resulting formula into DNF, and split positive equations
      // (which often gives better performance)

      import p._

      val newClauses = new ArrayBuffer[Clause]

      for (clause@Clause(head, body, constraint) <- clauses) scope {
        addConstantsRaw(SymbolCollector constantsSorted constraint)
        for (d <- ap.PresburgerTools.nonDNFEnumDisjuncts(asConjunction(constraint)))
          for (f <- splitPosEquations(Transform2NNF(!asIFormula(d)))) {
            if (newClauses.size % 100 == 0)
              lazabs.GlobalParameters.get.timeoutChecker()
            val newClause = Clause(head, body, Transform2NNF(!f))
            newClauses += newClause
            clauseBackMapping.put(newClause, clause)
          }
      }

      newClauses

//      (for (Clause(head, body, constraint) <- clauses4.iterator;
//            constraint2 <- splitConstraint(~constraint))
//       yield Clause(head, body, Transform2NNF(!constraint2))).toList
    }

    val translator = new BackTranslator {
      private val backMapping = clauseBackMapping.toMap

      def translate(solution : Solution) =
        solution

      def translate(cex : CounterExample) =
        for (p <- cex) yield {
          val (a, clause) = p
          (a, backMapping(clause))
        }
    }
    
    clauseBackMapping.clear

    (newClauses, hints, translator)
  }

  //////////////////////////////////////////////////////////////////////////////

  object CNFSimplifier extends Simplifier {
    override protected def furtherSimplifications(expr : IExpression) =
      expr match {
        case IBinFormula(IBinJunctor.Or, f,
                         IBinFormula(IBinJunctor.And, g1, g2)) =>
          (f | g1) & (f | g2)
        case IBinFormula(IBinJunctor.Or,
                         IBinFormula(IBinJunctor.And, g1, g2),
                         f) =>
          (g1 | f) & (g2 | f)
        case expr => expr
      }
  }

  def splitPosEquations(f : IFormula) : Seq[IFormula] = {
    val split =
      or(for (g <- LineariseVisitor(f, IBinJunctor.Or)) yield g match {
           case EqZ(t) => geqZero(t) & geqZero(-t)
           case g => g
         })
    LineariseVisitor(CNFSimplifier(split), IBinJunctor.And)
  }

}