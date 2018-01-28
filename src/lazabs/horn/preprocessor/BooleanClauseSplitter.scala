/**
 * Copyright (c) 2016-2018 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.parser.HornReader

import ap.basetypes.IdealInt
import ap.parser._
import IExpression._
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

/**
 * Elimination of remaining Boolean structure in clauses.
 */
object BooleanClauseSplitter extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "Boolean clause splitting"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val clauseMapping = new MHashMap[Clause, Clause]

    val newClauses =
      for (clause <- clauses; newClause <- simpClause(clause)) yield {
        clauseMapping.put(newClause, clause)
        newClause
      }

    val translator = new BackTranslator {
      def translate(solution : Solution) =
        solution
      def translate(cex : CounterExample) =
        for (p <- cex) yield (p._1, clauseMapping(p._2))
    }

    (newClauses, hints, translator)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def simpClause(clause : Clause) : Seq[Clause] = {
    val Clause(head@IAtom(headPred, headArgs), body, constraint) = clause

    var newConstCounter = 0
    var newConstraint = constraint
    val seenHeadArgs = new MHashSet[ConstantTerm]

    def newConst(s : Sort) = {
      val res = s newConstant ("arg" + newConstCounter)
      newConstCounter = newConstCounter + 1
      i(res)
    }

    val newHeadArgs =
      for ((t, tSort) <- headArgs zip predArgumentSorts(headPred))
      yield t match {
        case IConstant(c) if !(seenHeadArgs contains c) => {
          seenHeadArgs += c
          t
        }
        case t => {
          val newArg = newConst(tSort)
          newConstraint = newConstraint & (t === newArg)
          newArg
        }
      }

    val newBody = for (IAtom(pred, args) <- body) yield {
      val newArgs =
        for ((t, tSort) <- args zip predArgumentSorts(pred)) yield {
          if (needsProcessing(t)) {
            val newArg = newConst(tSort)
            newConstraint = newConstraint & (t === newArg)
            newArg
          } else {
            t
          }
        }
      IAtom(pred, newArgs)
    }

    val processedConstraint =
      EquivExpander(PartialEvaluator(~newConstraint))

    var prenexConstraint =
      Transform2Prenex(Transform2NNF(processedConstraint), Set(Quantifier.ALL))
    var varSubst : List[ITerm] = List()
    
    var cont = true
    while (cont) prenexConstraint match {
      case IQuantified(Quantifier.ALL, d) => {
        prenexConstraint = d
        varSubst = newConst(Sort.Integer) :: varSubst
      }
      case _ =>
        cont = false
    }

    val groundConstraint = subst(prenexConstraint, varSubst, 0)

    for (conjunct <- HornReader.cnf_if_needed(groundConstraint)) yield {
      Clause(IAtom(headPred, newHeadArgs), newBody, ~conjunct)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def needsProcessing(t : ITerm) : Boolean = try {
    NeedsProcessingVisitor.visitWithoutResult(t, ())
    false
  } catch {
    case NeedsProcessingException => true
  }

  private object NeedsProcessingException extends Exception

  private object NeedsProcessingVisitor extends CollectingVisitor[Unit, Unit] {
    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult = {
      if (t.isInstanceOf[IFormula])
        throw NeedsProcessingException
      KeepArg
    }
    def postVisit(t : IExpression, arg : Unit, subres : Seq[Unit]) : Unit = ()
  }

}