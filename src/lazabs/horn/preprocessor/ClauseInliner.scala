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

import lazabs.horn.bottomup.HornClauses
import HornClauses._
import lazabs.horn.bottomup.Util.Dag

import ap.basetypes.IdealInt
import ap.parser._
import IExpression._
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

/**
 * Inline linear definitions.
 */
object ClauseInliner extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "clause inlining"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val (newClauses, newHints) = elimLinearDefs(clauses, hints)

    (newClauses, newHints, IDENTITY_TRANSLATOR)
  }

  //////////////////////////////////////////////////////////////////////////////

  def elimLinearDefs(allClauses : Seq[HornClauses.Clause],
                     allInitialPreds : Map[Predicate, Seq[IFormula]])
                    : (Seq[HornClauses.Clause], Map[Predicate, Seq[IFormula]]) = {
    var changed = true
    var clauses = allClauses
    var initialPreds = allInitialPreds

    val allInlinedClauses = new MHashMap[Predicate, Clause]

    while (changed) {
      changed = false

      // determine relation symbols that are uniquely defined

      val uniqueDefs =
        extractUniqueDefs(clauses)
      val finalDefs =
        extractAcyclicDefs(allClauses, uniqueDefs, allInlinedClauses)

      val newClauses =
        for (clause@Clause(IAtom(p, _), _, _) <- clauses;
             if (!(finalDefs contains p)))
        yield applyDefs(clause, finalDefs)

      if (newClauses.size < clauses.size) {
        clauses = newClauses
        changed = true
      }

      initialPreds = initialPreds -- finalDefs.keys
    }

    (clauses, initialPreds)
  }

  //////////////////////////////////////////////////////////////////////////////

  def extractUniqueDefs(clauses : Iterable[Clause]) = {
    val uniqueDefs = new MHashMap[Predicate, Clause]
    val badHeads = new MHashSet[Predicate]
    badHeads += FALSE

    for (clause@Clause(head, body, _) <- clauses)
      if (!(badHeads contains head.pred)) {
        if ((uniqueDefs contains head.pred) ||
            body.size > 1 ||
            (body.size == 1 && head.pred == body.head.pred)) {
          badHeads += head.pred
          uniqueDefs -= head.pred
        } else {
          uniqueDefs.put(head.pred, clause)
        }
      }

    uniqueDefs.toMap
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Extract an acyclic subset of the definitions, and
   * shorten definition paths
   */
  def extractAcyclicDefs(clauses : Clauses,
                         uniqueDefs : Map[Predicate, Clause],
                         oriInlinedClauses : MHashMap[Predicate, Clause]) = {
    var remDefs = new MHashMap[Predicate, Clause] ++ uniqueDefs
    val finalDefs = new MHashMap[Predicate, Clause]

    while (!remDefs.isEmpty) {
      val bodyPreds =
        (for (Clause(_, body, _) <- remDefs.valuesIterator;
              IAtom(p, _) <- body.iterator)
         yield p).toSet
      val (remainingDefs, defsToInline) =
        remDefs partition { case (p, _) => bodyPreds contains p }

      if (defsToInline.isEmpty) {
        // we have to drop some definitions to eliminate cycles
        val pred =
          (for (Clause(IAtom(p, _), _, _) <- clauses.iterator;
                if ((remDefs contains p) && (bodyPreds contains p)))
           yield p).next

        remDefs retain {
          case (_, Clause(_, Seq(), _)) => true
          case (_, Clause(_, Seq(IAtom(p, _)), _)) => p != pred
        }
      } else {
        remDefs = remainingDefs

        finalDefs transform {
          case (_, clause) => applyDefs(clause, defsToInline)
        }

        finalDefs ++= defsToInline
        oriInlinedClauses ++= defsToInline
      }
    }

    finalDefs.toMap
  }

  //////////////////////////////////////////////////////////////////////////////

  def applyDefs(clause : Clause,
                defs : scala.collection.Map[Predicate, Clause]) : Clause = {
    val Clause(head, body, constraint) = clause
    assert(!(defs contains head.pred))

    var changed = false

    val (newBody, newConstraints) = (for (bodyLit@IAtom(p, args) <- body) yield {
      (defs get p) match {
        case None =>
          (List(bodyLit), i(true))
        case Some(defClause) => {
          changed = true
          defClause inline args
        }
      }
    }).unzip

    if (changed)
      Clause(head, newBody.flatten, constraint &&& and(newConstraints))
    else
      clause
  }

}