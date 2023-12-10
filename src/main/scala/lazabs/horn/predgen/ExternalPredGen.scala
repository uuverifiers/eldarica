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

package lazabs.horn.predgen

import ap.terfor.TerForConvenience
import ap.parser._
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}

import lazabs.horn.Util
import lazabs.horn.bottomup.{HornClauses, NormClause}

class ExternalPredGen extends PredicateGenerator {

  import PredicateGenerator._
  import Util.Dag

  def apply(dag : ClauseDag) : Either[PredicateMap, Counterexample] = {
    println("Counterexample:")

    val clauseDag : Dag[String] =
      for (n <- dag) yield n match {
        case AndNode(clause) => {
          toPrettyClause(clause)
          clause.toString
        }
        case OrNode(_) =>
          "(disjunction)"
      }

    clauseDag.prettyPrint
    throw new PredGenFailed("msg")
  }

  private def toPrettyClause(clause : NormClause) : HornClauses.Clause = {
    val clauseOrder = clause.order
    import TerForConvenience._

    val tempPreds =
      for ((rs, _) <- clause.body) yield {
        new Predicate(rs.pred.name, rs.pred.arity)
      }

    implicit val order = clauseOrder extendPred tempPreds

    val tempAtoms =
      for (((rs, occ), p) <- clause.body zip tempPreds) yield {
        p(rs.arguments(occ) map (l(_)))
      }
    val body =
      conj(tempAtoms ++ List(clause.constraint))
    val quanBody =
      exists(clause.allSymbols filterNot clause.headSyms.toSet, body)

    val simpBody =
      ReduceWithConjunction(Conjunction.TRUE, order)(quanBody)

    println(simpBody)

    null
  }

}
