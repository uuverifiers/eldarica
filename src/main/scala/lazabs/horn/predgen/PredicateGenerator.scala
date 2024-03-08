/**
 * Copyright (c) 2011-2023 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.Util._
import lazabs.horn.bottomup.NormClause

import ap.parser.IAtom
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate

import scala.collection.mutable.LinkedHashMap

object PredicateGenerator {

  abstract sealed class AndOrNode[AndD, OrD]
  case class AndNode[AndD, OrD](d : AndD) extends AndOrNode[AndD, OrD]
  case class OrNode [AndD, OrD](d : OrD)  extends AndOrNode[AndD, OrD]

  type ClauseDag      = Dag[AndOrNode[NormClause, Unit]]
  type PredicateMap   = Seq[(Predicate, Seq[Conjunction])]
  type Counterexample = Dag[(IAtom, NormClause)]

  class PredGenFailed(msg : String) extends Exception(msg)

  def fromFunction(f : ClauseDag => Either[PredicateMap, Counterexample])
                     : PredicateGenerator =
    new PredicateGenerator {
      def apply(dag : ClauseDag) = f(dag)
    }

  object FailingPredGen extends PredicateGenerator {
    def apply(dag : ClauseDag) =
      throw new PredGenFailed("predicate generator not implemented")
  }

}

/**
 * Trait for objects that are able to infer new predicates, given a
 * possible counterexample.
 */
trait PredicateGenerator {
  import PredicateGenerator._

  /**
   * Given a recursion-free set of Horn clauses, either infer new
   * predicates to be fed to the CEGAR engine, or prove that the Horn
   * clauses are unsatisfiable by returning a counterexample DAG.
   * 
   * A predicate generator can signal failure by throwing an exception
   * <code>PredicateGenerator.PredGenFailed</code>.
   */
  def apply(dag : ClauseDag) : Either[PredicateMap, Counterexample]

  /**
   * Form the union of the sets of predicates produced by two
   * generators.
   */
  def ++(that : PredicateGenerator) = {
    val fst = this
    val snd = that

    new PredicateGenerator {
      def apply(dag : ClauseDag) : Either[PredicateMap, Counterexample] = {
        try {
          fst.apply(dag) match {
            case Left(preds1) => {
              try {
                snd.apply(dag) match {
                  case Left(preds2) => {
                    val res = new LinkedHashMap[Predicate, Seq[Conjunction]]
                    res ++= preds1
                    for ((p, l) <- preds2)
                      res.put(p, (res.getOrElse(p, List()) ++ l).distinct)
                    Left(res.toSeq)
                  }
                  case Right(cex) =>
                    Right(cex)
                }
              } catch {
                case _ : PredGenFailed => Left(preds1)
              }
            }
            case Right(cex) => {
              Right(cex)
            }
          }
        } catch {
          case _ : PredGenFailed => snd.apply(dag)
        }
      }
    }
  }

}
