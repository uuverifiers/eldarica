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

import ap.SimpleAPI
import ap.terfor.TerForConvenience
import ap.parser._
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.types.{SortedConstantTerm, Sort}

import lazabs.horn.Util
import lazabs.horn.bottomup.{HornClauses, NormClause}

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

/**
 * Class to invoke external tools as predicate generators. Currently
 * not functional.
 */
class ExternalPredGen extends PredicateGenerator {

  import PredicateGenerator._
  import Util.{Dag, DagNode, DagEmpty}

  def apply(dag : ClauseDag) : Either[PredicateMap, Counterexample] = {
    println("Counterexample:")

    def clauseString(prettyClause : HornClauses.Clause)
                    (implicit prover : SimpleAPI) : String = {
      import PrincessLineariser.{asString => pp}

      pp(prettyClause.head) + " :- " +
      (for (b <- prettyClause.body ++ List(prettyClause.constraint))
       yield pp(b)).mkString(", ") + "."
    }

    SimpleAPI.withProver { p =>
      implicit val prover = p
      var nodeCnt = 1

      def printClauses(dag : ClauseDag, depth : Int) : Map[Int, Int] =
        dag match {
          case DagNode(aoNode, children, subDag) =>
            val childNodes = printClauses(subDag, depth + 1)
            aoNode match {
              case AndNode(clause) => {
                val prettyClause = toPrettyClause(clause)

                println
                print(s"($nodeCnt) ${prettyClause.head} follows from ")

                if (children.isEmpty) {
                  println("clause")
                } else {
                  print((for (c <- children)
                         yield s"(${childNodes(c + depth)})").mkString(", "))
                  println(" and clause")
                }
                println
                println("  " + clauseString(prettyClause))

                val res = childNodes + (depth -> nodeCnt)
                nodeCnt = nodeCnt + 1

                res
              }
              case OrNode(_) => {
                println("(disjunction)")
                childNodes
              }
            }
          case DagEmpty =>
            Map()
        }

      printClauses(dag, 0)
    }

    throw new PredGenFailed("msg")
  }

  private def toPrettyClause
      (clause : NormClause)(implicit prover : SimpleAPI) : HornClauses.Clause =
  prover.scope {
    val clauseOrder = clause.order
    import TerForConvenience._

    prover.addConstantsRaw(clauseOrder sort clauseOrder.orderedConstants)

    val tempPreds =
      for ((rs, _) <- clause.body) yield {
        prover.createRelation(rs.pred.name, rs.pred.arity)
      }
    val tempPredIndex =
      tempPreds.zipWithIndex.toMap

    val (headRS, headOcc) = clause.head

    val headArgs =
      for ((c, n) <- headRS.arguments(headOcc).zipWithIndex)
      yield prover.createConstantRaw(niceVarName(n), Sort.sortOf(c))

    implicit val order = prover.order

    val tempAtoms =
      for (((rs, occ), p) <- clause.body zip tempPreds) yield {
        p(rs.arguments(occ) map (l(_)))
      }

    val simpBody = {
      val body = conj(tempAtoms ++
                        List(clause.constraint,
                             headArgs === headRS.arguments(headOcc)))
      val quanBody =
        exists(clause.allSymbols, body)
      prover.asIFormula(
        ReduceWithConjunction(Conjunction.TRUE, order)(quanBody))
    }

    val dequantifiedBody = {
      import IExpression._

      var sorts = List[Sort]()
      var body = simpBody

      while (body.isInstanceOf[IQuantified]) {
        val ISortedQuantified(Quantifier.EX, sort, d) = body
        body = d
        sorts = sort :: sorts
      }

      val parameterConsts =
        for ((s, n) <- sorts.zipWithIndex)
        yield prover.createConstant(niceVarName(headArgs.size + n), s)
      subst(body, parameterConsts, 0)
    }

    val newHead =
      IAtom(headRS.pred, headArgs)

    val bodyConjuncts =
      LineariseVisitor(Transform2NNF(dequantifiedBody), IBinJunctor.And)

    val (newBody, newConstraint) = {
      import IExpression._

      val bodyArray = new Array[IAtom](tempPreds.size)
      val otherConjuncts = new ArrayBuffer[IFormula]

      for (f <- bodyConjuncts)
        f match {
          case IAtom(p, args) =>
            (tempPredIndex get p) match {
              case Some(idx) =>
                bodyArray(idx) = IAtom(clause.body(idx)._1.pred, args)
              case None =>
                otherConjuncts += f
            }
          case f =>
            otherConjuncts += f
        }

      assert(!bodyArray.contains(null))
      (bodyArray.toList, and(otherConjuncts))
    }

    HornClauses.Clause(newHead, newBody, newConstraint)
  }

  private def niceVarName(index : Int) : String = {
    assert(index >= 0 && index <= 25)
    ('A'.toInt + index).toChar.toString
  }

}
