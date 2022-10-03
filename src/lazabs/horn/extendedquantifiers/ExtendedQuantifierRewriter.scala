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
import ap.parser.IExpression.{Predicate, _}
import ap.parser._
import ap.types.SortedConstantTerm
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.extendedquantifiers.GhostVariableAdder._
import lazabs.horn.extendedquantifiers.Util._

object ExtendedQuantifierRewriter {
  def rewrite (clause       : Clause,
               allGhostVarInds : Map[ExtendedQuantifierInfo,
                                  Map[Predicate, Seq[GhostVariableInds]]])
  : Clause = {
    // start from the whole constraint
    var newConstraint : IFormula = clause.constraint

    val extQuantifierInfos = gatherExtQuans(Seq(clause))

    for (exqInfo@ExtendedQuantifierInfo(exq, app, a, lo, hi) <- extQuantifierInfos) {
      // todo: below code is experimental and will not work in most cases!

      val ghostVarTerms: Seq[GhostVariableTerms] =
        (for (ghostVarInds <- allGhostVarInds(exqInfo)(clause.body.head.pred)) yield {
          val GhostVariableInds(iblo, ibhi, ibres, ibarr) = ghostVarInds

          val blo = clause.body.head.args(iblo)
          val bhi = clause.body.head.args(ibhi)
          val bres = clause.body.head.args(ibres)
          val barr = clause.body.head.args(ibarr)
          GhostVariableTerms(lo = blo, hi = bhi, res = bres, arr = barr)
        })

      // for [g1, g2, g3] combinations will have
      // [[g1], [g2], [g3], [g1,g2], [g1,g3], [g2,g3], [g1,g2,g3]]
      val combinations: Seq[Seq[GhostVariableTerms]] =
        (for (i <- 1 to ghostVarTerms.length) yield {
          ghostVarTerms.combinations(i)
        }).flatten

      // range1 ? res1 : (range 2 ? res2 : (... : range1+range2 ? res1+res : range2+range1 ? res2+res1 : ... ))

      def buildRangeFormula(combs : Seq[Seq[GhostVariableTerms]]) : ITerm = {
        combs.headOption match {
          case Some(comb) =>
            if (comb.length == 1) {
              ite(comb.head.lo === lo & comb.head.hi === hi &
                  comb.head.arr === a,
                comb.head.res, // then
                buildRangeFormula(combs.tail)) // else
            } else if (comb.length == 2) {
              ite(comb(0).lo === lo & comb(0).hi === comb(1).lo &
                  comb(1).hi === hi & comb(0).arr === a & comb(1).arr === a,
                  exq.reduceOp(comb(0).res, comb(1).res), // then
                ite(
                  comb(1).lo === lo & comb(1).hi === comb(0).lo &
                    comb(0).hi === hi & comb(0).arr === a & comb(1).arr === a,
                  exq.reduceOp(comb(1).res, comb(0).res),
                  buildRangeFormula(combs.tail)) // else
                )
            } else {
              ??? // todo: generalize this!
            }
          case None =>
            IConstant(new SortedConstantTerm("unknownRes",
              exqInfo.exTheory.arrayTheory.objSort))
        }
      }

      newConstraint = ExpressionReplacingVisitor(
        newConstraint,
        replaced = app,
        replaceWith = buildRangeFormula(combinations))
    }

    Clause(clause.head, clause.body, newConstraint)

  }
}
