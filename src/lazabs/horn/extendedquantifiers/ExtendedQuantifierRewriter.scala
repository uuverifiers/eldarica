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
               ghostVarInds : Map[ExtendedQuantifierInfo,
                                  Map[Predicate, Seq[GhostVariableInds]]])
  : Clause = {
    // start from the whole constraint
    var newConstraint : IFormula = clause.constraint

    val extQuantifierInfos = gatherExtQuans(Seq(clause))

    for (exqInfo@ExtendedQuantifierInfo(exq, app, a, lo, hi) <- extQuantifierInfos) {
      // todo: below code is experimental and will not work in most cases!

      val GhostVariableInds(iblo, ibhi, ibres, ibarr) =
        ghostVarInds(exqInfo)(clause.body.head.pred).head
      //  getGhostVarInds(exqInfo, ghostVarInds)(clause.body.head.pred).head

      val blo = clause.body.head.args(iblo)
      val bhi = clause.body.head.args(ibhi)
      val bres = clause.body.head.args(ibres)
      val barr = clause.body.head.args(ibarr)

      val (_, sorts) = collectArgsSortsFromAtoms(Seq(clause.body.head))

      newConstraint = ExpressionReplacingVisitor(
        newConstraint,
        replaced = app,
        replaceWith =
          ite(blo === lo & bhi === hi & barr === a,
            bres,
            IConstant(new SortedConstantTerm("unknownRes", sorts(ibarr))))
      )
    }

    Clause(clause.head, clause.body, newConstraint)

  }
}
