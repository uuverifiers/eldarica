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

    val extQuantifierInfos =
      ExtQuantifierFunctionApplicationCollector(clause.constraint)

    for (exqInfo@ExtendedQuantifierInfo(exq, app, a, lo, hi) <- extQuantifierInfos) {
      // todo: below code is experimental and will not work in most cases!

      val GhostVariableInds(iblo, ibhi, ibres, ibarr) =
        ghostVarInds(exqInfo)(clause.body.head.pred).head

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
