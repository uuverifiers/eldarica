package lazabs.horn.extendedquantifiers

import ap.parser.IExpression.{Predicate, _}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.extendedquantifiers.Util.ExtendedQuantifierInfo
import lazabs.horn.extendedquantifiers.GhostVariableAdder._
import lazabs.horn.preprocessor.HornPreprocessor._
import lazabs.horn.preprocessor._

class GhostVariableInitializer(
  ghostVarInds : Map[ExtendedQuantifierInfo, Map[Predicate, Seq[GhostVariableInds]]])
  extends HornPreprocessor {
  override val name: String = "Initializing ghost variables"

  override def process(clauses: Clauses,
                       hints: VerificationHints,
                       frozenPredicates: Set[Predicate]):
  (Clauses, VerificationHints, HornPreprocessor.BackTranslator) = {
    val entryClauses = clauses.filter(_.body isEmpty)


    val newClauses = for (clause <- clauses) yield {
      if (entryClauses contains clause) {
        val newConjuncts = for ((exq, predToGhostVars) <- ghostVarInds) yield {
          val ghostVars = predToGhostVars(clause.head.pred)
          // todo: support for multiple ranges
          val GhostVariableInds(lo, hi, res, arr) = ghostVars.head
          clause.head.args(lo) === 0 &&& clause.head.args(hi) === 0
        }
        val newConstraint = clause.constraint &&&
          newConjuncts.fold(i(true))((c1, c2) => c1 &&& c2)
        Clause(clause.head, clause.body, newConstraint)
      } else {
        clause
      }
    }
    val clauseBackMapping = (newClauses zip clauses).toMap

    val translator = new BackTranslator {
      def translate(solution : Solution) = solution

      def translate(cex : CounterExample) =
        for (p <- cex) yield (p._1, clauseBackMapping(p._2))
    }

    (newClauses, hints, translator)
  }
}
