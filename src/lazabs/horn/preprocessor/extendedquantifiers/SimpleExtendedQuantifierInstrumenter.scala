package lazabs.horn.preprocessor.extendedquantifiers

import ap.parser.IExpression.Predicate
import lazabs.horn.preprocessor.HornPreprocessor
import HornPreprocessor.{Clauses, VerificationHints, _}
import Util._
import InstrumentingPreprocessor._

class SimpleExtendedQuantifierInstrumenter(clauses : Clauses,
                                           hints : VerificationHints,
                                           frozenPredicates : Set[Predicate]) {
  val exqApps = gatherExtQuans(clauses)
  val exqs = exqApps.map(_.exTheory).toSet
  private val clauseInstrumenters = (exqs.map(exq =>
    (exq, new SimpleClauseInstrumenter(exq)))).toMap
  private val instrumentingPreprocessor =
    new InstrumentingPreprocessor(clauses, hints, frozenPredicates, clauseInstrumenters)
  val (InstrumentationResult(instrumentedClauses, branchPredicates, searchSpace),
        newHints, newFrozenPredicates) = instrumentingPreprocessor.process
}
