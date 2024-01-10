package lazabs.horn.extendedquantifiers

import ap.parser._
import ap.types.Sort
import lazabs.horn.extendedquantifiers.Util._

object RewriteRules {
  /**
   * The result of a rewrite rule. Let `c` be the original conjunct that the
   * rewrite rule is applied to. Then the new formula  will be:
   * `subst(c &&& newConjunct, rewriteFormulas)` where `subst` is some method
   * that rewrites all formulas appearing in the keys of `rewriteFormulas` with
   * their values.
   * Each formula in `assertions` will also be asserted.
   */
  case class Result(newConjunct     : IFormula,
                    rewriteFormulas : Map[IFormula, IFormula],
                    assertions      : Seq[IFormula])
}

trait RewriteRules {
  // These rules are hardcoded as the array operations, but with some effort
  // the methods could also be generalized to a map from theory functions to
  // rewrite rules.

  import InstrumentationOperator.GhostVar

  /**
   * `oldGhostTerms` and `newGhostTerms` are the old and new values of ghost
   * variables defined in [[InstrumentationOperator.ghostVars]].
   * All rewrite rules return a sequence of [[RewriteRules.Result]], which
   * contains information about which conjuncts to add, rewrite, and assert.
   */
  def rewriteStore(oldGhostTerms : Map[GhostVar, ITerm],
                   newGhostTerms : Map[GhostVar, ITerm],
                   storeInfo     : StoreInfo) : Seq[RewriteRules.Result]
  def rewriteSelect(oldGhostTerms : Map[GhostVar, ITerm],
                    newGhostTerms : Map[GhostVar, ITerm],
                    selectInfo    : SelectInfo) : Seq[RewriteRules.Result]
  def rewriteConst(oldGhostTerms : Map[GhostVar, ITerm],
                   newGhostTerms : Map[GhostVar, ITerm],
                   constInfo     : ConstInfo) : Seq[RewriteRules.Result]

  /**
   * The rule for rewriting applications of [[ExtendedQuantifier.morphism]].
   * @param ghostTerms A collection of [[InstrumentationOperator.ghostVars]].
   *                   There will be
   *                   [[InstrumentationOperatorApplier.numGhostRanges]] such
   *                   collections.
   * @param exqInfo Information extracted from the application of
   *                [[ExtendedQuantifier.morphism]].
   */
  def rewriteAggregate(
    ghostTerms              : Seq[Map[GhostVar, ITerm]],
    exqInfo                 : ExtendedQuantifierApp) : Seq[RewriteRules.Result]
}

object InstrumentationOperator {
  class GhostVar(val sort : Sort, val name : String) {
    override def toString : String = name
  }
}

abstract class InstrumentationOperator(val exq : ExtendedQuantifier)
  extends RewriteRules {
  import InstrumentationOperator.GhostVar

  /**
   * These are the ghost variables of the extended quantifier.
   * There will be [[InstrumentationOperatorApplier.numGhostRanges]] such
   * sequences of ghost variables.
   * Sometimes we might want additional ghost variables that are not directly
   * related to the extended quantifier (such as alien terms). For simplicity,
   * these should be declared as part of below ghostVars. As a result, these
   * terms will be needlessly duplicated when `numGhostRanges > 1`.
   *
   * @todo Check if Eldarica's other preprocessors slice away such copies.
   */
  val ghostVars : Seq[GhostVar]

  /**
   * Initial values for `ghostVars`.
   * If an initial value is not found for a GhostVar, it is left uninitialized.
   */
  val ghostVarInitialValues : Map[GhostVar, ITerm]

  /**
   * Each instrumentation operator is initially assigned one set of ghost
   * variables. If `maxSupportedGhostVarRanges` is set to a value other than 1,
   * if the result is `Inconclusive` the number of ghost variable sets is
   * incremented by one, at most until `maxSupportedGhostVarRanges`.
   * If a value other than `1` is specified,
   * [[InstrumentationOperator.rewriteAggregate]] should handle the combining
   * values coming from multiple sets of ghost variables. Other rewrite rules
   * do not require special treatment, as they each rule will automatically be
   * applied once per ghost variable set, per extended quantifier application.
   * @todo This is currently ignored, refactor to consider it.
   */
  val maxSupportedGhostVarRanges : Int = 1

  /**
   * Given a map from ghost variables to terms, this should construct a formula
   * using those terms and [[exq.morphism]]. This is later used when
   * back-translating solutions in [[GhostVariableAdder]] to eliminate
   * ghost variables.
   */
  def ghostVarsToAggregateFormula(ghostTerms : Map[GhostVar, ITerm]) : IFormula
}



