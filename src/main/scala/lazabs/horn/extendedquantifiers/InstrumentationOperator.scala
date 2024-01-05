package lazabs.horn.extendedquantifiers

import ap.parser._
import ap.types.Sort
import lazabs.horn.extendedquantifiers.Util.{ConstInfo, ExtendedQuantifierApp, SelectInfo, StoreInfo}
import sun.reflect.generics.reflectiveObjects.NotImplementedException

object RewriteRules {
  case class Result(newConjunct     : IFormula,
                    rewriteFormulas : Map[IFormula, IFormula],
                    assertions      : Seq[IFormula])
}

abstract class GhostVar(val sort : Sort)

trait RewriteRules {
  // These rules are hardcoded as the array operations, but with some effort
  // the methods could also be generalized to a map from theory functions to
  // rewrite rules.

  /**
   * `oldGhostTerms` and `newGhostTerms` are the old and new values of ghost
   * variables defined in [[InstrumentationOperator.ghostVars]].
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
  def rewriteAggregate(ghostTerms : Seq[Map[GhostVar, ITerm]],
                       exqInfo    : ExtendedQuantifierApp) : Seq[RewriteRules.Result]
}

abstract class InstrumentationOperator(val exq : ExtendedQuantifier)
  extends RewriteRules {
  val ghostVars : Seq[GhostVar]
  /**
   * Initial values for the ghost variables. If an initial value is not found
   * for a GhostVar, it is not initialized to any value.
   */
  val ghostVarInitialValues : Map[GhostVar, ITerm]
}



