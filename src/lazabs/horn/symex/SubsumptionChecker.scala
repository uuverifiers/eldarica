package lazabs.horn.symex

trait SubsumptionChecker {
  // returns: cuc is subsumed by some clauses in the unitClauseDB
  def checkForwardSubsumption(cuc:          UnitClause,
                              unitClauseDB: UnitClauseDB): Boolean

  // returns: a set of cucs subsumed by this cuc that are in the unitClauseDB
  def checkBackwardSubsumption(
      cuc:          UnitClause,
      unitClauseDB: UnitClauseDB
  ): Set[UnitClause]
}

trait SimpleSubsumptionChecker extends SubsumptionChecker {

  import Symex._

  override def checkForwardSubsumption(cuc:          UnitClause,
                                       unitClauseDB: UnitClauseDB): Boolean = {
    false
  }

  override def checkBackwardSubsumption(
      cuc:          UnitClause,
      unitClauseDB: UnitClauseDB
  ): Set[UnitClause] = {
    //unitClauseDB
    //  .inferredCUCsForPred(cuc.pred)
    //  .filter(existingCuc => cuc subsumes existingCuc)
    //  .toSet
    Set()
  }
}
