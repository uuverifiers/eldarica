package lazabs.horn.symex

import ap.terfor.{ComputationLogger, Term, TermOrder}
import ap.terfor.arithconj.ModelElement
import ap.terfor.conjunctions.{ConjunctEliminator, Conjunction}

trait ConstraintSimplifier {
  def simplifyConstraint(constraint:                 Conjunction,
                         localSymbols:               Set[Term],
                         reduceBeforeSimplification: Boolean)(
      implicit symex_sf:                             SymexSymbolFactory): Conjunction
}

trait ConstraintSimplifierUsingConjunctEliminator extends ConstraintSimplifier {

  class LocalSymbolEliminator(constraint:   Conjunction,
                              localSymbols: Set[Term],
                              order:        TermOrder)
      extends ConjunctEliminator(constraint, localSymbols, Set(), order) {

    override protected def nonUniversalElimination(f: Conjunction) = {}

    // todo: check if this eliminates function applications
    //   e.g., unused select and stores

    protected def universalElimination(m: ModelElement): Unit = {}

    override protected def addDivisibility(f: Conjunction) =
      divJudgements = f :: divJudgements

    var divJudgements: List[Conjunction] = List()

    override protected def isEliminationCandidate(t: Term): Boolean =
      localSymbols contains t

    override protected def eliminationCandidates(
        constraint: Conjunction): Iterator[Term] = localSymbols.iterator

  }

  override def simplifyConstraint(constraint:                 Conjunction,
                                  localSymbols:               Set[Term],
                                  reduceBeforeSimplification: Boolean)(
      implicit symex_sf:                                      SymexSymbolFactory): Conjunction = {
    val reducedConstraint =
      if (reduceBeforeSimplification)
        symex_sf.reducer(Conjunction.TRUE)(constraint)
      else constraint

    new LocalSymbolEliminator(reducedConstraint, localSymbols, symex_sf.order)
      .eliminate(ComputationLogger.NonLogger)
  }
}
