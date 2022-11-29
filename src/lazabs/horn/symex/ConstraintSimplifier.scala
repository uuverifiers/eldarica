package lazabs.horn.symex

import ap.terfor.{ComputationLogger, Term, TermOrder}
import ap.terfor.arithconj.ModelElement
import ap.terfor.conjunctions.{
  ConjunctEliminator,
  Conjunction,
  ReduceWithConjunction
}

// todo: should get the unit clause
// todo: argument variables should be part of the arguments
trait ConstraintSimplifier {
  def simplifyConstraint(constraint: Conjunction, localSymbols: Set[Term])(
      implicit symex_sf:             SymexSymbolFactory): Conjunction
}

// todo: keep all variables
trait NaiveConstraintSimplifier extends ConstraintSimplifier {

  class LocalSymbolEliminator(constraint:   Conjunction,
                              localSymbols: Set[Term],
                              order:        TermOrder)
      extends ConjunctEliminator(constraint, localSymbols, Set(), order) {

    override protected def nonUniversalElimination(f: Conjunction) = {
      ???
    }

    // can eliminate function applications if unused // e.g., eliminate unused select and stores

    protected def universalElimination(m: ModelElement): Unit = {} //???

    override protected def addDivisibility(f: Conjunction) = // todo: ?
      divJudgements = f :: divJudgements

    var divJudgements: List[Conjunction] = List()

    override protected def isEliminationCandidate(t: Term): Boolean =
      localSymbols contains t

    override protected def eliminationCandidates(
        constraint: Conjunction): Iterator[Term] = localSymbols.iterator

  }

  override def simplifyConstraint(constraint:   Conjunction,
                                  localSymbols: Set[Term])(
      implicit symex_sf:                        SymexSymbolFactory): Conjunction = {
    //t todo: move reducer outside?
    //   also add option to disable reducer, would be useful while debugging.
    val redConj = symex_sf.reducer(Conjunction.TRUE)(constraint)
    //println("\nBefore: " + Conjunction.conj(constraint, order))
    val simpConj =
      new LocalSymbolEliminator(redConj, localSymbols, symex_sf.order)
        .eliminate(ComputationLogger.NonLogger)
    //println("After : " + simpConj + "\n")
    simpConj
  }
}
