/**
 * Copyright (c) 2024 Zafer Esen, Philipp Ruemmer. All rights reserved.
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
package lazabs.horn.symex

import ap.basetypes.IdealInt
import ap.terfor.{ComputationLogger, ConstantTerm, Term, TermOrder}
import ap.terfor.arithconj.ModelElement
import ap.terfor.conjunctions.{ConjunctEliminator, Conjunction}
import ap.terfor.equations.NegEquationConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.substitutions.ConstantSubst

/**
 * Takes a constraint and a set of local symbols that can safely be eliminated.
 * If reduceBeforeSimplification is true, the symbol factory's reducer will
 * be first applied to the constraint before attempting simplification.
 */
trait ConstraintSimplifier {
  def simplifyConstraint(constraint                 : Conjunction,
                         localSymbols               : Set[Term],
                         reduceBeforeSimplification : Boolean)
           (implicit symex_sf : SymexSymbolFactory) : Conjunction
}

/**
 * An implementation of ConstraintSimplifier based on ConjunctEliminator.
 */
trait ConstraintSimplifierUsingConjunctEliminator extends ConstraintSimplifier {

  class LocalSymbolEliminator(constraint   : Conjunction,
                              localSymbols : Set[Term],
                              order        : TermOrder)
      extends ConjunctEliminator(constraint, localSymbols, Set(), order) {

    var divJudgements : List[Conjunction] = List()

    override protected def nonUniversalElimination(f : Conjunction) = {}

    // todo: check if this eliminates function applications
    //   e.g., unused select and stores

    protected def universalElimination(m : ModelElement): Unit = {}

    override protected def addDivisibility(f : Conjunction) =
      divJudgements = f :: divJudgements

    override protected def isEliminationCandidate(t : Term) : Boolean =
      localSymbols contains t

    override protected def eliminationCandidates(
        constraint: Conjunction) : Iterator[Term] = localSymbols.iterator

  }

  private def inlineLocalEquations(constraint   : Conjunction,
                                   localSymbols : Set[Term],
                                   order        : TermOrder) : Conjunction = {
    // the first equation defining a local symbol with coefficient 1 or -1
    def findDefinedLocal(conj : Conjunction)
        : Option[(IdealInt, ConstantTerm, LinearCombination)] = {
      val candidates =
        for (lc <- conj.arithConj.positiveEqs.iterator;
             (coeff, c : ConstantTerm) <- lc.pairIterator
               if coeff.isUnit && (localSymbols contains c))
          yield (coeff, c, lc)
      if (candidates.hasNext) Some(candidates.next()) else None
    }

    @annotation.tailrec
    def inlineAll(conj : Conjunction) : Conjunction =
      findDefinedLocal(conj) match {
        case Some((coeff, c, lc)) =>
          // lc is coeff * c + t = 0 with coeff being 1 or -1, so
          // c = -t / coeff = -coeff * t, which equals -coeff * lc + c
          val replacement =
            LinearCombination.sum(-coeff, lc,
                                  IdealInt.ONE, LinearCombination(c, order),
                                  order)
          inlineAll(ConstantSubst(c, replacement, order)(conj))
        case None => conj
      }

    inlineAll(constraint)
  }

  /**
   * Drop local symbols whose occurrences are only inequalities with
   * constant bounds and disequalities
   * e.g.,
   * x >= 1 & 0 <= c <= 3 & c != x
   * the range is 4, one disequality forbids at most 1, c can be dropped
   *
   * x >= 1 & 0 <= c <= 1 & c != x & c != x - 1
   * for x = 1 two disequalities cover the whole range, no drop
   */
  private def dropRangeConstrainedLocals(constraint   : Conjunction,
                                         localSymbols : Set[Term],
                                         order        : TermOrder) : Conjunction = {

    def droppable(conj : Conjunction, c : ConstantTerm) : Boolean = {
      val arith    = conj.arithConj
      val bounds   = arith.inEqs filter (_.constants contains c)
      val diseqs   = arith.negativeEqs filter (_.constants contains c)

      val occursElsewhere =
        (arith.positiveEqs.constants contains c) ||
        (conj.predConj.constants contains c) ||
        (conj.negatedConjs.constants contains c)

      // every inequality on c must mention only c with coeff 1 or -1
      // nothing on c may contain bound variables
      val boundsAreClean = bounds forall (lc =>
        lc.constants == Set(c) && (lc get c).isUnit && lc.variables.isEmpty)
      val diseqsAreClean = diseqs forall (_.variables.isEmpty)

      // each inequality is coeff * c + offset >= 0
      def rangeExceeds(count : Int) : Boolean = {
        val lower = (bounds collect {
          case lc if (lc get c).isOne =>
            -lc.constant }) reduceOption (_ max _)
        val upper = (bounds collect {
          case lc if (lc get c).isMinusOne =>
            lc.constant }) reduceOption (_ min _)
        (lower, upper) match {
          case (Some(lo), Some(hi)) =>
            hi - lo + IdealInt.ONE > IdealInt(count)
          case _ =>
            true // unbounded on one side
        }
      }
      !occursElsewhere && boundsAreClean && diseqsAreClean &&
        rangeExceeds(diseqs.size)
    }

    def dropConstraintsOn(conj : Conjunction, c : ConstantTerm) : Conjunction =
      conj.updateInEqs(InEqConj(
            conj.arithConj.inEqs.iterator filterNot (_.constants contains c),
            order))(order)
          .updateNegativeEqs(NegEquationConj(
            conj.arithConj.negativeEqs.iterator filterNot (_.constants contains c),
            order))(order)

    val localConstants = localSymbols collect { case c : ConstantTerm => c }

    // repeat until nothing more can be dropped
    @annotation.tailrec
    def dropAll(conj : Conjunction) : Conjunction = localConstants find (c =>
      (conj.constants contains c) && droppable(conj, c)) match {
      case Some(c) => dropAll(dropConstraintsOn(conj, c))
      case None    => conj
    }
    dropAll(constraint)
  }

  override def simplifyConstraint(constraint                 : Conjunction,
                                  localSymbols               : Set[Term],
                                  reduceBeforeSimplification : Boolean)
                    (implicit symex_sf : SymexSymbolFactory) : Conjunction = {
    val reducedConstraint =
      if (reduceBeforeSimplification)
        symex_sf.reducer(Conjunction.TRUE)(constraint)
      else constraint

    if (constraint.negatedConjs.isEmpty) {
      /**
       * If the constraint is a conjunction, we can use the
       * [[ConjunctEliminator]] class for simplification.
       */
      val inlined = inlineLocalEquations(
        reducedConstraint, localSymbols, symex_sf.order)
      val dropped = dropRangeConstrainedLocals(
        inlined, localSymbols, symex_sf.order)
      val eliminator  = new LocalSymbolEliminator(
        dropped, localSymbols, symex_sf.order)
      val eliminated  = eliminator.eliminate(ComputationLogger.NonLogger)
      if (eliminator.divJudgements isEmpty)
        eliminated
      else
        Conjunction.conj(
          eliminated :: eliminator.divJudgements.map(_.negate), symex_sf.order)
    } else {
      /**
       * If there are disjunctions, then try another method of
       * simplification.
       */
      // quantify local symbols
      val sortedLocalSymbols =
        symex_sf.order.sort(localSymbols.map(_.asInstanceOf[ConstantTerm]))
      val quanF = Conjunction.quantify(ap.terfor.conjunctions.Quantifier.EX,
                                       sortedLocalSymbols,
                                       constraint, constraint.order)

      // try to eliminate the quantified vars
      val reducedQuanF : Conjunction =
        symex_sf.reducer(Conjunction.TRUE).apply(quanF)

      // re-introduce local symbols only for the outermost exists
      val exBlockSize =
        reducedQuanF.quans.reverse.takeWhile(
          _ == ap.terfor.conjunctions.Quantifier.EX).size
      val numToInstantiate = exBlockSize min sortedLocalSymbols.size

      reducedQuanF.instantiate(
        sortedLocalSymbols take numToInstantiate)(reducedQuanF.order)
    }
  }
}
