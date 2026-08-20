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
import ap.terfor.preds.{Atom, Predicate}
import ap.terfor.substitutions.ConstantSubst
import ap.theories.bitvectors.ModuloArithmetic
import ap.types.{Sort, SortedPredicate}

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

  // c used anywhere outside argument position pos of atom a
  private def usedOutsideAtomArg(conj : Conjunction,
                                 a    : Atom,
                                 pos  : Int,
                                 c    : ConstantTerm) : Boolean =
    ((0 until a.length) exists (i =>
       i != pos && (a(i).constants contains c))) || // not in other args of atom
    (conj.arithConj.positiveEqs.constants contains c) || // eqs
    (conj.arithConj.negativeEqs.constants contains c) || // diseqs
    (conj.negatedConjs.constants contains c) || // disjs
    (conj.predConj.positiveLits exists (b =>    // other atoms
       !(b eq a) && (b.constants contains c))) ||
    (conj.predConj.negativeLits exists (_.constants contains c))

  // the constant bounds of c, when every inequality on c mentions only
  // c with coeff 1 or -1 and contains no bound variables; None otherwise
  // each inequality is coeff * c + offset >= 0
  private def constantBoundsOf(conj : Conjunction, c : ConstantTerm)
      : Option[(Option[IdealInt], Option[IdealInt])] = {
    val bounds = conj.arithConj.inEqs filter (_.constants contains c)
    val clean = bounds forall (lc =>
      lc.constants == Set(c) && (lc get c).isUnit && lc.variables.isEmpty)
    if (!clean) None
    else Some((
      (bounds collect {
        case lc if (lc get c).isOne => -lc.constant }) reduceOption (_ max _),
      (bounds collect {
        case lc if (lc get c).isMinusOne => lc.constant }) reduceOption (_ min _)))
  }

  // remove every equ, ineq, diseq and atom containing c and add the given ineqs
  private def removeConstraintsOn(conj       : Conjunction,
                                  c          : ConstantTerm,
                                  addedInEqs : Iterator[LinearCombination],
                                  order      : TermOrder) : Conjunction = {
    val (_, remainingLits) =
      conj.predConj partition (_.constants contains c)
    conj.updateInEqs(InEqConj(
          (conj.arithConj.inEqs.iterator filterNot (_.constants contains c)) ++
            addedInEqs, order))(order)
        .updateNegativeEqs(NegEquationConj(
          conj.arithConj.negativeEqs.iterator filterNot (_.constants contains c),
          order))(order)
        .updatePredConj(remainingLits)(order)
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

    def canDrop(conj : Conjunction, c : ConstantTerm) : Boolean = {
      val diseqs = conj.arithConj.negativeEqs filter (_.constants contains c)

      val occursElsewhere =
        (conj.arithConj.positiveEqs.constants contains c) ||
        (conj.predConj.constants contains c) ||
        (conj.negatedConjs.constants contains c)
      val diseqsAreClean = diseqs forall (_.variables.isEmpty)

      !occursElsewhere && diseqsAreClean &&
      (constantBoundsOf(conj, c) match {
        case Some((Some(lo), Some(hi))) =>
          hi - lo + IdealInt.ONE > IdealInt(diseqs.size)
        case Some(_) => true  // unbounded on one side
        case None    => false // an ineq on c is not a plain bound
      })
    }

    val localConstants = localSymbols collect { case c : ConstantTerm => c }

    // repeat until nothing more can be dropped
    @annotation.tailrec
    def dropAll(conj : Conjunction) : Conjunction = localConstants find (c =>
      (conj.constants contains c) && canDrop(conj, c)) match {
      case Some(c) => dropAll(removeConstraintsOn(conj, c, Iterator.empty, order))
      case None    => conj
    }
    dropAll(constraint)
  }

  /**
   * Drop atoms of total functions, e.g. mod_cast, whose result is a
   * local used nowhere else
   */
  private def dropUnusedFunctionAtoms(constraint    : Conjunction,
                                      localSymbols  : Set[Term],
                                      functionPreds : Set[Predicate],
                                      order         : TermOrder) : Conjunction = {

    // the last argument must exactly be one symbol with coeff 1
    def resultSymbol(a : Atom) : Option[ConstantTerm] =
      if (a.last.size == 1 && (a.last getCoeff 0).isOne)
        a.last getTerm 0 match {
          case c : ConstantTerm => Some(c)
          case _ => None
        }
      else None

    def sortRange(s : Sort) : (Option[IdealInt], Option[IdealInt]) = s match {
      case ModuloArithmetic.ModSort(lower, upper) => (Some(lower), Some(upper))
      case Sort.Interval(lower, upper) => (lower, upper)
      case _ => (None, None)
    }

    // every ineq on c must be implied by the sort of the res of a
    // e.g., c ≤ 255 with sort 0..255 passes for 255; fails for c ≤ 3
    def boundsAreVacuous(conj : Conjunction, a : Atom,
                         c : ConstantTerm) : Boolean = {
      val (lower, upper) = sortRange(SortedPredicate.argumentSorts(a).last)
      conj.arithConj.inEqs forall { lc =>
        !(lc.constants contains c) || {
          val coeff = lc get c
          lc.constants == Set(c) && lc.variables.isEmpty &&
          (if (coeff.signum > 0)
             lower exists (b => coeff * b + lc.constant >= 0)
           else
             upper exists (b => coeff * b + lc.constant >= 0))
        }
      }
    }

    // c used nowhere else
    def canDrop(conj : Conjunction, a : Atom, c : ConstantTerm) : Boolean =
      !usedOutsideAtomArg(conj, a, a.length - 1, c) &&
      boundsAreVacuous(conj, a, c)

    def findDroppable(conj : Conjunction) : Option[(Atom, ConstantTerm)] =
      (for (a <- conj.predConj.positiveLits.iterator
              if functionPreds contains a.pred;
            c <- resultSymbol(a).iterator
              if (localSymbols contains c) && canDrop(conj, a, c))
         yield (a, c)).toStream.headOption

    @annotation.tailrec
    def dropAll(conj : Conjunction) : Conjunction =
      findDroppable(conj) match {
        case Some((_, c)) => dropAll(removeConstraintsOn(conj, c, Iterator.empty, order))
        case None => conj
      }
    dropAll(constraint)
  }

  /**
   * Replace unnecessary mod_cast atoms
   * i.e., whose arg contains a local used nowhere else
   * e.g.,
   * mod_cast(0, 15, a, r)  &  0 ≤ a ≤ 255  --> 0 ≤ r ≤ 15
   * mod_cast(0, 15, a, r)  &  0 ≤ a ≤ 7    --> 0 ≤ r ≤ 7
   * mod_cast(0, 15, a, r)  &  14 ≤ a ≤ 17  --> no change
   */
  private def dropFreeArgumentCasts(constraint   : Conjunction,
                                    localSymbols : Set[Term],
                                    order        : TermOrder) : Conjunction = {

    // floor div (also for negative numbers)
    def floorDiv(x : IdealInt, m : IdealInt) : IdealInt = {
      val q = x / m
      if ((x - q * m).signum < 0) q - IdealInt.ONE else q
    }

    def replacement(conj : Conjunction, a : Atom)
        : Option[(ConstantTerm, IdealInt, IdealInt)] = {
      if (!(a(0).isConstant && a(1).isConstant)) return None // range must be concrete
      val loV = a(0).constant
      val hiV = a(1).constant
      val m = hiV - loV + IdealInt.ONE

      val arg = a(2)
      val candidate = arg.pairIterator collectFirst {
        case (coeff, c : ConstantTerm)
            if coeff.isUnit && (localSymbols contains c) => (coeff, c) // arg with coeff +-1
      }
      candidate flatMap { case (coeff, c) =>
        if (usedOutsideAtomArg(conj, a, 2, c) || arg.variables.nonEmpty)
          None
        else constantBoundsOf(conj, c) flatMap { case (lower, upper) =>
          val fullPeriod = (lower, upper) match {
            case (Some(lo), Some(hi)) => hi - lo + IdealInt.ONE >= m
            case _                    => true // unbounded on a side
          }
          val restIsConstant = arg.constants == Set(c)

          if (fullPeriod)
            Some((c, loV, hiV))
          else if (restIsConstant) {
            // the argument values are the interval [ilo, ihi]
            val (Some(clo), Some(chi)) = (lower, upper)
            val rest = arg.constant
            val (ilo, ihi) =
              if (coeff.isOne) (rest + clo, rest + chi)
              else (rest - chi, rest - clo)
            val shift = floorDiv(ilo - loV, m) * m
            val rlo   = ilo - shift
            val rhi   = ihi - shift
            if (rhi <= hiV) Some((c, rlo, rhi))
            else None
          } else None
        }
      }
    }

    def findReplaceable(conj : Conjunction)
        : Option[(Atom, ConstantTerm, IdealInt, IdealInt)] =
      (for (a <- conj.predConj.positiveLits.iterator
              if a.pred == ModuloArithmetic._mod_cast;
            (c, rlo, rhi) <- replacement(conj, a).iterator)
         yield (a, c, rlo, rhi)).toStream.headOption

    def applyReplacement(conj : Conjunction, c : ConstantTerm,
                         a : Atom, rlo : IdealInt, rhi : IdealInt)
        : Conjunction = {
      // rlo <= result and result <= rhi
      val resultBounds = Iterator(
        LinearCombination.sum(IdealInt.ONE, a.last,
                              IdealInt.ONE, LinearCombination(-rlo), order),
        LinearCombination.sum(IdealInt.MINUS_ONE, a.last,
                              IdealInt.ONE, LinearCombination(rhi), order))
      removeConstraintsOn(conj, c, resultBounds, order)
    }

    @annotation.tailrec
    def dropAll(conj : Conjunction) : Conjunction =
      findReplaceable(conj) match {
        case Some((a, c, rlo, rhi)) =>
          dropAll(applyReplacement(conj, c, a, rlo, rhi))
        case None => conj
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
      val stages : List[Conjunction => Conjunction] = List(
        inlineLocalEquations(_, localSymbols, symex_sf.order),
        dropRangeConstrainedLocals(_, localSymbols, symex_sf.order),
        dropUnusedFunctionAtoms(_, localSymbols,
          ModuloArithmetic.functionalPredicates, symex_sf.order),
        dropFreeArgumentCasts(_, localSymbols, symex_sf.order))

      @annotation.tailrec
      def runStages(conj : Conjunction) : Conjunction = {
        val next = stages.foldLeft(conj)((c, stage) => stage(c))
        if (next eq conj) conj else runStages(next)
      }
      val dropped = runStages(reducedConstraint)
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
