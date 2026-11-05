/**
 * Copyright (c) 2024-2026 Zafer Esen, Philipp Ruemmer. All rights reserved.
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
import ap.terfor.{ComputationLogger, ConstantTerm, OneTerm, Term, TermOrder}
import ap.terfor.arithconj.ModelElement
import ap.terfor.conjunctions.{ConjunctEliminator, Conjunction}
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.{Atom, Predicate}
import ap.terfor.substitutions.ConstantSubst
import ap.theories.bitvectors.ModuloArithmetic
import ap.types.{Sort, SortedPredicate}

import scala.collection.immutable.BitSet

/**
 * Simplification of constraints, based on ConjunctEliminator.
 */
class ConstraintSimplifier(implicit symex_sf : SymexSymbolFactory) {

  // logging
  private val collectStats  = lazabs.GlobalParameters.get.log
  private val stageFires    = collection.mutable.LinkedHashMap[String, Long]()
  private var stageRounds   = 0L
  private var simplifyNanos = 0L
  private var inSimplify    = false

  def timeNanos : Long = simplifyNanos

  def stats : Option[String] =
    if (!collectStats) None
    else Some(s"simplifier: $stageRounds rounds: " +
              (stageFires map { case (name, n) => s"$name $n" } mkString ", "))

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

    // sorted so that elimination is deterministic
    private val sortedCandidates =
      order.sort(localSymbols collect { case c : ConstantTerm => c })

    override protected def eliminationCandidates(constraint : Conjunction)
    : Iterator[Term] = sortedCandidates.iterator
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
  // c with coeff 1 or -1 and contains no bound variables. None otherwise
  // each inequality is coeff * c + offset >= 0
  private def constantBoundsOf(conj : Conjunction, c : ConstantTerm)
      : Option[(Option[IdealInt], Option[IdealInt])] = {
    val bounds = conj.arithConj.inEqs filter (_.constants contains c)
    val clean = bounds forall (lc =>
      lc.constants == Set(c) &&  // only c is mentioned
        (lc get c).isUnit &&     // c is unit
        lc.variables.isEmpty)    // no bound vars
    if (!clean) None
    else {
      val lowers = bounds collect { case lc if (lc get c).isOne => -lc.constant }
      val uppers = bounds collect { case lc if (lc get c).isMinusOne => lc.constant }
      Some((lowers reduceOption (_ max _), uppers reduceOption (_ min _))) // greatest lower and least upper bound
    }
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

  // the symbol of a linear combination that is exactly a single symbol with
  // coeff 1. None for anything else
  private def singleSymbol(lc : LinearCombination) : Option[ConstantTerm] =
    if (lc.size == 1 && (lc getCoeff 0).isOne)
      lc getTerm 0 match {
        case c : ConstantTerm => Some(c)
        case _ => None
      }
    else None

  // bounds implied by ineqs that mention only c
  // ignores if another symbol is mentioned / coeff not unit / under quan
  private def impliedBounds(conj : Conjunction, c : ConstantTerm)
  : (Option[IdealInt], Option[IdealInt]) = {
    val single = conj.arithConj.inEqs filter (lc =>
      lc.constants == Set(c) &&  // only c is mentioned
        (lc get c).isUnit &&     // c is unit
        lc.variables.isEmpty)    // no bound vars
    val lowers = single collect { case lc if (lc get c).isOne => -lc.constant }
    val uppers = single collect { case lc if (lc get c).isMinusOne => lc.constant }
    (lowers reduceOption (_ max _), uppers reduceOption (_ min _)) // greatest lower and least upper bound
  }

  // checks that x has no bits above bit
  // i.e., x is within [0, 2^(bit+1) - 1]
  private def hasNoBitsAbove(conj : Conjunction,
                             x    : ConstantTerm,
                             bit  : Int) : Boolean = {
    val (lo, hi) = impliedBounds(conj, x)
    (lo exists (_.signum >= 0)) &&
    (hi exists (_ <= IdealInt.pow2MinusOne(bit + 1)))
  }

  /**
   * Replace an extract with a constant result by the interval it denotes
   * when the extractee has no bits above the slice.
   * e.g., for 0 <= x <= 255
   * x[7:4] = 3  -->  48 <= x <= 63     (3*16 <= x < 4*16, bits 3..0 free)
   * x[7:4] = 0  -->  0 <= x <= 15      (tighter bound, can make the next slice replaceable)
   */
  private def linearizeConstantSlices(constraint : Conjunction,
                                      order      : TermOrder) : Conjunction = {

    // the first extract x[hi:lo] = k where hi, lo and k are concrete
    // and x is a single symbol with no bits above hi
    def findConstantSlice(conj : Conjunction) : Option[(Atom, ConstantTerm)] = {
      val candidates =
        for (a <- conj.predConj.positiveLits.iterator;
             if a.pred == ModuloArithmetic._bv_extract;
             if a(0).isConstant && a(1).isConstant && a.last.isConstant;
             x <- singleSymbol(a(2)).iterator;
             if hasNoBitsAbove(conj, x, a(0).constant.intValueSafe))
          yield (a, x)
      if (candidates.hasNext) Some(candidates.next()) else None
    }

    // replace x[hi:lo] = k by the interval
    // k*2^lo <= x <= k*2^lo + 2^lo - 1
    // a k that does not fit in hi-lo+1 is a shortcut false
    def replaceOne(conj : Conjunction, a : Atom,
                   x : ConstantTerm) : Conjunction = {
      val hi = a(0).constant.intValueSafe
      val lo = a(1).constant.intValueSafe
      val k  = a.last.constant
      val kFitsSlice =
        k.signum >= 0 && k <= IdealInt.pow2MinusOne(hi - lo + 1)
      if (!kFitsSlice)
        Conjunction.FALSE
      else {
        val lower = k * IdealInt.pow2(lo)
        val upper = lower + IdealInt.pow2MinusOne(lo)
        val xMinusLower =           // x - lower >= 0
          LinearCombination.sum(IdealInt.ONE, LinearCombination(x, order),
                                IdealInt.ONE, LinearCombination(-lower), order)
        val upperMinusX =           // upper - x >= 0
          LinearCombination.sum(IdealInt.MINUS_ONE, LinearCombination(x, order),
                                IdealInt.ONE, LinearCombination(upper), order)
        val (_, remainingLits) = conj.predConj partition (_ eq a)
        Conjunction.conj(
          List(conj.updatePredConj(remainingLits)(order),
               InEqConj(Iterator(xMinusLower, upperMinusX), order)),
          order)
      }
    }

    @annotation.tailrec
    def replaceAll(conj : Conjunction) : Conjunction =
      findConstantSlice(conj) match {
        case Some((a, x)) => replaceAll(replaceOne(conj, a, x))
        case None         => conj
      }

    replaceAll(constraint)
  }

  /**
   * Replace a complete set of extracts over one symbol by a linear eq.
   * e.g., for 0 <= x <= 255
   * x[7:1] = a & x[0:0] = b  -->  x = 2*a + b & 127 >= a >= 0 & 1 >= b >= 0
   */
  private def recomposeExtracts(constraint : Conjunction,
                                order      : TermOrder) : Conjunction = {

    // one extract slice x[hi:lo] = sliceValue
    case class Slice(hi : Int, lo : Int, atom : Atom)

    // slices covering bits T..0 with every bit in exactly one slice
    // among such covers the one reaching the highest T wins
    // e.g., from x[7:4], x[3:0], x[5:2] the cover is x[7:4], x[3:0]
    def coveringSlices(slices : Seq[Slice]) : Option[List[Slice]] = {
      // covers(hi) is a cover of the bits hi..0
      // a slice with lo = 0 starts a cover. other slices extend a
      // cover that ends right below them
      var covers = Map[Int, List[Slice]]()
      for (s <- slices sortBy (_.lo)) {
        val extendsSomeCover = s.lo == 0 || (covers contains (s.lo - 1))
        if (extendsSomeCover && !(covers contains s.hi))
          covers = covers + (s.hi -> (s :: covers.getOrElse(s.lo - 1, Nil)))
      }
      if (covers.isEmpty) None
      else Some(covers(covers.keysIterator.max))
    }

    // the first extractee x whose slices contain a cover of bits
    // T..0 where x has no bits above T. only the largest cover is tried.
    def findRecomposable(conj : Conjunction)
        : Option[(ConstantTerm, List[Slice])] = {
      val extractAtoms = conj.predConj.positiveLits filter (a =>
        a.pred == ModuloArithmetic._bv_extract &&
          a(0).isConstant && a(1).isConstant)
      def slicesOf(x : ConstantTerm) : Seq[Slice] =
        for (a <- extractAtoms; if singleSymbol(a(2)) contains x)
          yield Slice(a(0).constant.intValueSafe,
                      a(1).constant.intValueSafe, a)
      val extractees = (extractAtoms flatMap (a => singleSymbol(a(2)))).distinct
      val candidates =
        for (x <- extractees.iterator;
             cover <- coveringSlices(slicesOf(x)).iterator;
             if hasNoBitsAbove(conj, x, cover.head.hi))
          yield (x, cover)
      if (candidates.hasNext) Some(candidates.next()) else None
    }

    // replace the cover's atoms by x = sum of 2^lo * sliceValue and
    // the bounds 0 <= sliceValue <= 2^(hi-lo+1) - 1 for every sliceValue
    // the extractee's own bounds stay untouched
    def recompose(conj  : Conjunction,
                  x     : ConstantTerm,
                  cover : List[Slice]) : Conjunction = {
      val weightedSliceValues = cover map (s => (-IdealInt.pow2(s.lo), s.atom.last))
      val eq = LinearCombination.sum(
        (IdealInt.ONE, LinearCombination(x, order)) :: weightedSliceValues, order)
      val sliceValueBounds = cover flatMap { s =>
        val widthMax = LinearCombination(IdealInt.pow2MinusOne(s.hi - s.lo + 1))
        List(s.atom.last,           // sliceValue >= 0
             LinearCombination.sum( // 2^width - 1 - sliceValue >= 0
               IdealInt.MINUS_ONE, s.atom.last,
               IdealInt.ONE, widthMax, order))
      }
      val coverAtoms = cover map (_.atom)
      val (_, remainingLits) = conj.predConj partition (coverAtoms contains _)
      Conjunction.conj(
        List(conj.updatePredConj(remainingLits)(order),
             EquationConj(eq, order),
             InEqConj(sliceValueBounds.iterator, order)),
        order)
    }

    @annotation.tailrec
    def recomposeAll(conj : Conjunction) : Conjunction =
      findRecomposable(conj) match {
        case Some((x, cover)) => recomposeAll(recompose(conj, x, cover))
        case None             => conj
      }

    recomposeAll(constraint)
  }

  private def inlineLocalEquations(constraint   : Conjunction,
                                   localSymbols : Set[Term],
                                   order        : TermOrder) : Conjunction = {
    // the definitions of local symbols by equations with coefficient 1 or
    // -1 in one pass over the equations, each definition applied to the
    // later equations and to the earlier definitions
    def definitionsOf(conj : Conjunction)
        : Map[ConstantTerm, LinearCombination] =
      (Map[ConstantTerm, LinearCombination]() /:
         conj.arithConj.positiveEqs) { (definitions, eq) =>
        val lc = ConstantSubst(definitions, order)(eq)
        lc.pairIterator collectFirst {
          case (coeff, c : ConstantTerm)
              if coeff.isUnit && (localSymbols contains c) => (coeff, c)
        } match {
          case Some((coeff, c)) =>
            // lc is coeff * c + t = 0 with coeff being 1 or -1, so
            // c = -t / coeff = -coeff * t, which equals -coeff * lc + c
            val replacement =
              LinearCombination.sum(-coeff, lc,
                                    IdealInt.ONE, LinearCombination(c, order),
                                    order)
            val subst = ConstantSubst(c, replacement, order)
            (definitions map { case (d, t) => (d, subst(t)) }) +
              (c -> replacement)
          case None => definitions
        }
      }

    @annotation.tailrec
    def inlineAll(conj : Conjunction) : Conjunction = {
      val definitions = definitionsOf(conj)
      if (definitions.isEmpty) conj
      else inlineAll(ConstantSubst(definitions, order)(conj))
    }

    inlineAll(constraint)
  }

  /**
   * Drop inequalities implied by a nonnegative combination of two other inequalities.
   * E.g.,
   * -2a - 2b - c - 10 >= 0 & -c + 9999 >= 0 & -a - b - c + 9996 >= 0
   * half the sum of the first two is -a - b - c + 4994 >= 0, which
   * implies the third
   */
  private def dropImpliedInEqs(constraint : Conjunction,
                               order      : TermOrder) : Conjunction = {
    val inEqs   = constraint.arithConj.inEqs.toIndexedSeq
    val implied = if (inEqs.size < 3) BitSet() else impliedInEqs(inEqs, order)
    if (implied.isEmpty) constraint
    else constraint.updateInEqs(InEqConj(
      inEqs.indices.iterator filterNot implied map inEqs, order))(order)
  }

  // the indices of the inequalities to drop; only inequalities not
  // dropped yet serve as premises, so the kept ones imply the dropped ones
  private def impliedInEqs(inEqs : IndexedSeq[LinearCombination],
                           order : TermOrder) : collection.Set[Int] = {
    import collection.mutable

    def termsOf(lc : LinearCombination) : Iterator[Term] =
      lc.termIterator filterNot (_ == OneTerm)
    def linearPart(lc : LinearCombination) : LinearCombination =
      lc + (-lc.constant)

    val terms     = (inEqs.iterator flatMap termsOf).toVector.distinct
    val termIndex = terms.zipWithIndex.toMap
    val supports  = inEqs map (lc => BitSet() ++ (termsOf(lc) map termIndex))
    val occurrences = Array.fill(terms.size)(mutable.BitSet())
    for (i <- inEqs.indices; t <- supports(i)) occurrences(t) += i
    lazy val withLinearPart : Map[LinearCombination, Int] =
      (inEqs.indices map (i => (linearPart(inEqs(i)), i))).toMap

    // a combination that cancels a term c of a and b is their
    // Fourier-Motzkin inference on c, so these pairs are found by looking
    // up the inferences
    val inferencePremises = mutable.Map[Int, List[(Int, Int)]]()
    for (t <- terms.indices) {
      val c = terms(t)
      val (positive, negative) =
        occurrences(t).toVector partition (i => (inEqs(i) get c).signum > 0)
      for (a <- positive; b <- negative) {
        val inference =
          LinearCombination.sum(-(inEqs(b) get c), inEqs(a),
                                inEqs(a) get c, inEqs(b), order)
        if (!inference.isConstant) {
          val primitive = inference.makePrimitive
          for (j <- withLinearPart get linearPart(primitive))
            if (primitive.constant <= inEqs(j).constant)
              inferencePremises(j) =
                (a, b) :: inferencePremises.getOrElse(j, Nil)
        }
      }
    }

    // u and v solve u * a + v * b = det * j on the leading term x of a and
    // a term y, by Cramer's rule; the other terms are compared after
    // dividing the combination by det
    def impliedBy(j : LinearCombination,
                  a : LinearCombination,
                  b : LinearCombination) : Boolean = {
      val x = a.leadingTerm
      val dets = (termsOf(a) ++ termsOf(b)) map (y =>
        (y, (a get x) * (b get y) - (a get y) * (b get x)))
      dets find (!_._2.isZero) exists { case (y, det) =>
        val sign = IdealInt(det.signum)
        val u = ((j get x) * (b get y) - (j get y) * (b get x)) * sign
        val v = ((a get x) * (j get y) - (a get y) * (j get x)) * sign
        u.signum >= 0 && v.signum >= 0 && !(u.isZero && v.isZero) && {
          val combination =
            LinearCombination.sum(u, a, v, b, order).makePrimitive
          (j constantDiff combination) exists (_.signum >= 0)
        }
      }
    }

    val dropped = mutable.BitSet()

    // a combination that cancels no term has premises with terms of j only
    def impliedByCombination(j : Int) : Boolean = {
      val candidates = mutable.BitSet()
      for (t <- supports(j)) candidates |= occurrences(t)
      val premises = candidates.toVector filter (i =>
        i != j && !dropped(i) && (supports(i) subsetOf supports(j)))
      premises.indices exists (p =>
        (p + 1 until premises.size) exists { q =>
          val (a, b) = (premises(p), premises(q))
          (supports(a) | supports(b)) == supports(j) &&
          impliedBy(inEqs(j), inEqs(a), inEqs(b))
        })
    }

    for (j <- inEqs.indices) {
      val implied =
        (inferencePremises.getOrElse(j, Nil) exists {
           case (a, b) => !dropped(a) && !dropped(b) }) ||
        impliedByCombination(j)
      if (implied) dropped += j
    }
    dropped
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

    val localConstants =
      order.sort(localSymbols collect { case c : ConstantTerm => c })

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
            c <- singleSymbol(a.last).iterator
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

  private def runStage(name  : String,
                       stage : Conjunction => Conjunction,
                       conj  : Conjunction) : Conjunction = {
    val result = stage(conj)
    if (collectStats) {
      val fires = stageFires.getOrElseUpdate(name, 0L)
      if (!(result eq conj)) stageFires(name) = fires + 1
    }
    result
  }

  private def runStages(constraint   : Conjunction,
                        localSymbols : Set[Term],
                        order        : TermOrder) : Conjunction = {
    val stages : List[(String, Conjunction => Conjunction)] = List(
      ("recompose",  recomposeExtracts(_, order)), // before linearize
      ("linearize",  linearizeConstantSlices(_, order)),
      ("inline",     inlineLocalEquations(_, localSymbols, order)),
      ("dropRange",  dropRangeConstrainedLocals(_, localSymbols, order)),
      ("dropUnused", dropUnusedFunctionAtoms(_, localSymbols,
                       ModuloArithmetic.functionalPredicates, order)),
      ("dropCasts",  dropFreeArgumentCasts(_, localSymbols, order)))

    @annotation.tailrec
    def run(conj : Conjunction) : Conjunction = {
      val staged = stages.foldLeft(conj) { case (c, (name, stage)) =>
        runStage(name, stage, c)
      }
      // alternate between running the reducer, which applies additional
      // simplification rules
      val next = symex_sf.reducer(Conjunction.TRUE)(staged)
      if (collectStats) stageRounds += 1
      if (next eq conj) conj else run(next)
    }
    run(constraint)
  }

  /**
   * Takes a constraint and a set of local symbols that can safely be
   * eliminated. If reduceBeforeSimplification is true, the symbol factory's
   * reducer will be first applied to the constraint before attempting
   * simplification.
   */
  def simplify(constraint                 : Conjunction,
               localSymbols               : Set[Term],
               reduceBeforeSimplification : Boolean) : Conjunction =
    if (!collectStats || inSimplify)
      simplifyConstraintImpl(constraint, localSymbols,
                             reduceBeforeSimplification)
    else {
      inSimplify = true
      val start = System.nanoTime
      try simplifyConstraintImpl(constraint, localSymbols,
                                 reduceBeforeSimplification)
      finally {
        inSimplify = false
        simplifyNanos += System.nanoTime - start
      }
    }

  private def simplifyConstraintImpl(constraint                 : Conjunction,
                                     localSymbols               : Set[Term],
                                     reduceBeforeSimplification : Boolean)
      : Conjunction = {
    val reducedConstraint =
      if (reduceBeforeSimplification)
        symex_sf.reducer(Conjunction.TRUE)(constraint)
      else constraint

    if (isQuantifierFreeConjunction(constraint)) {
      /**
       * If the constraint is a quantifier-free conjunction, we can use the
       * [[ConjunctEliminator]] class for simplification.
       */
      val simplified =
        runStages(reducedConstraint, localSymbols, symex_sf.order)
      val eliminator  = new LocalSymbolEliminator(
        simplified, localSymbols, symex_sf.order)
      val eliminated  = eliminator.eliminate(ComputationLogger.NonLogger)
      val eliminatedWithDivJudgements = if (eliminator.divJudgements isEmpty)
        eliminated
      else
        Conjunction.conj(
          eliminated :: eliminator.divJudgements.map(_.negate), symex_sf.order)
      runStage("dropImplied", dropImpliedInEqs(_, symex_sf.order),
               eliminatedWithDivJudgements)
    } else {
       // If there are disjunctions, then try another simp method
      val base = runStages(reducedConstraint, localSymbols, symex_sf.order)

      // quantify local symbols
      val sortedLocalSymbols =
        symex_sf.order.sort(localSymbols.map(_.asInstanceOf[ConstantTerm]))
      val quanF = Conjunction.quantify(ap.terfor.conjunctions.Quantifier.EX,
                                       sortedLocalSymbols,
                                       base, base.order)

      // try to eliminate the quantified vars
      val reducedQuanF : Conjunction =
        symex_sf.reducer(Conjunction.TRUE).apply(quanF)

      // re-introduce local symbols only for the outermost exists
      val exBlockSize =
        reducedQuanF.quans.reverse.takeWhile(
          _ == ap.terfor.conjunctions.Quantifier.EX).size
      val numToInstantiate = exBlockSize min sortedLocalSymbols.size

      val instantiated = reducedQuanF.instantiate(
        sortedLocalSymbols take numToInstantiate)(reducedQuanF.order)

      if (isQuantifierFreeConjunction(instantiated))
        simplify(instantiated, localSymbols,
                 reduceBeforeSimplification = false)
      else
        runStage("dropImplied", dropImpliedInEqs(_, instantiated.order),
                 instantiated)
    }
  }

  private def isQuantifierFreeConjunction(c : Conjunction) : Boolean =
    c.negatedConjs.isEmpty && c.quans.isEmpty
}
