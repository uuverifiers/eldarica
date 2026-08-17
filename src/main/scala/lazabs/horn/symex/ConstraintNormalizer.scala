/**
 * Copyright (c) 2026 Zafer Esen, Philipp Ruemmer. All rights reserved.
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
import ap.terfor.{ConstantTerm, Term, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.linearcombination.LinearCombination.SingleTerm
import ap.terfor.preds.{Atom, Predicate}
import ap.terfor.substitutions.ConstantSubst
import ap.util.{Debug, Seqs}

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

/**
 * Result type of [[ConstraintNormalizer.normalize]]
 * @param constraint         : the normalized constraint
 * @param definingTheoryLits : definingTheoryLits[i] is the theory literal that
 *                             defines local symbol number i (may not exist).
 *                             e.g., the BV literal
 *                             bv_extract(0,0, p_0_0, p_c_0_i) is at index i,
 *                             because it defines p_c_0_i (result arg)
 */
case class NormalizedConstraint(constraint         : Conjunction,
                                definingTheoryLits : IndexedSeq[Option[Atom]])

/**
 * Intermediate, same info as [[NormalizedConstraint]] but before rebuilding
 * the constraint.
 * e.g., localSymbol      s = [              x,                 y,   z ]
 *       definingTheoryLits = [Some(fun(..., x)), Some(fun(..., y)), None]
 *       where fun is some theory function, and z is not the res of any
 */
private[symex]
case class CanonicalSymbolOrder(localSymbols       : IndexedSeq[ConstantTerm],
                                definingTheoryLits : IndexedSeq[Option[Atom]])

// An arg of a theory literal, where symbols are replaced with canonical pos.
// E.g., arg: 2*x + y + 5 with x at pos 4, y at 1
//       terms = Seq((1,1), (4,2))
//                   pos 1 (y) coeff = 1, pos 4 (x) coeff = 2
//       constant = 5
private[symex] case class ArgKey(terms : Seq[(Int, IdealInt)], constant : IdealInt)

// A theory literal and its ArgKeys.
// e.g., bv_extract(7, 1, p_0_0, x) with p_0_0 at pos 0
//       pred = bv_extract
//       args = ( ArgKey(Nil, constant = 7,
//                ...,
//                ArgKey(Seq((0, 1)), 0))
//               )
//               (p_0_0 is result, so not in args)
private[symex] case class LitKey(pred : Predicate, args : Seq[ArgKey])

// A usage of a symbol in a theory literal. This is used as fallback for
// symbols that no theory literal defines. The sorted usage list is then used instead.
// E.g., for undefinable symbols a and b
// usages of a: f(0, a, x), f(42, a, y)
// usages of b: f(0, b, x), f(3,  b, z)
// for a: argIndex: 1, (f(0, ?, ?), f(42, ?, ?))
// for b: argIndex: 1, (f(0, ?, ?), f( 3, ?, ?))
// 3 < 42 so b will be placed first. ? represent unplaced syms.
private[symex] case class UsageKey(argIndex : Int, lit : LitKey)

/**
 * Normalizes constraints so that they can be checked for structural
 * equivalence. For instance for cheap hash lookups, subsumption checks etc.
 * E.g., bv_extract(0,0,a,b) and bv_extract(0,0,a,c), after
 * normalization b and c get the same symbol.
 * - Every symbol gets a canonical position 0, 1, ... computed from the
 *   structure of the constraint.
 * - Every symbol is renamed using that position, e.g.,
 *   local symbols: p_c_0_0, p_c_0_1 etc.
 */
object ConstraintNormalizer {

  private object AC extends Debug.ASSERTION_CATEGORY

  /**
   *  Normalizes a constraint with theory literals using its structure.
   * @param fixedSyms   Fixed symbols tha tthe normalizer does not touch.
   *                    e.g., pred args etc.
   * @param constraint  The constraint to be normalized
   * @param newSyms     A generator for new names. E.g., if constraint has
   *                    n symbols to rename, names will be generated by
   *                    newSyms(n)(0), newSyms(n)(1) etc., based on the order
   *                    of their canonical positions.
   * @return            The normalized constraint.
   */
  def normalize(fixedSyms  : Seq[ConstantTerm],
                constraint : Conjunction,
                newSyms    : Int => (Seq[ConstantTerm], TermOrder))
  : NormalizedConstraint = {
    val simpConstraint = simplify(constraint)
    val symbolOrder    = canonicalSymbolOrder(fixedSyms, simpConstraint)
    rebuild(simpConstraint, symbolOrder, newSyms)
  }

  // Some(c): merged; c may also be false if contradiction detected
  // None : nothing to merge
  private def mergeDuplicateLiterals(constraint : Conjunction)
  : Option[Conjunction] = {
    // lits with same args applied to same funs
    val equalResultGroups =
      constraint.predConj.positiveLits.groupBy(lit => (lit.pred, lit.init))
        .values.filter(_.size > 1) // must be more than 1 lit for equality
        .map(_.map(_.last)) // keep only the las arg (res)

    def isContradiction(results : Seq[LinearCombination]) : Boolean =
      results.filter(_.isConstant) // const results
        .map(_.constant).distinct.size > 1 // but more than one distinct val

    if (equalResultGroups exists isContradiction) // args same but res is constant and different
      return Some(Conjunction.FALSE)

    val replacements : Map[ConstantTerm, Term] =
      (for(results <- equalResultGroups.iterator;
           groupValue = results.find(_.isConstant).getOrElse(results.head);
           SingleTerm(sym : ConstantTerm) <- results.iterator
           if !(groupValue.constants contains sym))
        yield sym -> (groupValue : Term)).toMap
    if (replacements.isEmpty) None
    else Some(ConstantSubst(replacements, constraint.order)(constraint))
  }

  // Applies some simplification passes before normalization
  private[symex]
  def simplify(constraint : Conjunction) : Conjunction = {
    var cur = constraint
    var done = false
    while(!done) {
      mergeDuplicateLiterals(cur) match {
        case Some(next) => cur = next
        case None       => done = true
      }
      // TODO others simplifications?
    }
    cur
  }

  // Computes the canonical order of every symbol occurring in the constraint.
  // `fixedSyms` get the first positions, then smallest literal
  // whose args all have positions but not its result defines its result symbol
  // (i.e., that result symbol gets the next position). If some symbols
  // remain (may be that no literal defines them), they are positioned at
  // the end.
  private[symex]
  def canonicalSymbolOrder(fixedSyms  : Seq[ConstantTerm],
                           constraint : Conjunction) : CanonicalSymbolOrder = {
    val theoryLits = constraint.predConj.positiveLits
    val allSyms = constraint.constants
    val definableSyms = theoryLits.flatMap(l => resultSymbol(l)).toSet

    val symPosition = new MHashMap[ConstantTerm, Int]
    // init position with fixed symbols
    for (sym <- fixedSyms)
      symPosition.getOrElseUpdate(sym, symPosition.size)

    val localSymbols = new ArrayBuffer[ConstantTerm]
    val definingTheoryLits = new ArrayBuffer[Option[Atom]]

    def placeSym(sym : ConstantTerm, definingLit : Option[Atom]) : Unit = {
      symPosition(sym) = symPosition.size
      localSymbols += sym
      definingTheoryLits += definingLit
    }

    // can this theory literal define its result? i.e., are all its
    // input syms (syms except the last one) already defined?
    def canDefine(lit : Atom) : Boolean = resultSymbol(lit) match {
      case Some(sym) => // this lit may be able to define sym
        !(symPosition contains sym) && // sym not yet defined
        lit.init.forall(_.constants forall symPosition.contains) // all else defined
      case None => false // nothing to define
    }

    def litKey(lit : Atom) : LitKey = {
      val args = for (linearComb <- lit.init) yield {
        val sortedTerms = (for ((coeff, sym : ConstantTerm) <- linearComb)
          yield (symPosition(sym), coeff)).toList.sortBy(_._1)
        ArgKey(sortedTerms, linearComb.constant)
      }
      LitKey(lit.pred, args.toList)
    }

    val UnplacedPos = Int.MaxValue

    def argKeyOf(linearComb : LinearCombination) : ArgKey = {
      val sortedTerms = (for ((coeff, sym : ConstantTerm) <- linearComb)
        yield (symPosition.getOrElse(sym, UnplacedPos),
          coeff)).toList.sortBy(_._1)
      ArgKey(sortedTerms, linearComb.constant)
    }

    // also includes result (lit instead of lit.init, and allows unplaced syms)
    def litKeyFull(lit : Atom) : LitKey = LitKey(lit.pred, lit.map(argKeyOf))

    def signatureOf(sym : ConstantTerm) : (Seq[UsageKey], Seq[(Int, ArgKey)]) = {
      val theoryUsages = (for (lit <- theoryLits; (arg, id) <- lit.zipWithIndex
                               if arg.constants contains sym)
        yield UsageKey(id, litKeyFull(lit))).toList.sorted
      val arithUsages =
        (for ((lcs, kind) <- Seq((constraint.arithConj.positiveEqs, 0),
                                 (constraint.arithConj.negativeEqs, 1),
                                 (constraint.arithConj.inEqs, 2));
          lc <- lcs if lc.constants contains sym) yield (kind, argKeyOf(lc))).toList.sorted
      (theoryUsages, arithUsages)
    }

    var done = false
    while(!done) {
      val readyToDefineLits = theoryLits filter canDefine
      if (readyToDefineLits nonEmpty) { // some lits ready
        val lit = readyToDefineLits.minBy(litKey)
        placeSym(resultSymbol(lit).get, Some(lit))
      } else { // no lits ready to define a result symbol
        val unplacedSyms = allSyms filterNot symPosition.contains
        if (unplacedSyms isEmpty) {
          done = true
        } else {
          // symbols that are not "resultSymbols" will never be defined
          // so they get their positions here.
          val undefinableSyms = unplacedSyms filterNot definableSyms
          val candidates = // e.g., f(a,b) and g(b,a).
            if(undefinableSyms nonEmpty) undefinableSyms else unplacedSyms
          placeSym(candidates.minBy(signatureOf)(signatureOrdering), None)
        }
      }
    }
    Debug.assertPost(AC, constraint.constants forall symPosition.contains)
    Debug.assertPost(AC, localSymbols.size == definingTheoryLits.size)
    CanonicalSymbolOrder(localSymbols, definingTheoryLits)
  }

  private[symex]
  def resultSymbol(a : Atom) : Option[ConstantTerm] = {
    a.last match {
      case SingleTerm(c : ConstantTerm) => Some(c)
      case _ => None
    }
  }

  // Rename symbols in atoms and constraint to canonical ones
  private[symex]
  def rebuild(constraint  : Conjunction,
              symbolOrder : CanonicalSymbolOrder,
              newSyms     : Int => (Seq[ConstantTerm], TermOrder))
  : NormalizedConstraint = {
    val (replacements, order) = newSyms(symbolOrder.localSymbols.size)
    Debug.assertPre(AC, replacements.size == symbolOrder.localSymbols.size)
    Debug.assertPre(AC, replacements.toSet.size == replacements.size)
    Debug.assertPre(AC, {
      val untouched = constraint.constants -- symbolOrder.localSymbols
      (replacements.toSet intersect untouched).isEmpty
    })
    val subst = ConstantSubst(
      (symbolOrder.localSymbols zip replacements).toMap, order)
    val newConstraint = subst(constraint)
    Debug.assertPost(AC, newConstraint.constants.size == constraint.constants.size)
    val definingLits = for (maybeLit <- symbolOrder.definingTheoryLits)
      yield maybeLit.map(lit => Atom(lit.pred,
        for(linearComb <- lit) yield subst(linearComb), order))
    NormalizedConstraint(newConstraint, definingLits)
  }

  // ORDERINGS
  // term of an arg, lexical ordering with canonical pos first, then coefficient
  private implicit val termOrdering : Ordering[(Int, IdealInt)] =
    new Ordering[(Int, IdealInt)] {
      def compare(a : (Int, IdealInt), b : (Int, IdealInt)) : Int =
        Seqs.lexCombineInts(a._1 compare b._1, a._2 compare b._2)
    }

  // one arg: terms first, constant last
  private implicit val argKeyOrdering : Ordering[ArgKey] = new Ordering[ArgKey] {
    def compare(a : ArgKey, b : ArgKey) : Int = Seqs.lexCombineInts(
      Seqs.lexCompare(a.terms.iterator, b.terms.iterator),
      a.constant compare b.constant)
  }

  // a literal: pred name, pred arity, args
  private[symex]
  implicit val LitKeyOrdering : Ordering[LitKey] = new Ordering[LitKey] {
    def compare(a : LitKey, b : LitKey) : Int = Seqs.lexCombineInts(
      a.pred.name compareTo b.pred.name,
      a.pred.arity compareTo b.pred.arity,
      Seqs.lexCompare(a.args.iterator, b.args.iterator)
    )
  }

  // a usage: pred name, arity, arg index and the lit args
  private implicit val usageKeyOrdering : Ordering[UsageKey] =
    new Ordering[UsageKey] {
      def compare(a : UsageKey, b : UsageKey) : Int = Seqs.lexCombineInts(
        a.lit.pred.name compareTo b.lit.pred.name,
        a.lit.pred.arity compareTo b.lit.pred.arity,
        a.argIndex compareTo b.argIndex,
        Seqs.lexCompare(a.lit.args.iterator, b.lit.args.iterator)
      )
    }

  private implicit val arithUsageOrdering : Ordering[(Int, ArgKey)] =
    new Ordering[(Int, ArgKey)] {
      def compare(a : (Int, ArgKey), b : (Int, ArgKey)) : Int =
        Seqs.lexCombineInts(a._1 compare b._1,
          argKeyOrdering.compare(a._2, b._2))
    }

  // a symbol's sorted usages
  private[symex]
  val signatureOrdering : Ordering[(Seq[UsageKey], Seq[(Int, ArgKey)])] =
    new Ordering[(Seq[UsageKey], Seq[(Int, ArgKey)])] {
    def compare(a : (Seq[UsageKey], Seq[(Int, ArgKey)]),
                b : (Seq[UsageKey], Seq[(Int, ArgKey)])) : Int =
      Seqs.lexCombineInts(
        Seqs.lexCompare(a._1.iterator, b._1.iterator),
        Seqs.lexCompare(a._2.iterator, b._2.iterator)
      )
  }
}
