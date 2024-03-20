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

import ap.terfor.{ComputationLogger, ConstantTerm, Term, TermOrder}
import ap.terfor.arithconj.ModelElement
import ap.terfor.conjunctions.{ConjunctEliminator, Conjunction}

/**
 * Takes a constraint and a set of local symbols that can safely be eliminated.
 * If reduceBeforeSimplification is true, the symbol factory's reducer will
 * be first applied to the constraint before attempting simplification.
 */
trait ConstraintSimplifier {
  def simplifyConstraint(constraint:                 Conjunction,
                         localSymbols:               Set[Term],
                         reduceBeforeSimplification: Boolean)(
      implicit symex_sf:                             SymexSymbolFactory): Conjunction
}

/**
 * An implementation of ConstraintSimplifier based on ConjunctEliminator.
 */
trait ConstraintSimplifierUsingConjunctEliminator extends ConstraintSimplifier {

  class LocalSymbolEliminator(constraint:   Conjunction,
                              localSymbols: Set[Term],
                              order:        TermOrder)
      extends ConjunctEliminator(constraint, localSymbols, Set(), order) {

    override protected def nonUniversalElimination(f: Conjunction) = {}

    // todo: check if this eliminates function applications
    //   e.g., unused select and stores

    protected def universalElimination(m: ModelElement): Unit = {}

    override protected def addDivisibility(f: Conjunction) = {}

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

    if (constraint.negatedConjs.isEmpty) {
      /**
       * If the constraint is a conjunction, we can use the
       * [[ConjunctEliminator]] class for simplification.
       */
      new LocalSymbolEliminator(reducedConstraint,
                                localSymbols,
                                symex_sf.order)
        .eliminate(ComputationLogger.NonLogger)
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

      // eliminate any remaining quantifiers by re-introducing local symbols
      assert(sortedLocalSymbols.size >= reducedQuanF.quans.size)

      reducedQuanF.instantiate(sortedLocalSymbols take reducedQuanF.quans.size)(
                               reducedQuanF.order)
    }
  }
}
