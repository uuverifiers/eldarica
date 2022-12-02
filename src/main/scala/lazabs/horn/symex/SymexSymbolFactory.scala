/**
 * Copyright (c) 2022 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import ap.SimpleAPI
import ap.terfor.preds.Predicate
import ap.terfor.ConstantTerm
import ap.theories.Theory
import lazabs.horn.bottomup.SymbolFactory
import lazabs.horn.bottomup.Util.toStream
import collection.mutable.{HashMap => MHashMap}

class SymexSymbolFactory(theories: Seq[Theory], prover: SimpleAPI)
    extends SymbolFactory(theories) {

  /**
   * A stream of local symbols for each occurrence of a predicate
   * E.g., {(pc_0_0, pc_1_0), (pc_0_1, pc_1_1), ...} for predicate p with max occ 1
   *            | | local symbol id
   *            | occurrence
   * Note: local symbols should be in the same order for all occurrences for
   * substitution performance.
   */
  private var localSymbolsForPredicate
    : Map[Predicate, Stream[Seq[ConstantTerm]]] = _

  private val lastLocalSymbolIdForPredicate = new MHashMap[Predicate, Int]

  /**
   * This method must be called to initialize the symbol factory after the
   * occurrence count of predicates are known.
   * @param predicatesAndMaxOccurrences: A set of (predicate, max occurrence)
   *                                   tuples, where max occurrence is inclusive.
   */
  def initialize(predicatesAndMaxOccurrences: Set[(Predicate, Int)]) = {
    localSymbolsForPredicate =
      (for ((pred, maxOcc) <- predicatesAndMaxOccurrences)
        yield
          (pred, toStream { symbolId =>
            // create a version of this variable for each occurrence
            for (occ <- 0 to maxOcc) yield {
              val newSymbol =
                new ConstantTerm(s"${pred.name}_c_${occ}_$symbolId")
              addSymbol(newSymbol)
              newSymbol
            }
          })).toMap

    for ((pred, _) <- predicatesAndMaxOccurrences) {
      lastLocalSymbolIdForPredicate += ((pred, 0))
    }
  }

  //def lastLocalSymbolIdForPred(pred: Predicate): Int = {
  //  lastLocalSymbolIdForPredicate get pred match {
  //    case Some(id) => id
  //    case None =>
  //      throw new UnsupportedOperationException(
  //        "Trying to get symbol id for an unknown predicate. Did you " +
  //          "initialize SymexSymbolFactory with the correct set of predicates?")
  //  }
  //}

  /**
   * @return The local symbol at symbolId for each occurrence
   */
  def localSymbolsForPred(pred:       Predicate,
                          numSymbols: Int,
                          occ:        Int): Seq[ConstantTerm] =
    if (localSymbolsForPredicate == null) {
      throw new NullPointerException(
        "SymexSymbolFactory must be initialized first. " +
          "Did you forget to call initialize?")
    } else {
      localSymbolsForPredicate get pred match {
        case Some(constantStream) =>
          //if (symbolId > lastLocalSymbolIdForPred(pred)) {
          //  lastLocalSymbolIdForPredicate(pred) = symbolId
          // todo: review this implementation during revision, might be suboptimal
          //  maybe we do not need so many checks
          //constantStream(symbolId)
          (constantStream take numSymbols).map(seq => seq(occ))
        // todo: a different data-structure to avoid map?
        case None =>
          throw new UnsupportedOperationException(
            "Trying to get a local symbol for an unknown predicate. Did you " +
              "initialize SymexSymbolFactory with the correct set of predicates?")
      }
    }

  /**
   * Override SymbolFactory.addConstant so that each symbol is also added
   * to the passed prover.
   */
  override protected def addConstant(constant: ConstantTerm): Unit = {
    super.addConstant(constant)
    prover.addConstant(constant)
  }

}
