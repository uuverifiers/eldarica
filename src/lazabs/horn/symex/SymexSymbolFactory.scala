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
