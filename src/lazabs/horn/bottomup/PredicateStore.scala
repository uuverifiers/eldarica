/**
 * Copyright (c) 2011-2022 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.bottomup

import ap.PresburgerTools
import ap.parser._
import ap.terfor.{TermOrder, TerForConvenience}
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.substitutions.VariableSubst
import ap.theories.ExtArray
import ap.proof.ModelSearchProver
import ap.types.Sort
import ap.util.Seqs

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

object PredicateStore {
  import IExpression._

  class  PredicateGenException(msg : String)
         extends Exception(msg)
  object QuantifierInPredException
         extends PredicateGenException("cannot handle quantifier in predicate")

  /**
   * Visitor for instantiating quantifiers in a formula with given
   * terms. This is sometimes a way to get rid of quantifiers in
   * interpolants over arrays.
   */
  class InstantiatingVisitor(terms : Map[Sort, Seq[ITerm]])
                       extends CollectingVisitor[Unit, IExpression] {
    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression =
      (t update subres) match {
        case ISortedQuantified(q, s, f)
            if terms.contains(s) =>
              q match {
                case Quantifier.ALL =>
                  and(for (t <- terms(s))
                      yield IExpression.subst(f, List(t), -1))
                case Quantifier.EX =>
                  or (for (t <- terms(s))
                      yield IExpression.subst(f, List(t), -1))
              }
        case newT => newT
      }
    
  }

}

class PredicateStore[CC <% HornClauses.ConstraintClause]
                    (context : HornPredAbsContext[CC]) {

  import context._
  import PredicateStore._

  var implicationChecks = 0
  var implicationChecksPos = 0
  var implicationChecksNeg = 0
  var implicationChecksPosTime : Long = 0
  var implicationChecksNegTime : Long = 0
  var implicationChecksSetup = 0
  var implicationChecksSetupTime : Long = 0

  var matchCount = 0
  var matchTime : Long = 0  

  //////////////////////////////////////////////////////////////////////////////

  val predicates =
    (for (rs <- relationSymbols.values)
       yield (rs -> new ArrayBuffer[RelationSymbolPred])).toMap

  val predicateHashIndexes =
    (for (rs <- relationSymbols.values)
         yield (rs -> new ArrayBuffer[Stream[Int]])).toMap

  val predicate2Index =
    new MHashMap[RelationSymbolPred, Int]

  private def predicateHashIndexesFor(pred : RelationSymbolPred) : Stream[Int] =
    predicateHashIndexes(pred.rs)(predicate2Index(pred))

  //////////////////////////////////////////////////////////////////////////////

  def addRelationSymbolPred(pred : RelationSymbolPred) : Unit = {
    assert(predicates(pred.rs).size == predicateHashIndexes(pred.rs).size)

    val predBuf = predicates(pred.rs)

    predicate2Index.put(pred, predBuf.size)
    predBuf += pred

    predicateHashIndexes(pred.rs) +=
      (for (f <- pred.posInstances) yield (hasher addFormula f))
  }

  def addRelationSymbolPreds(preds : Iterable[RelationSymbolPred]) : Unit =
    for (pred <- preds) addRelationSymbolPred(pred)

  def addHasherAssertions(clause : NormClause,
                          from : Seq[AbstractState]) = if (hasher.isActive) {
    hasher assertFormula clauseHashIndexes(clause)
    for ((state, (rs, occ)) <- from.iterator zip clause.body.iterator)
      for (pred <- state.preds) {
        val id = predicateHashIndexesFor(pred)(occ)
        hasher assertFormula id
      }
  }

  def addIPredicates(preds : Map[Predicate, Seq[IFormula]]) : Unit =
    for ((p, preds) <- preds) {
      val rs = relationSymbols(p)
      for (f <- preds) {
        val intF = IExpression.subst(f, rs.argumentITerms.head.toList, 0)
        val (rawF, posF, negF) = rsPredsToInternal(intF)
        val pred = RelationSymbolPred(rawF, posF, negF, rs)
        addRelationSymbolPred(pred)
      }
    }

  private def elimQuansIfNecessary(c : Conjunction,
                                   positive : Boolean) : Conjunction =
    if (ap.terfor.conjunctions.IterativeClauseMatcher.isMatchableRec(
           if (positive) c else c.negate, Map())) {
      c
    } else {
      val newC = PresburgerTools.elimQuantifiersWithPreds(c)
      if (!ap.terfor.conjunctions.IterativeClauseMatcher.isMatchableRec(
              if (positive) newC else newC.negate, Map()))
        throw QuantifierInPredException
      newC
    }

  private def rsPredsToInternal(f : IFormula)
                             : (Conjunction, Conjunction, Conjunction) = {
    val rawF = sf.toInternalClausify(f)
    val posF = elimQuansIfNecessary(sf.preprocess(
                                      sf.toInternalClausify(~f)).negate, true)
    val negF = elimQuansIfNecessary(sf.preprocess(
                                      rawF), false)
    (rawF, posF, negF)
  }

  //////////////////////////////////////////////////////////////////////////////

  var hasherChecksHit, hasherChecksMiss = 0

  def predIsConsequenceWithHasher(pred : RelationSymbolPred, rsOcc : Int,
                                  reducer : ReduceWithConjunction,
                                  prover : => ModelSearchProver.IncProver,
                                  order : TermOrder) : Boolean = {
    val hasherId = predicateHashIndexesFor(pred)(rsOcc)

    if (hasher mightBeImplied hasherId) {
      val res = predIsConsequence(pred, rsOcc, reducer, prover, order)
      if (!res)
        hasherChecksMiss = hasherChecksMiss + 1
      res
    } else {
      hasherChecksHit = hasherChecksHit + 1
      false
    }
  }

  def predIsConsequence(pred : RelationSymbolPred, rsOcc : Int,
                        reducer : ReduceWithConjunction,
                        prover : => ModelSearchProver.IncProver,
                        order : TermOrder) : Boolean = {
    val startTime = System.currentTimeMillis
    implicationChecks = implicationChecks + 1
    val reducedInstance = reducer.tentativeReduce(pred posInstances rsOcc)

    val res =
      !reducedInstance.isFalse &&
      (reducedInstance.isTrue ||
       isValid(prover.conclude(reducedInstance, order)))

    if (res) {
      implicationChecksPos = implicationChecksPos + 1
      implicationChecksPosTime =
        implicationChecksPosTime + (System.currentTimeMillis - startTime)
    } else {
      implicationChecksNeg = implicationChecksNeg + 1
      implicationChecksNegTime =
        implicationChecksNegTime + (System.currentTimeMillis - startTime)
    }

    res
  }
  
  //////////////////////////////////////////////////////////////////////////////

  def preparePredicates(preds : Seq[(Predicate, Seq[Conjunction])])
                      : Map[RelationSymbol, IndexedSeq[RelationSymbolPred]] = {
    val predsToAdd =
      new MHashMap[RelationSymbol, IndexedSeq[RelationSymbolPred]]

    for ((p, fors) <- preds) {
      val rs = relationSymbols(p)
      val subst = VariableSubst(0, rs.arguments.head, sf.order)
      val rsReducer = relationSymbolReducers(rs)

      val rsPreds =
        (for (f <- fors.iterator;
              substF2 = rsReducer(subst(f));
              substF <- splitPredicate(substF2);
              if (reallyAddPredicate(substF, rs));
              pred <- genSymbolPredBestEffort(substF, rs).toSeq;
              if (!(predicates(rs) exists
                      (_.rawPred == pred.rawPred)))) yield {
           addRelationSymbolPred(pred)
           pred
         }).toVector

      if (!rsPreds.isEmpty) {
        if (lazabs.GlobalParameters.get.log) {
          print(p.name + ": ")
          println(rsPreds mkString ", ")
        }
        predsToAdd.put(rs, rsPreds)
      }
    }

    predsToAdd.toMap
  }

  /**
   * Split a new predicate into conjuncts, which can be treated
   * then as separate predicates.
   */
  private def splitPredicate(f : Conjunction) : Iterator[Conjunction] =
    if (f.quans.isEmpty)
      f.iterator
    else
      Iterator single f

  private def reallyAddPredicate(f : Conjunction,
                                 rs : RelationSymbol) : Boolean =
    !f.isFalse && !f.isTrue &&
    !(predicates(rs) exists (_.rawPred == f)) && {
      // check whether the predicate is subsumed by older predicates
      val reducer = sf reducer f
      val impliedPreds =
        for (p <- predicates(rs); if (reducer(p.rawPred).isTrue))
        yield p.positive

      impliedPreds.isEmpty || {
        import TerForConvenience._
        implicit val _ = sf.order
        val c = sf reduce conj(impliedPreds)
        !((sf reducer c)(f).isTrue)
      }
    }

  private def genSymbolPredBestEffort(f  : Conjunction,
                                      rs : RelationSymbol)
                                         : Option[RelationSymbolPred] =
    try {
      Some(genSymbolPred(f, rs))
    } catch {
      case t : PredicateGenException =>
        if (lazabs.GlobalParameters.get.log)
          println("Warning: dropping predicate: " + t.getMessage)
        None
    }

  private def genSymbolPred(f : Conjunction,
                            rs : RelationSymbol) : RelationSymbolPred =
    if (Seqs.disjoint(f.predicates, sf.functionalPreds)) {
      RelationSymbolPred(f, f, f, rs)
    } else {
      // some simplification, to avoid quantifiers in predicates
      // as far as possible, or at least provide good triggers
/*      println(f)
      val prenex = PresburgerTools toPrenex f
      println(" -> " + prenex)
      val cnf = (PresburgerTools toDNF prenex.unquantify(prenex.quans.size).negate).negate
      val complete = sf reduce Conjunction.quantify(prenex.quans, cnf, f.order)
      println(" -> " + complete) */

      val iabsy =
        sf.postprocessing(f, simplify = true)

      val (rawF, posF, negF) =
        try {
          rsPredsToInternal(iabsy)
        } catch {
          case QuantifierInPredException => {
            val arrayConsts =
              for (c <- SymbolCollector constantsSorted iabsy;
                   if (Sort sortOf c).isInstanceOf[ExtArray.ArraySort])
              yield IConstant(c)

            if (arrayConsts.isEmpty)
              throw QuantifierInPredException

            val constsMap  = arrayConsts.groupBy(Sort.sortOf _)

            val visitor    = new InstantiatingVisitor(constsMap)
            val inst       = visitor.visit(iabsy, ()).asInstanceOf[IFormula]

            val simplifier = new ap.interpolants.ExtArraySimplifier
            val simpInst   = simplifier(inst)

            rsPredsToInternal(simpInst)
          }
        }

//      println(" -> pos: " + posF)
//      println(" -> neg: " + negF)

      RelationSymbolPred(rawF, posF, negF, rs)
    }

  /**
   * Translate solution formulas back to input ASTs. This will first
   * replace the variables with sorted constants, to to enable
   * theory-specific back-translation.
   */
  def convertToInputAbsy(p : Predicate,
                         cs : Seq[Conjunction]) : Seq[IFormula] =
    cs match {
      case Seq(c) if c.isTrue =>
        List(IBoolLit(true))
      case Seq(c) if c.isFalse =>
        List(IBoolLit(false))
      case cs => {
        val consts =
          for (s <- HornPredAbs.predArgumentSorts(p)) yield (s newConstant "X")
        val order =
          sf.order extend consts.reverse
        val subst =
          VariableSubst(0, consts, order)
        // TODO: switch to sorted variables at this point
        val backSubst =
          (for ((c, n) <- consts.iterator.zipWithIndex)
           yield (c -> IVariable(n))).toMap

        for (c <- cs) yield {
          val raw = sf.postprocessing(subst(c),
                                      simplify = true,
                                      int2TermTranslation = true)
          ConstantSubstVisitor(raw, backSubst)
        }
      }
    }
  
}
