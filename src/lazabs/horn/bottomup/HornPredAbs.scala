/**
 * Copyright (c) 2011-2021 Philipp Ruemmer. All rights reserved.
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

import ap.Signature
import ap.parser._
import ap.parameters.PreprocessingSettings
import ap.terfor.{ConstantTerm, TerForConvenience}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.preds.Predicate
import ap.terfor.substitutions.ConstantSubst
import ap.proof.QuantifierElimProver
import ap.theories.TheoryCollector
import ap.types.{Sort, MonoSortedPredicate}

import Util._
import DisjInterpolator._

object HornPredAbs {

  import HornClauses._
  import TerForConvenience._
  import SymbolFactory.normalPreprocSettings

  def predArgumentSorts(pred : Predicate) : Seq[Sort] =
    MonoSortedPredicate argumentSorts pred

  def toInternal(f : IFormula, sig : Signature) : Conjunction =
    toInternal(f, sig, null, normalPreprocSettings)

  def toInternal(f : IFormula,
                 sig : Signature,
                 functionEnc : FunctionEncoder,
                 settings : PreprocessingSettings) : Conjunction = {
    implicit val order = sig.order
    val (fors, _, _) =
      if (functionEnc == null)
        Preprocessing(~f, List(), sig, settings)
      else
        Preprocessing(~f, List(), sig, settings, functionEnc)
    ReduceWithConjunction(Conjunction.TRUE, order)(conj(InputAbsy2Internal(
      IExpression.or(for (f <- fors) yield IExpression removePartName f), order)).negate)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  implicit def normClause2ConstraintClause(nc : NormClause) = {
    val NormClause(_, bodyLits, (RelationSymbol(headPred), _)) = nc

    new ConstraintClause {
      def head : Literal = new Literal {
        val predicate = headPred
        val relevantArguments = (0 until predicate.arity).toSeq
      }
      def body : Seq[Literal] =
        (for (((RelationSymbol(pred), _), relSyms) <-
              bodyLits.iterator zip nc.relevantBodySyms.iterator)
         yield new Literal {
           val predicate = pred
           val relevantArguments = relSyms
         }).toSeq
      def localVariableNum : Int = nc.localSymbols.size
      def instantiateConstraint(headArguments : Seq[ConstantTerm],
                                bodyArguments: Seq[Seq[ConstantTerm]],
                                localVariables : Seq[ConstantTerm],
                                sig : Signature) : Conjunction =
        nc.substituteSyms(localVariables, headArguments, bodyArguments)(sig.order)
      override def collectTheories(coll : TheoryCollector) : Unit =
        coll(nc.constraint.order)
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

class HornPredAbs[CC <% HornClauses.ConstraintClause]
                 (iClauses : Iterable[CC],
                  initialPredicates : Map[Predicate, Seq[IFormula]],
                  predicateGenerator : Dag[AndOrNode[NormClause, Unit]] =>
                                       Either[Seq[(Predicate, Seq[Conjunction])],
                                              Dag[(IAtom, NormClause)]],
                  counterexampleMethod : CEGAR.CounterexampleMethod.Value =
                                           CEGAR.CounterexampleMethod.FirstBestShortest) {
  
  import HornPredAbs._

  val hornPredAbsStartTime = System.currentTimeMillis

  lazabs.GlobalParameters.get.setupApUtilDebug
  
  val context : HornPredAbsContext[CC] = new HornPredAbsContextImpl(iClauses)
  import context._

  val predStore = new PredicateStore(context)
  import predStore._

  //////////////////////////////////////////////////////////////////////////////

  // Initialise with given initial predicates
  predStore.addIPredicates(initialPredicates)

  //////////////////////////////////////////////////////////////////////////////
  
  val cegar = new CEGAR(context, predStore,
                        predicateGenerator, counterexampleMethod)
  import cegar._
  import CEGAR._

  val rawResult = cegar.rawResult

  if (lazabs.GlobalParameters.get.log)
    println

  println
  printStatistics(hornPredAbsStartTime)
  println

  //////////////////////////////////////////////////////////////////////////////

  /**
   * A set of predicates that is sufficient to solve the set of Horn clauses.
   */
  lazy val relevantRawPredicates : Map[Predicate, Seq[Conjunction]] = {
    import TerForConvenience._
    implicit val order = sf.order

    (for ((rs, preds) <- maxAbstractStates.iterator;
          if (rs.pred != HornClauses.FALSE)) yield {
      val symMap =
       (rs.arguments.head.iterator zip (
           for (i <- 0 until rs.arity) yield v(i)).iterator).toMap
      val subst = ConstantSubst(symMap, order)

      val allPreds =
        (for (AbstractState(_, fors) <- preds.iterator;
              f <- fors.iterator) yield subst(f.posInstances.head)).toList
             
      rs.pred -> allPreds.distinct
    }).toMap
  }

  /**
   * A set of predicates that is sufficient to solve the set of Horn clauses.
   */
  lazy val relevantPredicates : Map[Predicate, Seq[IFormula]] =
    for ((p, preds) <- relevantRawPredicates) yield {
      p -> convertToInputAbsy(p, preds)
    }

  //////////////////////////////////////////////////////////////////////////////

  lazy val relevantDisjuncts : Map[Predicate, Seq[Conjunction]] = {
    import TerForConvenience._
    implicit val order = sf.order

    (for ((rs, preds) <- maxAbstractStates.iterator;
          if (rs.pred != HornClauses.FALSE)) yield {
      val symMap =
       (rs.arguments.head.iterator zip (
           for (i <- 0 until rs.arity) yield v(i)).iterator).toMap
      val subst = ConstantSubst(symMap, order)

      val allPreds =
        (for (AbstractState(_, fors) <- preds.iterator;
              if (!fors.isEmpty)) yield {
          val g = conj(for (f <- fors.iterator) yield f.posInstances.head)
          subst(!QuantifierElimProver(!g, true, order))
        }).toList
             
      rs.pred -> allPreds.distinct
    }).toMap
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * The result of CEGAR: either a solution of the Horn clauses, or
   * a counterexample DAG containing the predicates and clauses.
   */
  lazy val result : Either[Map[Predicate, IFormula],
                           Dag[(IAtom, CC)]] = rawResult match {
    case Left(solution) =>
      Left(for ((p, c) <- solution)
           yield (p, convertToInputAbsy(p, List(c)).head))
    case Right(trace) =>
      Right(trace)
  }

}

