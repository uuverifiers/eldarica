/**
 * Copyright (c) 2016-2018 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.preprocessor

import lazabs.horn.bottomup.HornClauses
import HornClauses._
import lazabs.horn.bottomup.Util.{Dag, DagNode, DagEmpty}

import ap.basetypes.IdealInt
import ap.parser._
import IExpression._
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet, ArrayStack}

/**
 * Simple pre-processor that removes clauses that are unreachable from the entry
 * clauses, or from which no assertions clauses are reachable.
 */
object ReachabilityChecker extends HornPreprocessor {

  import HornPreprocessor._

  val name : String = "eliminating fwd/bwd unreachable clauses"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val allPredicates = HornClauses allPredicates clauses

    ////////////////////////////////////////////////////////////////////////////
    // check fwd reachability
    val fwdReachable, fwdUnreachable = new MHashSet[Predicate]

    val fwdReachableClauses = {
      val workList = new ArrayStack[Predicate]

      // add entry predicates
      for (Clause(IAtom(p, _), Seq(), _) <- clauses)
        if (fwdReachable add p)
          workList push p

      // fixed-point iteration
      val clausesWithBodyPred =
        (for (clause@Clause(_, body, _) <- clauses;
              IAtom(p, _) <- body)
         yield (p, clause)) groupBy (_._1)
    
      while (!workList.isEmpty) {
        val pred = workList.pop

        for ((_, Clause(IAtom(headPred, _), body, _)) <-
               clausesWithBodyPred.getOrElse(pred, List()))
          if (!(fwdReachable contains headPred) &&
              (body forall { case IAtom(p, _) => fwdReachable contains p })) {
            fwdReachable += headPred
            workList push headPred
          }
      }

      for (clause <- clauses; if clause.predicates subsetOf fwdReachable)
      yield clause
    }

    ////////////////////////////////////////////////////////////////////////////
    // check bwd reachability
    val bwdReachable = new MHashSet[Predicate]

    val bwdReachableClauses = {
      val workList = new ArrayStack[Predicate]

      // FALSE is exit
      bwdReachable += HornClauses.FALSE
      workList push HornClauses.FALSE

      // fixed-point iteration
      val clausesWithHeadPred = fwdReachableClauses groupBy (_.head.pred)

      while (!workList.isEmpty) {
        val pred = workList.pop

        for (Clause(_, body, _) <- clausesWithHeadPred.getOrElse(pred, List()))
          for (IAtom(p, _) <- body)
            if (bwdReachable add p)
              workList push p
      }
      
      for (clause <- clauses; if clause.predicates subsetOf bwdReachable)
      yield clause
    }

    ////////////////////////////////////////////////////////////////////////////
    // Back-translation of solutions

    val translator = new BackTranslator {
      def translate(solution : Solution) =
        if (solution.size == allPredicates.size)
          solution
        else
          solution ++ (
            for (pred <- allPredicates.iterator;
                 if !(bwdReachable contains pred)) yield {
              if (fwdReachable contains pred)
                (pred, i(true))
              else
                (pred, i(false))
            })
        
      def translate(cex : CounterExample) = cex
    }

    (bwdReachableClauses, hints filterPredicates bwdReachable, translator)
  }

}