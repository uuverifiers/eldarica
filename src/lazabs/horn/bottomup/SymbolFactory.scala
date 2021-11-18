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
import ap.parameters.{PreprocessingSettings, GoalSettings, Param,
                      ReducerSettings}
import ap.terfor.{ConstantTerm, TerForConvenience, TermOrder}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction, Quantifier,
                               SeqReducerPluginFactory}
import ap.theories.Theory
import ap.types.Sort

import scala.collection.mutable.ArrayBuffer

object SymbolFactory {
  val normalPreprocSettings = PreprocessingSettings.DEFAULT
  val clausifyPreprocSettings = Param.CLAUSIFIER.set(normalPreprocSettings,
                                                     Param.ClausifierOptions.Simple)

  val SKOLEM_BATCH_SIZE_INIT  = 1 << 8
  val SKOLEM_BATCH_SIZE_LIMIT = 1 << 16
}

  class SymbolFactory(theories : Seq[Theory]) {
    import HornClauses._
    import TerForConvenience._
    import SymbolFactory._

    private val constantsToAdd = new ArrayBuffer[ConstantTerm]

    val functionalPreds =
      (for (t <- theories.iterator;
            p <- t.functionalPredicates.iterator) yield p).toSet

    val reducerSettings = {
      var rs = ReducerSettings.DEFAULT
      rs = Param.FUNCTIONAL_PREDICATES.set(
             rs, functionalPreds)
      rs = Param.REDUCER_PLUGIN.set(
             rs, SeqReducerPluginFactory(
                   for (t <- theories) yield t.reducerPlugin))
      rs
    }

    private var orderVar : TermOrder = TermOrder.EMPTY
    private val functionEnc =
      new FunctionEncoder(
        Param.TIGHT_FUNCTION_SCOPES(PreprocessingSettings.DEFAULT),
        Param.GENERATE_TOTALITY_AXIOMS(PreprocessingSettings.DEFAULT))

    for (t <- theories) {
      orderVar = t extend orderVar
      functionEnc addTheory t
    }

    def order : TermOrder = {
      if (!constantsToAdd.isEmpty) {
        orderVar = orderVar extend constantsToAdd
        constantsToAdd.clear
      }
      orderVar
    }

    def postprocessing =
      new Postprocessing(signature, functionEnc.predTranslation)

    def genConstant(name : String) : ConstantTerm = {
      val res = new ConstantTerm(name)
      constantsToAdd += res
      res
    }

    private var skolemCounter = 0

    private var skolemBatchSize = SKOLEM_BATCH_SIZE_INIT
    private var skolemConstIt : Iterator[ConstantTerm] = Iterator.empty

    def genSkolemConstant : ConstantTerm = {
      if (!skolemConstIt.hasNext) {
        // declare the Skolem constants in batches; otherwise the
        // frequent changes of the term order slows down translation
        // of clauses to NormClause
        skolemConstIt =
          (for (_ <- 0 until skolemBatchSize) yield {
             val num = skolemCounter
             skolemCounter = skolemCounter + 1
             genConstant("sk" + num)
           }).toIndexedSeq.iterator

        if (skolemBatchSize < SKOLEM_BATCH_SIZE_LIMIT)
          skolemBatchSize = skolemBatchSize * 2
      }

      skolemConstIt.next
    }

    def addSymbol(c : ConstantTerm) : Unit =
      constantsToAdd += c
    def addSymbols(cs : Seq[ConstantTerm]) : Unit =
      constantsToAdd ++= cs
    
    def reducer(assumptions : Conjunction) =
      ReduceWithConjunction(assumptions, order, reducerSettings)
    def reduce(c : Conjunction) =
      reducer(Conjunction.TRUE)(c)
    
    def genConstants(prefix : String,
                     num : Int, suffix : String) : Seq[ConstantTerm] = {
      val res = for (i <- 0 until num)
                yield new ConstantTerm(prefix + "_" + i + "_" + suffix)
      addSymbols(res)
      res
    }

    def genConstants(prefix : String,
                     sorts : Seq[Sort],
                     suffix : String) : Seq[ConstantTerm] = {
      val res = (for ((s, i) <- sorts.iterator.zipWithIndex)
                 yield s.newConstant(prefix + "_" + i + "_" + suffix)).toList
      addSymbols(res)
      res
    }

    def duplicateConstants(cs : Seq[ConstantTerm]) = {
      val res = for (c <- cs) yield c.clone
      addSymbols(res)
      res
    }
      
    def signature =
      Signature(Set(), Set(), order.orderedConstants, Map(), order, theories)

    def toInternal(f : IFormula) : Conjunction =
      HornPredAbs.toInternal(f, signature, functionEnc,
                             normalPreprocSettings)

    def toInternalClausify(f : IFormula) : Conjunction =
      HornPredAbs.toInternal(f, signature, functionEnc,
                             clausifyPreprocSettings)

    def preprocess(f : Conjunction) : Conjunction =
      if (theories.isEmpty) f else !Theory.preprocess(!f, theories, order)
  }
