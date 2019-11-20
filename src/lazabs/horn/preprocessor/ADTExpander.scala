/**
 * Copyright (c) 2019 Philipp Ruemmer. All rights reserved.
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
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts

import ap.parser._
import ap.theories.ADT

import scala.collection.mutable.{HashMap => MHashMap}


// Under development ...



object ADTExpander {

  /**
   * Interface for adding auxiliary predicate arguments for ADT types
   */
  trait Expansion {

    /**
     * Decide whether to expand an ADT sort should be expanded. In
     * this case, the method returns sorts of new terms to be added as
     * arguments, as well as a function that maps the ADT term to the
     * auxiliary terms.
     */
    def expand(sort : ADT.ADTProxySort)
             : Option[(Seq[IExpression.Sort], ITerm => (Seq[ITerm], IFormula))]


//    def expand(argument : ITerm, sort : ADT.ADTProxySort)
//             : Option[(Seq[(ITerm, IExpression.Sort)], IFormula)]

    protected def getNewSymNumber : Int = {
      val res = symbolCounter
      symbolCounter = symbolCounter + 1
      res
    }

    private var symbolCounter = 0

  }

  /**
   * Preprocessor that adds explicit size arguments for each predicate
   * argument for a recursive ADT
   */
  class SizeArgumentAdder extends Expansion {

    import IExpression._

    def expand(sort : ADT.ADTProxySort)
             : Option[(Seq[IExpression.Sort],
                       ITerm => (Seq[ITerm], IFormula))] =
      if (recursiveADTSorts.getOrElseUpdate(sort, isRecursive(sort))) {
        val sizefun = sort.adtTheory.termSize(sort.sortNum)
        def termgen(t : ITerm) : (Seq[ITerm], IFormula) = {
          val sizeConst = new ConstantTerm ("adt_size_" + getNewSymNumber)
          val sizeTerm = IConstant(sizeConst)
          (List(sizeTerm), sizeTerm === sizefun(t))
        }
        Some((List(Sort.Integer), termgen _))
      } else {
        None
      }

    private val recursiveADTSorts = new MHashMap[ADT.ADTProxySort, Boolean]

    private def isRecursive(sort : ADT.ADTProxySort) : Boolean =
      isRecursive(sort.sortNum, List(), sort.adtTheory)

    private def isRecursive(sortNum : Int,
                            seenSorts : List[Int],
                            adt : ADT)  : Boolean =
      if (seenSorts contains sortNum) {
        true
      } else {
        val newSeen = sortNum :: seenSorts
        (for (ctor <- adt.constructors.iterator;
              sort <- ctor.argSorts.iterator)
         yield sort) exists {
           case sort : ADT.ADTProxySort if sort.adtTheory == adt =>
             isRecursive(sort.sortNum, newSeen, adt)
           case _ =>
             false
         }
      }

  }

}

////////////////////////////////////////////////////////////////////////////////

class ADTExpander(val name : String,
                  expansion : ADTExpander.Expansion) extends HornPreprocessor {
  import HornPreprocessor._

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val predicates = HornClauses allPredicates clauses
    println(predicates)

    for (pred <- predicates) {
      val sorts = predArgumentSorts(pred)
      println(pred)
      println(sorts)
      val newSorts =
        for (sort <- sorts;
             s <-
               if (sort.isInstanceOf[ADT.ADTProxySort])
                 (expansion expand sort.asInstanceOf[ADT.ADTProxySort]) match {
                   case Some((addSorts, arggen)) =>
                     List(sort) ++ addSorts
                   case None =>
                     List(sort)
                 }
               else
                 List(sort))
        yield s
      println(newSorts)
    }

    (clauses, hints, HornPreprocessor.IDENTITY_TRANSLATOR)
  }

//  private def expand(sort : Sort) : List

}


/**
 * Preprocessor that adds explicit size arguments for each predicate
 * argument for a recursive ADT
 */
class SizeArgumentExtender extends ADTExpander("adding size arguments",
                                               new ADTExpander.SizeArgumentAdder) {

}
