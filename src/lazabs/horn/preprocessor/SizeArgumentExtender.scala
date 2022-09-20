/**
 * Copyright (c) 2019-2022 Philipp Ruemmer. All rights reserved.
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

import ap.parser._
import IExpression.{Predicate, Sort, and}
import ap.theories.{ADT, Theory}
import ap.types.MonoSortedPredicate

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer,
                                 LinkedHashMap, HashSet => MHashSet}

/**
 * Preprocessor that adds explicit size arguments for each predicate
 * argument for a recursive ADT
 */
class SizeArgumentExtender extends ArgumentExpander {

  import IExpression._
  import HornPreprocessor.Clauses

  val name = "adding size arguments"

  def expand(pred : Predicate, argNum : Int, sort : Sort)
           : Option[(Seq[(ITerm, Sort, String)], Option[ITerm])] = {
    val adtSort = sort.asInstanceOf[ADT.ADTProxySort]
    if ((usedTheories contains adtSort.adtTheory) &&
          adtSort.adtTheory.termSize != null &&
          recursiveADTSorts.getOrElseUpdate(adtSort, isRecursive(adtSort))) {
      val sizefun = adtSort.adtTheory.termSize(adtSort.sortNum)
      Some((List((sizefun(v(0)), Sort.Nat, "adt_size")), None))
    } else {
      None
    }
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

  override def setup(clauses : Clauses,
                     frozenPredicates : Set[Predicate]) : Unit = {
    usedTheories.clear
    for (clause <- clauses)
      usedTheories ++= clause.theories
  }

  private val usedTheories = new MHashSet[Theory]

  def isExpandableSort(s : Sort) : Boolean = s.isInstanceOf[ADT.ADTProxySort]

}
