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

import ap.DialogUtil
import ap.parser._
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.terfor.{Term, ConstantTerm, TerForConvenience}
import ap.terfor.substitutions.ConstantSubst

import Util._

case class RelationSymbol(pred : Predicate)(implicit val sf : SymbolFactory) {
  import HornPredAbs.predArgumentSorts

  def arity = pred.arity
  def name = pred.name
  val argumentSorts = predArgumentSorts(pred)
  val arguments = toStream {
    case i => sf.genConstants(name, argumentSorts, "" + i)
  }

  val argumentITerms = arguments map (_.map(IExpression.i(_)))
  override def toString = toString(0)
  def toString(occ : Int) = name + "(" + (arguments(occ) mkString ", ") + ")"
}

object RelationSymbolPred {
  def apply(rawPred : Conjunction,
            positive : Conjunction,
            negative : Conjunction,
            rs : RelationSymbol) =
    new RelationSymbolPred(rawPred, positive, negative, rs)
}

class RelationSymbolPred(val rawPred : Conjunction,
                         val positive : Conjunction,
                         val negative : Conjunction,
                         val rs : RelationSymbol) {
  import TerForConvenience._

  private val sf = rs.sf
  private val argConsts = rs.arguments.head

  private def substMap(from : Seq[ConstantTerm],
                       to : Seq[ConstantTerm])
                     : Map[ConstantTerm, Term] =
    (for ((oriC, newC) <- from.iterator zip to.iterator)
     yield (oriC -> l(newC)(sf.order))).toMap

  private def instanceStream(f : Conjunction) : Stream[Conjunction] =
    f #:: {
      for (cs <- rs.arguments.tail) yield {
        ConstantSubst(substMap(argConsts, cs), sf.order)(f)
      }
    }

  val posInstances = instanceStream(positive)
  val negInstances = instanceStream(negative)

  override def toString = DialogUtil.asString {
    PrincessLineariser.printExpression(
      rs.sf.postprocessing.processFormula(rawPred))
    //     print(positive)
    //     print(" / ")
    //     print(negative)
  }
}

