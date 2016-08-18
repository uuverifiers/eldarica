/**
 * Copyright (c) 2016 Philipp Ruemmer. All rights reserved.
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

import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.{ConstantTerm, TermOrder, TerForConvenience}

import scala.collection.mutable.{ArrayBuffer, BitSet => MBitSet}

object Hasher {

  type Model = Conjunction

  private def eval(model : Model, f : Conjunction)
                  (implicit order : TermOrder) : Boolean = {
    import TerForConvenience._

    val undefConsts = f.constants filterNot model.constants
    val completeModel =
      if (undefConsts.isEmpty)
        model
      else
        model & (undefConsts.toSeq === 0)

    val reducer = ReduceWithConjunction(completeModel, order)
    reducer(f).isTrue
  }

}

/**
 * Class to approximate sat and implication checks, by keeping a set of
 * models/structures that are used for evaluating formulas.
 */
class Hasher(globalOrder : TermOrder) {

  import Hasher._
  private implicit val _ = globalOrder

  private val watchedFormulas = new ArrayBuffer[Conjunction]
  private val evalVectors = new ArrayBuffer[MBitSet]

  private val models = new ArrayBuffer[Model]

  {
    // set up some default models
    import TerForConvenience._

    // all variables 0
    models +=
      (globalOrder.orderedConstants.toSeq === 0)

    // all variables distinct, increasing
    models +=
      conj(for ((c, n) <- globalOrder.orderedConstants.iterator.zipWithIndex)
           yield (c === n))

    // all variables distinct, decreasing
    models +=
      conj(for ((c, n) <- globalOrder.orderedConstants.iterator.zipWithIndex)
           yield (c === -n))
  }

  //////////////////////////////////////////////////////////////////////////////

  def addFormula(f : Conjunction) : Int = {
    val res = watchedFormulas.size
    watchedFormulas += f

    val evalVector = new MBitSet
    for ((m, i) <- models.iterator.zipWithIndex)
      if (eval(m, f))
        evalVector += i
    evalVectors += evalVector

    println("Adding " + f + ": " + evalVector)

    res
  }

}