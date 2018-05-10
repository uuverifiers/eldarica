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

package lazabs.horn.bottomup

import ap.parameters.ReducerSettings
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.{ConstantTerm, TermOrder, TerForConvenience}
import ap.util.Seqs

import scala.collection.mutable.{ArrayBuffer, BitSet => MBitSet}

object IHasher {

  type Model = Conjunction

}

abstract class IHasher {

  import IHasher.Model

  /**
   * Make the hasher watch the given formula. The formula can be referred
   * to using the returned id.
   */
  def addFormula(f : Conjunction) : Int

  /**
   * Add a new model that is subsequently used for hashing.
   */
  def addModel(model : Model) : Unit

  def acceptsModels : Boolean

  def isActive : Boolean

  def printStatistics : Unit

  // API for checking satisfaction and implications

  def push : Unit
  def pop : Unit

  def scope[A](comp : => A) : A

  def assertFormula(forId : Int) : Unit

  def isSat : Boolean

  def mightBeImplied(forId : Int) : Boolean

}

////////////////////////////////////////////////////////////////////////////////

object Hasher {

  private abstract sealed class AssertionStackElement

  private case class AssertedFormula(id : Int)
                     extends AssertionStackElement
  private case class AssertionFrame(oldVector : MBitSet)
                     extends AssertionStackElement

  private def setBit(set : MBitSet, index : Int, value : Boolean) : Unit =
    if (value)
      set += index
    else
      set -= index

  private val maxModelNum = 1024

}

////////////////////////////////////////////////////////////////////////////////

object InactiveHasher extends IHasher {

  import IHasher._

  /**
   * Make the hasher watch the given formula. The formula can be referred
   * to using the returned id.
   */
  def addFormula(f : Conjunction) : Int = 0

  /**
   * Add a new model that is subsequently used for hashing.
   */
  def addModel(model : Model) : Unit = throw new UnsupportedOperationException

  def acceptsModels : Boolean = false

  def isActive : Boolean = false

  def printStatistics : Unit = {}

  // API for checking satisfaction and implications

  def push : Unit = {}
  def pop : Unit = {}

  def scope[A](comp : => A) : A = comp

  def assertFormula(forId : Int) : Unit = {}

  // false is a safe answer, since hashing is known to under-approximate
  def isSat : Boolean = false

  def mightBeImplied(forId : Int) : Boolean = true

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class to approximate sat and implication checks, by keeping a set of
 * models/structures that are used for evaluating formulas.
 */
class Hasher(globalOrder : TermOrder, reducerSettings : ReducerSettings)
      extends IHasher {

  import Hasher._
  import IHasher._
  private implicit val _ = globalOrder

  private val watchedFormulas = new ArrayBuffer[Conjunction]
  private val evalVectors = new ArrayBuffer[MBitSet]

  private val models = new ArrayBuffer[Model]
  private val reducers = new ArrayBuffer[ReduceWithConjunction]

  {
    // set up some default models
    import TerForConvenience._

    // all variables 0
    models +=
      (globalOrder.orderedConstants.toSeq === 0)

    // all variables distinct, increasing
    models +=
      conj(for ((c, n) <- globalOrder.orderedConstants.iterator.zipWithIndex)
           yield (c === (n+1)))

    // all variables distinct, decreasing
    models +=
      conj(for ((c, n) <- globalOrder.orderedConstants.iterator.zipWithIndex)
           yield (c === -(n+1)))

    for (m <- models)
      reducers += ReduceWithConjunction(m, globalOrder, reducerSettings)
  }

  private val presetModelNum = models.size

  //////////////////////////////////////////////////////////////////////////////

  var evalTime : Long = 0
  var evalNum : Int = 0
  def modelNum = models.size

  private def eval(modelIndex : Int, f : Conjunction) : Boolean = {
    import TerForConvenience._

    val startTime = System.currentTimeMillis

    val reduced1 = reducers(modelIndex) tentativeReduce f
    val reduced2 = reducers(0) tentativeReduce reduced1
    val res = reduced2.isTrue

    evalTime = evalTime + (System.currentTimeMillis - startTime)
    evalNum = evalNum + 1

    res
  }

  private def mergeModels(modelIndex : Int,
                          model2 : Model) : Option[Model] = {
    import TerForConvenience._
    if ((reducers(modelIndex) tentativeReduce model2).isFalse) {
      None
    } else {
      val res = models(modelIndex) & model2
      if (res.isFalse) None else Some(res)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Make the hasher watch the given formula. The formula can be referred
   * to using the returned id.
   */
  def addFormula(f : Conjunction) : Int = {
    val res = watchedFormulas.size
    watchedFormulas += f

    val evalVector = new MBitSet
    for (i <- 0 until models.size)
      if (eval(i, f))
        evalVector += i
    evalVectors += evalVector

//    println("Adding " + f + ": " + evalVector)

    res
  }

  /**
   * Add a new model that is subsequently used for hashing.
   */
  def addModel(model : Model) : Unit = {
//    println("Adding model ...")
    var i = presetModelNum
    var finished = false

    while (i < models.size && !finished)
      mergeModels(i, model) match {
        case Some(mergedModel) => {
          val changedConstants = model.constants filterNot models(i).constants
          models(i) = mergedModel
          reducers(i) = ReduceWithConjunction(mergedModel, globalOrder, reducerSettings)
//    println("Merged with #" + i)
          extendModelAndUpdateVectors(i, changedConstants)
          finished = true
        }
        case None =>
          i = i + 1
      }

    if (!finished) {
      i = models.size
      models += model
      reducers += ReduceWithConjunction(model, globalOrder, reducerSettings)
      extendEvalVectors(i)
//println("now have " + models.size + " models")
    }

    updateAssertionStack(i)
  }

  def acceptsModels : Boolean = models.size < maxModelNum

  //////////////////////////////////////////////////////////////////////////////

  private def extendEvalVectors(modelIndex : Int) : Unit = {
    val model = models(modelIndex)
    val assignedConstants = model.constants

    // update the stored vectors
    for (formulaIndex <- 0 until watchedFormulas.size) {
      val formula = watchedFormulas(formulaIndex)
      val vector = evalVectors(formulaIndex)

      val newBit =
        if (Seqs.disjoint(formula.constants, assignedConstants))
          // use existing model where all constants are assigned 0
          vector(0)
        else
          eval(modelIndex, formula)

      setBit(vector, modelIndex, newBit)
    }
  }

  private def extendModelAndUpdateVectors
                         (modelIndex : Int,
                          changedConstants : Set[ConstantTerm]) : Unit = {
      val model = models(modelIndex)

      // update the stored vectors
      for (formulaIndex <- 0 until watchedFormulas.size) {
        val formula = watchedFormulas(formulaIndex)
        if (!Seqs.disjoint(formula.constants, changedConstants)) {
          val newBit = eval(modelIndex, formula)
          setBit(evalVectors(formulaIndex), modelIndex, newBit)
        }
      }
    }

  private def updateAssertionStack(modelIndex : Int) : Unit = {
    var newBit = true
    for (el <- assertionStack) el match {
      case AssertedFormula(id) =>
        newBit = newBit && evalVectors(id)(modelIndex)
      case AssertionFrame(oldVector) =>
        if (oldVector != null)
          setBit(oldVector, modelIndex, newBit)
    }

    if (currentEvalVector != null)
      setBit(currentEvalVector, modelIndex, newBit)
  }

  def isActive : Boolean = true

  def printStatistics : Unit = {
    println("Number of models in hasher:                            " + modelNum)
    println("Number of hasher evals:                                " + evalNum)
    println("Time for hasher eval:                                  " + evalTime)
  }

  //////////////////////////////////////////////////////////////////////////////

  // API for checking satisfaction and implications

  def push : Unit =
    assertionStack += AssertionFrame(currentEvalVector)
  def pop : Unit = {
    var i = assertionStack.size - 1
    while (i >= 0) {
      assertionStack(i) match {
        case AssertionFrame(vec) => {
          currentEvalVector = vec
          assertionStack reduceToSize i
          return
        }
        case _ =>
          // nothing
      }
      i = i - 1
    }
  }

  def scope[A](comp : => A) : A = {
    push
    try {
      comp
    } finally {
      pop
    }
  }

  def assertFormula(forId : Int) : Unit = {
    assertionStack += AssertedFormula(forId)
    if (currentEvalVector == null)
      currentEvalVector = evalVectors(forId)
    else
      currentEvalVector = currentEvalVector & evalVectors(forId)
  }

  def isSat : Boolean =
    currentEvalVector == null || !currentEvalVector.isEmpty

  def mightBeImplied(forId : Int) : Boolean =
    currentEvalVector != null &&
    (currentEvalVector subsetOf evalVectors(forId))

  private var currentEvalVector : MBitSet = null
  private val assertionStack = new ArrayBuffer[AssertionStackElement]

}