/**
 * Copyright (c) 2016-2020 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.abstractions

import ap.parser._
import IExpression._

import scala.collection.{Set => GSet}

object VerificationHints {
  def apply(hints : Map[IExpression.Predicate, Seq[VerifHintElement]]) =
    new VerificationHints {
      val predicateHints = hints
    }

  abstract sealed class VerifHintElement {
    /**
     * Shift references to predicate arguments by the given <code>offset</code>
     * and <code>shift</code> (like in <code>VariableShiftVisitor</code>).
     */
    def shiftArguments(offset : Int, shift : Int) : VerifHintElement

    /**
     * Shift references to predicate arguments using the given mapping.
     * If the hint contains any reference not occurring in the given map,
     * <code>None</code> will be returned. Otherwise, every variable
     * <code>_i</code> will be replaced with <code>_(i + mapping(i))</code..
     */
    def shiftArguments(mapping : Map[Int, Int]) : Option[VerifHintElement]

    protected def shiftVars(t : IExpression,
                            mapping : Map[Int, Int]) : Option[IExpression] =
      if (ContainsSymbol(t,
            (f : IExpression) => f match {
              case IVariable(ind) => !(mapping contains ind)
              case _ => false
             }))
        None
      else
        Some(VariablePermVisitor(t, IVarShift(mapping, 0)))
  }

  //////////////////////////////////////////////////////////////////////////////
  
  abstract sealed class VerifHintTplElement(val cost : Int)
                                         extends VerifHintElement

  case class VerifHintTplIterationThreshold(threshold : Int)
                                         extends VerifHintElement {
    def shiftArguments(offset : Int, shift : Int)
                      : VerifHintTplIterationThreshold = this
    def shiftArguments(mapping : Map[Int, Int])
                      : Option[VerifHintTplIterationThreshold] = Some(this)
  }

  case class VerifHintInitPred(f : IFormula) extends VerifHintElement {
    def shiftArguments(offset : Int, shift : Int) : VerifHintInitPred =
      VerifHintInitPred(VariableShiftVisitor(f, offset, shift))
    def shiftArguments(mapping : Map[Int, Int]) : Option[VerifHintInitPred] =
      for (newF <- shiftVars(f, mapping))
      yield VerifHintInitPred(newF.asInstanceOf[IFormula])
  }
  
  case class VerifHintTplPred(f : IFormula, _cost : Int)
                                         extends VerifHintTplElement(_cost) {
    def shiftArguments(offset : Int, shift : Int) : VerifHintTplPred =
      VerifHintTplPred(VariableShiftVisitor(f, offset, shift), cost)
    def shiftArguments(mapping : Map[Int, Int]) : Option[VerifHintTplPred] =
      for (newF <- shiftVars(f, mapping))
      yield VerifHintTplPred(newF.asInstanceOf[IFormula], cost)
  }
  
  case class VerifHintTplPredPosNeg(f : IFormula, _cost : Int)
                                         extends VerifHintTplElement(_cost) {
    def shiftArguments(offset : Int, shift : Int) : VerifHintTplPredPosNeg =
      VerifHintTplPredPosNeg(VariableShiftVisitor(f, offset, shift), cost)
    def shiftArguments(mapping : Map[Int, Int])
                      : Option[VerifHintTplPredPosNeg] =
      for (newF <- shiftVars(f, mapping))
      yield VerifHintTplPredPosNeg(newF.asInstanceOf[IFormula], cost)
  }
  
  case class VerifHintTplEqTerm(t : ITerm, _cost : Int)
                                         extends VerifHintTplElement(_cost) {
    def shiftArguments(offset : Int, shift : Int) : VerifHintTplEqTerm =
      VerifHintTplEqTerm(VariableShiftVisitor(t, offset, shift), cost)
    def shiftArguments(mapping : Map[Int, Int]) : Option[VerifHintTplEqTerm] =
      for (newT <- shiftVars(t, mapping))
      yield VerifHintTplEqTerm(newT.asInstanceOf[ITerm], cost)
  }

  case class VerifHintTplInEqTerm(t : ITerm, _cost : Int)
                                         extends VerifHintTplElement(_cost) {
    def shiftArguments(offset : Int, shift : Int) : VerifHintTplInEqTerm =
      VerifHintTplInEqTerm(VariableShiftVisitor(t, offset, shift), cost)
    def shiftArguments(mapping : Map[Int, Int]) : Option[VerifHintTplInEqTerm] =
      for (newT <- shiftVars(t, mapping))
      yield VerifHintTplInEqTerm(newT.asInstanceOf[ITerm], cost)
  }

  case class VerifHintTplInEqTermPosNeg(t : ITerm, _cost : Int)
                                         extends VerifHintTplElement(_cost) {
    def shiftArguments(offset : Int, shift : Int) : VerifHintTplInEqTermPosNeg =
      VerifHintTplInEqTermPosNeg(VariableShiftVisitor(t, offset, shift), cost)
    def shiftArguments(mapping : Map[Int, Int])
                      : Option[VerifHintTplInEqTermPosNeg] =
      for (newT <- shiftVars(t, mapping))
      yield VerifHintTplInEqTermPosNeg(newT.asInstanceOf[ITerm], cost)
  }
}

////////////////////////////////////////////////////////////////////////////////

  /**
   * Trait for providing verification hints, associated with predicates
   * defining the analysed programs.
   */
  trait VerificationHints {
    import VerificationHints._

    val predicateHints : Map[IExpression.Predicate, Seq[VerifHintElement]]

    def isEmpty = predicateHints.isEmpty

    def filterPredicates(remainingPreds : GSet[IExpression.Predicate]) = {
      val remHints = predicateHints filterKeys remainingPreds
      VerificationHints(remHints)
    }

    def filterNotPredicates(removed : GSet[IExpression.Predicate]) =
      if (removed.isEmpty)
        this
      else
        VerificationHints(predicateHints -- removed)

    def duplicatePredicates(newPreds : Predicate => Iterable[Predicate]) =
      if (isEmpty)
        this
      else
        VerificationHints((for ((p, hints) <- predicateHints.iterator;
                                newP <- newPreds(p).iterator)
                           yield (newP, hints)).toMap)

    def addPredicateHints(
          hints : Map[IExpression.Predicate, Seq[VerifHintElement]]) =
      if (hints.isEmpty)
        this
      else
        VerificationHints(predicateHints ++ hints)

    def toInitialPredicates : Map[IExpression.Predicate, Seq[IFormula]] =
      (for ((p, hints) <- predicateHints.iterator;
            remHints = for (VerifHintInitPred(f) <- hints) yield f;
            if !remHints.isEmpty)
       yield (p -> remHints)).toMap

    def ++(that : VerificationHints) =
      if (that.isEmpty) {
        this
      } else if (this.isEmpty) {
        that
      } else {
        val allHints =
          predicateHints ++
          (for ((p, hints) <- predicateHints.iterator) yield
            (predicateHints get p) match {
              case Some(oldHints) => p -> (oldHints ++ hints)
              case None           => p -> hints
            })
        VerificationHints(allHints)
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  object EmptyVerificationHints extends VerificationHints {
    import VerificationHints._

    val predicateHints = Map[IExpression.Predicate, Seq[VerifHintElement]]()
    override def filterPredicates(
                   remainingPreds : GSet[IExpression.Predicate]) = this
    override def toInitialPredicates : Map[IExpression.Predicate, Seq[IFormula]] =
      Map()
  }

  class InitPredicateVerificationHints(preds : Map[Predicate, Seq[IFormula]])
        extends VerificationHints {
    import VerificationHints._
    val predicateHints = preds mapValues { l => l map (VerifHintInitPred(_)) }
  }

  //////////////////////////////////////////////////////////////////////////////

