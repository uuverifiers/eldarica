/**
 * Copyright (c) 2011-2025 Philipp Ruemmer. All rights reserved.
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

import lazabs.GlobalParameters
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.concurrency.ReaderMain
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts

import ap.basetypes.IdealInt
import ap.theories.nia.GroebnerMultiplication
import ap.theories.rationals.Rationals
import ap.theories.bitvectors.ModuloArithmetic.ModSort
import ap.parser._
import ap.terfor.{VariableTerm, TermOrder, TerForConvenience}
import ap.terfor.linearcombination.LinearCombination

object StaticAbstractionBuilder {
  object AbstractionType extends Enumeration {
    val Empty, Term, Octagon, RelationalEqs, RelationalIneqs,
        RelationalEqs2, RelationalIneqs2 =
      Value
  }
}

/**
 * Class to extract hints and build abstraction lattices, given a set
 * of Horn clauses
 */
class StaticAbstractionBuilder(
         clauses : Seq[HornClauses.Clause],
         abstractionType : StaticAbstractionBuilder.AbstractionType.Value) {

  import IExpression._
  import HornClauses.Clause
  import VerificationHints._

  val loopDetector = new LoopDetector(clauses)

  Console.err.println("Loop heads:")

  //////////////////////////////////////////////////////////////////////////////

  def octagonAbstractions = VerificationHints(
    for ((loopHead, modifiedArgs) <-
           ModifiedLoopVarsDetector.simpleModifiedVars(loopDetector)) yield {
      val unmodArgsCosts =
        for (k <- 0 until loopHead.arity;
             if (!(modifiedArgs contains k))) yield (v(k) -> 1)
      val modArgsCosts =
        for (k <- modifiedArgs) yield (v(k) -> 6)

      val (diffCosts, sumCosts) =
        if (modifiedArgs.isEmpty) {
          (List(), List())
        } else {
          val modHead = modifiedArgs.head
          val diffCosts = (for (k <- modifiedArgs.iterator;
                                if (k != modHead)) yield ((v(modHead) - v(k)) -> 2)).toList
          val sumCosts =  (for (k <- modifiedArgs.iterator;
                                if (k != modHead)) yield ((v(modHead) + v(k)) -> 7)).toList
          (diffCosts, sumCosts)
        }

/*
      val diffCosts =
        (for ((k1, i1) <- modifiedArgs.iterator.zipWithIndex;
              (k2, i2) <- modifiedArgs.iterator.zipWithIndex;
              if (i1 < i2)) yield ((v(k1) - v(k2)) -> 3)).toList
      val sumCosts =
        (for ((k1, i1) <- modifiedArgs.iterator.zipWithIndex;
              (k2, i2) <- modifiedArgs.iterator.zipWithIndex;
              if (i1 < i2)) yield ((v(k1) + v(k2)) -> 10)).toList
*/

      Console.err.println("   " + loopHead +
              " (" + loopDetector.loopBodies(loopHead).size + " clauses, " +
              (unmodArgsCosts.size + modArgsCosts.size + diffCosts.size + sumCosts.size) + " templates)")

      (loopHead,
       for ((t, c) <- unmodArgsCosts ++ modArgsCosts ++ diffCosts ++ sumCosts)
       yield VerifHintTplEqTerm(t, c))
    })

  //////////////////////////////////////////////////////////////////////////////

  def termAbstractions = VerificationHints(
    for ((loopHead, argOffsets) <-
           ModifiedLoopVarsDetector.varOffsets(loopDetector)) yield {
      val counterArgs =
        (for ((v, k) <- argOffsets.iterator.zipWithIndex;
              if (v == List(IdealInt.ONE))) yield k).toList
      val modifiedArgs =
        (for ((v, k) <- argOffsets.iterator.zipWithIndex;
              if (v != List(IdealInt.ZERO))) yield k).toList

      val unmodArgsCosts =
        for (k <- 0 until loopHead.arity;
             if (!(modifiedArgs contains k))) yield (v(k) -> 1)
      val modArgsCosts =
        for (k <- 0 until loopHead.arity;
             if ((modifiedArgs contains k) &&
                 !(counterArgs contains k))) yield (v(k) -> 4)
      val counterArgsCosts =
        for (k <- counterArgs) yield (v(k) -> 9)

      Console.err.println("   " + loopHead +
              " (" + loopDetector.loopBodies(loopHead).size + " clauses, " +
              (unmodArgsCosts.size + modArgsCosts.size + counterArgsCosts.size) + " templates)")

      (loopHead,
       for ((t, c) <- unmodArgsCosts ++ modArgsCosts ++ counterArgsCosts)
       yield VerifHintTplEqTerm(t, c))
    })

  //////////////////////////////////////////////////////////////////////////////

  def emptyAbstractions = VerificationHints(
    for ((head, _) <- loopDetector.loopBodies) yield {
      Console.err.println("   " + head +
              " (" + loopDetector.loopBodies(head).size + " clauses)")
      // just create some unit lattice (with exactly one element)
      (head, List())
    })

  //////////////////////////////////////////////////////////////////////////////

  def relationAbstractions(ineqs : Boolean) = VerificationHints(
    for ((loopHead, argOffsets) <-
           ModifiedLoopVarsDetector.varOffsets(loopDetector)) yield {
      val modifiedArgs =
        (for ((v, k) <- argOffsets.iterator.zipWithIndex;
              if (v != List(IdealInt.ZERO))) yield k).toList

      val unmodArgsCosts =
        for (k <- 0 until loopHead.arity;
             if (!(modifiedArgs contains k))) yield (v(k) -> 1)
      val modArgsCosts =
        for (k <- modifiedArgs) yield (v(k) -> 6)

      val counter = (
         for ((List(o), k) <- argOffsets.iterator.zipWithIndex;
              if (o.isUnit)) yield k).toSeq.headOption              orElse (
         for ((l, k) <- argOffsets.iterator.zipWithIndex;
              if (l exists (_.isUnit))) yield k).toSeq.headOption   orElse (
         modifiedArgs.headOption)

      def handleEmpty(l : List[IdealInt]) : List[IdealInt] = l match {
        case List() => List(IdealInt.ONE, IdealInt.MINUS_ONE)
        case l => l
      }

      val offsetDiffCosts = counter match {
        case Some(counterInd) =>
          (for (o1 <- handleEmpty(argOffsets(counterInd)).iterator;
                if (!o1.isZero);
                (l2, i2) <- argOffsets.iterator.zipWithIndex;
                if (i2 != counterInd);
                o2 <- handleEmpty(l2).iterator;
                if (!o2.isZero);
                (op1, op2) = if (o2.signum >= 0) (o1, o2) else (-o1, -o2))
           yield ((v(counterInd)*op2 - v(i2)*op1) -> 2)).toList.distinct
        case None =>
          List()
      }

/*
      val modCosts = 
        (for ((offsets, k) <- argOffsets.iterator.zipWithIndex;
              if (offsets match {
                case List(o) => !o.isZero && !o.isUnit
                case _ => false
              }))
        yield (GroebnerMultiplication.eMod(v(k), offsets.head.abs) -> 2)).toList
*/

      Console.err.println("   " + loopHead +
              " (" + loopDetector.loopBodies(loopHead).size + " clauses, " +
              (unmodArgsCosts.size + modArgsCosts.size +
               offsetDiffCosts.size /* + modCosts.size */) + " templates)")

      val allCosts =
        unmodArgsCosts ++ modArgsCosts ++ offsetDiffCosts // ++ modCosts

      (loopHead,
       if (ineqs)
         for ((t, c) <- allCosts) yield VerifHintTplInEqTermPosNeg(t, c)
       else
         for ((t, c) <- allCosts) yield VerifHintTplEqTerm(t, c))
    })

  //////////////////////////////////////////////////////////////////////////////

  def lcRelationAbstractions(ineqs : Boolean) = VerificationHints(
    for ((loopHead, argTransformations) <-
           ModifiedLoopVarsDetector.linearTransformations(loopDetector)) yield {
      implicit val order = TermOrder.EMPTY
      implicit val lcOrder = order.lcOrdering

      def effectiveSort(s : Sort) : Sort =
        s match {
          case Sort.Numeric(_) => Sort.Integer
          case Rationals.dom   => Sort.Integer
          case _               => s
        }

      def toTemplate(term : ITerm, cost : Int, s : Sort) =
        s match {
          case Sort.Numeric(_) | Rationals.dom | _ : ModSort if ineqs =>
            VerifHintTplInEqTermPosNeg(term, cost)
          case _ =>
            VerifHintTplEqTerm(term, cost)
        }

      def incPattern(inc : Option[LinearCombination]) : LinearCombination =
        inc match {
          case Some(lc) if !lc.isConstant => lc.makePrimitiveAndPositive
          case _                          => LinearCombination.ONE
        }

      def effectiveInc(inc : Option[LinearCombination]) : LinearCombination =
        inc match {
          case Some(lc) => lc
          case _        => LinearCombination.ONE
        }

      val argIncrements = {
        import TerForConvenience._
        (for ((t, n) <- argTransformations.zipWithIndex) yield {
           for (lc <- t; if lc.get(v(n)).isOne)
           yield lc - l(v(n))
         }).toVector
      }

      val unmodifiedArgs =
        (for ((Some(lc), n) <- argIncrements.iterator.zipWithIndex;
              if lc.isZero)
         yield n).toSet

      val argSorts = predArgumentSorts(loopHead)

      val singleArgTemplates =
        for ((s, k) <- argSorts.zipWithIndex) yield {
          val cost = if (unmodifiedArgs(k)) 1 else 6
          toTemplate(v(k), cost, s)
        }

      val argsPerSort = argSorts.zipWithIndex.groupBy(p => effectiveSort(p._1))

      val intTemplates =
        for (args <- argsPerSort.get(Sort.Integer).toSeq;
             increments = (for ((_, n) <- args.iterator; if !unmodifiedArgs(n))
                           yield (n -> argIncrements(n))).toVector;
             incGroups = increments.groupBy(p => incPattern(p._2));
             (_, argsIncs) <- incGroups.toVector.sortBy(_._1);
             if argsIncs.size > 1;
             effArgsIncs = argsIncs.map(p => (p._1, effectiveInc(p._2)));
             (masterInd, masterInc) = effArgsIncs.head;
             (otherInd, otherInc) <- effArgsIncs.tail)
        yield {
          val term = (v(masterInd) *** otherInc.leadingCoeff) +
                     (v(otherInd) *** -masterInc.leadingCoeff)
          val cost = 2
          toTemplate(term, cost, Sort.Integer)
        }

      val otherTemplates =
        for ((sort, args) <- argsPerSort; if sort != Sort.Integer;
             relevantArgs = for ((_, n) <- args; if !unmodifiedArgs(n)) yield n;
             if relevantArgs.size > 1;
             masterInd = relevantArgs.head;
             otherInd <- relevantArgs.tail)
        yield {
          toTemplate(v(masterInd) - v(otherInd), 2, sort)
        }

      val bvTemplates =
        for ((sort, args) <- argsPerSort; if sort.isInstanceOf[ModSort];
             relevantArgs = for ((_, n) <- args; if !unmodifiedArgs(n)) yield n;
             if relevantArgs.size > 1;
             masterInd = relevantArgs.head;
             otherInd <- relevantArgs.tail)
        yield {
          toTemplate(v(masterInd) + v(otherInd), 2, sort)
        }

      val allTemplates =
        singleArgTemplates ++ intTemplates ++ otherTemplates ++ bvTemplates

      Console.err.println("   " + loopHead +
         " (" + loopDetector.loopBodies(loopHead).size + " clauses, " +
         allTemplates.size + " templates)")

      (loopHead, allTemplates)
    })

  //////////////////////////////////////////////////////////////////////////////

  import StaticAbstractionBuilder._

  val abstractionHints : VerificationHints =
    abstractionType match {
      case AbstractionType.Empty =>
        emptyAbstractions
      case AbstractionType.Term =>
        termAbstractions
      case AbstractionType.Octagon =>
        octagonAbstractions
      case AbstractionType.RelationalEqs =>
        relationAbstractions(false)
      case AbstractionType.RelationalEqs2 =>
        lcRelationAbstractions(false)
      case AbstractionType.RelationalIneqs =>
        relationAbstractions(true)
      case AbstractionType.RelationalIneqs2 =>
        lcRelationAbstractions(true)
    }

  if (GlobalParameters.get.templateBasedInterpolationPrint)
    AbsReader printHints abstractionHints

  val abstractionRecords : AbstractionRecord.AbstractionMap =
    loopDetector.hints2AbstractionRecord(abstractionHints)

}
