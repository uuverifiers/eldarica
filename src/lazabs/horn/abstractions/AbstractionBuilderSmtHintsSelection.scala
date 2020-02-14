/**
 * Copyright (c) 2011-2019 Philipp Ruemmer. All rights reserved.
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

import java.io.{File, PrintWriter}

import ap.basetypes.IdealInt
import ap.parser._
import lazabs.GlobalParameters
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.bottomup.{HornClauses, HornPredAbs}
import lazabs.horn.concurrency.HintsSelection.initialIDForHints
import lazabs.horn.concurrency._
import lazabs.horn.global.HornClause
import lazabs.horn.preprocessor.HornPreprocessor.Clauses
import lazabs.viewer.HornPrinter

import scala.collection.immutable.ListMap

//object StaticAbstractionBuilderSmtHintsSelection {
//  object AbstractionType extends Enumeration {
//    val Empty, Term, Octagon, RelationalEqs, RelationalIneqs = Value
//  }
//}

/**
 * Class to extract hints and build abstraction lattices, given a set
 * of Horn clauses
 */
class StaticAbstractionBuilderSmtHintsSelection(
         clauses : Seq[HornClauses.Clause],
         abstractionType : StaticAbstractionBuilder.AbstractionType.Value,
         counterexampleMethod : HornPredAbs.CounterexampleMethod.Value =
         HornPredAbs.CounterexampleMethod.FirstBestShortest,
         simpHints:VerificationHints,
         clauseSet: Seq[HornClause]) {

  import IExpression._
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
      case AbstractionType.RelationalIneqs =>
        relationAbstractions(true)
    }

  if (GlobalParameters.get.templateBasedInterpolationPrint)
    ReaderMain printHints abstractionHints
//////////////////////////////////////////////////////////////////////////////////////////
  //select hints here

  val hintsAbstraction : AbstractionMap =
    if (simpHints.isEmpty)
      Map()
    else
      loopDetector hints2AbstractionRecord simpHints
  val sortedHints=HintsSelection.sortHints(abstractionHints)
  var optimizedHints=sortedHints
  if(sortedHints.isEmpty){
    println("No hints generated")
  }else{
    //write selected hints with IDs to file
    val InitialHintsWithID=initialIDForHints(sortedHints) //ID:head->hint
    println("---initialHints-----")
    for (wrappedHint<-InitialHintsWithID){
      println(wrappedHint.ID.toString,wrappedHint.head,wrappedHint.hint)
    }

    val selectedHint=HintsSelection.tryAndTestSelectionTemplatesSmt(sortedHints,
      clauses,GlobalParameters.get.fileName,InitialHintsWithID,counterexampleMethod,hintsAbstraction)
    optimizedHints=selectedHint
    if(selectedHint.isEmpty){ //when no hint available
      println("No hints selected (no need for hints)")
      //not write horn clauses to file
    }else{
      //write argument score to file
      val argumentList=(for (p <- HornClauses.allPredicates(clauses)) yield (p, p.arity)).toList
      HintsSelection.writeArgumentScoreToFile(GlobalParameters.get.fileName,argumentList,selectedHint)

      //Output graphs
      //val hornGraph = new GraphTranslator(clauses, GlobalParameters.get.fileName)
      DrawHornGraph.writeHornClausesGraphToFile(GlobalParameters.get.fileName,clauses,sortedHints)
      val hintGraph= new GraphTranslator_hint(clauses, GlobalParameters.get.fileName, sortedHints,InitialHintsWithID)

      //write horn clauses to file
      val fileName=GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/")+1)
      val writer = new PrintWriter(new File("../trainData/"+fileName+".horn")) //python path
      writer.write(HornPrinter(clauseSet))
      writer.close()
      //HintsSelection.writeHornClausesToFile(system,GlobalParameters.get.fileName)
      //write smt2 format to file
      if(GlobalParameters.get.fileName.endsWith(".c")){ //if it is a c file
        HintsSelection.writeSMTFormatToFile(clauses,"../trainData/")  //write smt2 format to file
      }
      if(GlobalParameters.get.fileName.endsWith(".smt2")){ //if it is a smt2 file
        //copy smt2 file
        val fileName=GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/")+1)
        HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../trainData/"+fileName)
      }


    }

  }

  //////////////////////////////////////////////////////////////////////////////////////////


  val abstractionRecords : AbstractionRecord.AbstractionMap =
    loopDetector.hints2AbstractionRecord(optimizedHints)

}
