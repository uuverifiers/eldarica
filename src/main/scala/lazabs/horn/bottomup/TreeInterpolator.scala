/**
 * Copyright (c) 2011-2018 Philipp Ruemmer. All rights reserved.
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

import ap.basetypes.IdealInt
import ap.parameters.{Param, GoalSettings}
import ap.parser.PartName
import ap.theories.Theory
import ap.terfor.{ConstantTerm, TermOrder, TerForConvenience, Term,
                  ComputationLogger}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               ConjunctEliminator, NegatedConjunctions}
import ap.terfor.substitutions.ConstantSubst
import ap.terfor.equations.EquationConj
import ap.terfor.arithconj.{ModelElement, EqModelElement}
import ap.terfor.linearcombination.LinearCombination
import ap.proof.ModelSearchProver
import ap.proof.theoryPlugins.PluginSequence
import ap.proof.certificates.Certificate
import ap.util.Seqs

import lazabs.prover.Tree

import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet,
                                 HashMap => MHashMap}

object TreeInterpolator {

  type TreeInterpolatorFun =
    (Tree[Conjunction], TermOrder, Boolean, Seq[Theory]) =>
      Either[Tree[Conjunction],Conjunction]

  val interpolator = LinTreeInterpolator
//  val interpolator = BSTreeInterpolator

  def size(t : Tree[Conjunction]) =
    (for (c <- t.iterator) yield nodeCount(c)).sum

  def nodeCount(c : Conjunction) : Int =
    ((c.arithConj.size + c.predConj.size) /: c.negatedConjs) {
      case (n,d) => n + nodeCount(d)
    }

  def treeInterpolate(oriProblem : Tree[Conjunction],
                      order : TermOrder,
                      fullCEX : Boolean,
                      theories : Seq[Theory])
                     : Either[Tree[Conjunction],Conjunction] =
    interpolator.treeInterpolate(oriProblem, order, fullCEX, theories)
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Generic implementation of tree interpolation.
 */
abstract class TreeInterpolator {

  import TreeInterpolator.size

    def treeInterpolate(oriProblem : Tree[Conjunction],
                        order : TermOrder,
                        fullCEX : Boolean,
                        theories : Seq[Theory])
                       : Either[Tree[Conjunction],Conjunction] = {
//    println("and-tree interpolation:")
//    oriProblem.prettyPrint

    val (problem2, symbolTranslation, preWitnesses) =
      preSimplify(oriProblem, order)
    val problem =
      for (c <- problem2) yield factorCommonParts(c, order)

    var partNum = 0
    val partNames = for (f <- problem) yield {
      partNum = partNum + 1
      new PartName("part" + (partNum-1))
    }

    // theory axioms
    val axioms =
      Conjunction.conj(for (t <- theories.iterator) yield t.axioms,
                       order).negate
    val theoryPlugin =
      PluginSequence(for (t <- theories; p <- t.plugin.toSeq) yield p)

    // convert to internal representation, pre-simplify
    val formulas = problem.toSeq

    val namedParts =
      (for ((f, n) <- (problem zip partNames).iterator)
       yield (n -> f.negate)).toMap +
      (PartName.NO_NAME -> axioms)

    val interpolationSettings =
      Param.THEORY_PLUGIN.set(
      Param.PROOF_CONSTRUCTION.set(GoalSettings.DEFAULT, true),
                              theoryPlugin)
    val prover = {
      val prover = ModelSearchProver emptyIncProver interpolationSettings
      prover.conclude(axioms, order)
    }

    prover.assert(formulas, order).checkValidity(fullCEX) match {
      case Left(m) if (fullCEX) => {
        // formula is sat

        assert(false) // not supported right now
        null

/*
 
      import TerForConvenience._
      implicit val o = order

      val smallModel =
        (for (lc <- m.arithConj.positiveEqs.iterator)
         yield (lc.leadingTerm.asInstanceOf[ConstantTerm] -> -lc.constant)).toMap

      val arithModel =
        ModelElement.constructModel(preWitnesses, order, smallModel)

      Right(m & arithModel)
*/
      }

      case Left(m) =>
        // formula is sat
        Right(m)
      
      case Right(cert) =>
        // found a proof of unsatisfiability, extract tree interpolants
        Left(computeInts(cert, partNames, namedParts, problem,
                         symbolTranslation, order))
    }
  }

  def computeInts(cert : Certificate,
                  names : Tree[PartName],
                  namedParts : Map[PartName, Conjunction],
                  fors  : Tree[Conjunction],
                  symbolTranslation : Tree[Map[ConstantTerm, ConstantTerm]],
                  order : TermOrder) : Tree[Conjunction]

  //////////////////////////////////////////////////////////////////////////////

  def preSimplify(problem : Tree[Conjunction],
                  order : TermOrder)
               : (Tree[Conjunction],
                  Tree[Map[ConstantTerm, ConstantTerm]],
                  Seq[ModelElement]) = {
    if (lazabs.GlobalParameters.get.log)
      print(" " + size(problem) + " -> ")

    val (newProblem, symbolTranslation) = propagateSymbols(problem, order)

    val witnesses = new ArrayBuffer[ModelElement]

//    val newProblem = elimSimpleEqs(problem, order, witnesses)
    val newProblem2 = elimLocalSyms(newProblem, order, witnesses)

    if (lazabs.GlobalParameters.get.log)
      print(size(newProblem2))

    (newProblem2, symbolTranslation, witnesses)
  }

  def propagateSymbols(problem : Tree[Conjunction], order : TermOrder)
                      : (Tree[Conjunction],
                         Tree[Map[ConstantTerm, ConstantTerm]]) =
    (problem, for (f <- problem) yield Map())

  //////////////////////////////////////////////////////////////////////////////

  def elimLocalSyms(oriProblem : Tree[Conjunction],
                    order : TermOrder,
                    witnesses : ArrayBuffer[ModelElement])
                   : Tree[Conjunction] = {
    implicit val o = order
    val reducer = ReduceWithConjunction(Conjunction.TRUE, order)

    var problem = for (c <- oriProblem) yield reducer(c)

    val symOccurrenceNum = new MHashMap[Term, Int]
    for (c <- problem) {
      for (s <- c.constants)
        symOccurrenceNum.put(s, symOccurrenceNum.getOrElse(s, 0) + 1)
    }

    var cont = true
    while (cont) {
      cont = false
      
      def elimLocalVars(c : Conjunction) : Conjunction =
        if (c.quans.isEmpty && c.variables.isEmpty) {
          val negConjs = c.negatedConjs
          val literals = Conjunction(List(), c.arithConj, c.predConj,
                                     NegatedConjunctions.TRUE, order)

          if (literals.variables.isEmpty) {
            val negConjsConsts = negConjs.constants
            val localVars =
              (for (s <- literals.constants.iterator;
                    if (symOccurrenceNum(s) == 1 && !(negConjsConsts contains s)))
               yield s.asInstanceOf[Term]).toSet
            
            if (!localVars.isEmpty) {
              val localWitnesses = new ArrayBuffer[ModelElement]
              val eliminator = new LiteralEliminator(literals, localVars, order, localWitnesses)
              val essentialLits = eliminator eliminate ComputationLogger.NonLogger
        
              if (!localWitnesses.isEmpty) {
                val newNegConjs =
                  if (eliminator.divJudgements.isEmpty)
                    negConjs
                  else
                    NegatedConjunctions(negConjs ++ eliminator.divJudgements, order)

                Conjunction(List(), essentialLits.arithConj, essentialLits.predConj,
                            newNegConjs, order)
              } else {
                c
              }
            } else {
              c
            }
          } else {
            c
          }
        } else {
          c
        }

      problem = for (c <- problem) yield {
        val newC =
          if (c.isTrue || c.isFalse) {
            c
          } else if (c.arithConj.isTrue && c.predConj.isTrue && c.negatedConjs.size == 1) {
            // c represents a disjunction, and we can consider each disjunct separately
            val negConj = c.negatedConjs.head
            val subNegConjs = negConj.negatedConjs
            val newSubNegConjs =
              subNegConjs.update(for (c <- subNegConjs) yield elimLocalVars(c), order)
            if (newSubNegConjs eq subNegConjs)
              c
            else
              c.updateNegatedConjs(
                NegatedConjunctions(List(negConj.updateNegatedConjs(newSubNegConjs)), order))
          } else {
            elimLocalVars(c)
          }

        if (!(newC eq c)) {
          val newCConsts = newC.constants
          for (s <- c.constants)
            if (!(newCConsts contains s)) {
              val newNum = symOccurrenceNum(s) - 1
              if (newNum == 1)
                cont = true
              symOccurrenceNum.put(s, newNum)
            }
        }

        newC
      }
    }

    problem
  }

  //////////////////////////////////////////////////////////////////////////////

  def elimSimpleEqs(problem : Tree[Conjunction],
                    order : TermOrder,
                    witnesses : ArrayBuffer[ModelElement])
                   : Tree[Conjunction] = {
    val complicatedConsts = new MHashSet[ConstantTerm] ++ (
      for (c <- problem.iterator; s <- complicatedSyms(c)) yield s)

    // fixed-point iteration, to find other affected symbols
    var oldSize = 0
    while (oldSize != complicatedConsts.size) {
      oldSize = complicatedConsts.size

      for (c <- problem.iterator;
           lc <- c.arithConj.positiveEqs.iterator)
        if (!Seqs.disjoint(lc.constants, complicatedConsts))
          complicatedConsts ++= lc.constants
    }

    val constMap = (for (c <- order.orderedConstants.iterator;
                         if (!(complicatedConsts contains c)))
                    yield (c -> LinearCombination(0))).toMap
    val subst = ConstantSubst(constMap, order)

    val defEqs = EquationConj(for (c <- order.orderedConstants.iterator;
                                   if (!(complicatedConsts contains c)))
                              yield LinearCombination(c, order),
                              order)

    witnesses += EqModelElement(defEqs, defEqs.constants)

    for (c <- problem) yield subst(c)
  }

  def complicatedSyms(c : Conjunction) : Iterator[ConstantTerm] =
    c.predConj.constants.iterator ++
    c.negatedConjs.constants.iterator ++
    c.arithConj.negativeEqs.constants.iterator ++
    c.arithConj.inEqs.constants.iterator ++
    (for (lc <- c.arithConj.positiveEqs.iterator;
          if (!isSimpleEq(lc));
          c <- lc.constants.iterator) yield c)
  
  def isSimpleEq(lc : LinearCombination) = lc match {
    case Seq((IdealInt.ONE, c : ConstantTerm),
             (IdealInt.MINUS_ONE, d : ConstantTerm)) => c != d
    case Seq((IdealInt.MINUS_ONE, c : ConstantTerm),
             (IdealInt.ONE, d : ConstantTerm)) => c != d
    case _ : LinearCombination => false
  }

  //////////////////////////////////////////////////////////////////////////////

  def factorCommonParts(c : Conjunction,
                        order : TermOrder) : Conjunction =
    ReduceWithConjunction(Conjunction.TRUE, order)(
      factorCommonPartsHelp(c, order))

  private def factorCommonPartsHelp(c : Conjunction,
                                    order : TermOrder) : Conjunction = {
    val newNegConjs =
      c.negatedConjs.update(for (d <- c.negatedConjs)
                              yield factorCommonParts(d, order),
                            order)

    if (newNegConjs.size > 1) {
      val commonFors =
        (for (d <- newNegConjs.iterator) yield {
           if (d.quans.isEmpty) d.iterator.toSet else Set(d)
        }) reduceLeft (_ & _)

      if (commonFors.isEmpty) {
        c.updateNegatedConjs(newNegConjs)(order)
      } else {
        val f =
          Conjunction.conj(commonFors +
                             Conjunction.negate(newNegConjs, order),
                           order)
        val res =
          c.updateNegatedConjs(NegatedConjunctions(List(f), order))(order)

//      println("before: " + c)
//      println("after: " + res)

        res
      }
    } else {
      c.updateNegatedConjs(newNegConjs)(order)
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

private class LiteralEliminator(literals : Conjunction,
                                localVariables : Set[Term],
                                order : TermOrder,
                                witnesses : ArrayBuffer[ModelElement])
              extends ConjunctEliminator(literals, localVariables, Set(), order) {
  
  protected def nonUniversalElimination(f : Conjunction) =
    throw new UnsupportedOperationException
  
  protected def universalElimination(m : ModelElement) : Unit = {
    witnesses += m
  }

  protected def addDivisibility(f : Conjunction) =
    divJudgements = f :: divJudgements

  var divJudgements : List[Conjunction] = List()

  protected def isEliminationCandidate(t : Term) : Boolean =
    localVariables contains t

  protected def eliminationCandidates(literals : Conjunction) : Iterator[Term] =
    localVariables.iterator
  
}
