/**
 * Copyright (c) 2016-2019 Philipp Ruemmer. All rights reserved.
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

import lazabs.GlobalParameters
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.parser.HornReader

import ap.{SimpleAPI, PresburgerTools}
import SimpleAPI.ProverStatus
import ap.basetypes.{IdealInt, Leaf, Tree}
import ap.parser._
import IExpression._
import ap.util.{Seqs, Timeout}
import ap.types.MonoSortedPredicate

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

/**
 * Elimination of remaining Boolean structure in clauses.
 */
class BooleanClauseSplitter extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "Boolean clause splitting"

  private var symbolCounter = 0
  private val tempPredicates = new MHashSet[Predicate]
  private val clauseBackMapping = new MHashMap[Clause, (Clause, Tree[Int])]

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {

    val newClauses = SimpleAPI.withProver { p =>
      for (clause <- clauses;
           newClause <- cleverSplit(clause)(p)) yield {
        newClause
      }
    }

    val translator =
      ClauseShortener.BTranslator.withIndexes(tempPredicates.toSet,
                                              clauseBackMapping.toMap)

    tempPredicates.clear
    clauseBackMapping.clear

    (newClauses, hints, translator)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Split disjunctions in a clause body by introducing additional predicates,
   * to avoid combinatorial explosion. The method returns the new clauses,
   * as well as the number of temporary predicates that were needed.
   */
  private def splitWithIntPred(clause : Clause,
                               initialClause : Clause,
                               indexTree : Option[Tree[Int]])
                              (implicit p : SimpleAPI)
                            : (Seq[Clause], Int) = {
    val Clause(headAtom, body, constraint) = clause
    val negConstraint = Transform2NNF(~constraint)

      val conjuncts =
        LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)
      val (atomicConjs, compoundConjs) = conjuncts partition {
        case LeafFormula(_) => true
        case _              => false
      }

      if (compoundConjs.size > 8) {
        // introduce a new predicate to split the clause into multiple
        // clauses, and this way avoid combinatorial explosion

        // partition the conjuncts
        val leftConsts = new MHashSet[ConstantTerm]
        for (b <- body)
          leftConsts ++= (SymbolCollector constants b)

        val selectedConjs, remainingConjs = new ArrayBuffer[IFormula]
        remainingConjs ++= conjuncts

        var selCompound = 0
        while (selCompound < compoundConjs.size / 2) {
          val sel = remainingConjs minBy { c => {
            val consts = SymbolCollector constants c
            consts.size - (leftConsts & consts).size
          }}

          selectedConjs += sel
          remainingConjs -= sel

          leftConsts ++= SymbolCollector constants sel

          sel match {
            case LeafFormula(_) => // nothing
            case _ => selCompound = selCompound + 1
          }
        }

        val constraint1 = and(selectedConjs)
        val constraint2 = and(remainingConjs)

        val interfaceConstants =
          (SymbolCollector constantsSorted (constraint2 & headAtom)) filter leftConsts

        val intPred =
          MonoSortedPredicate("intPred" + symbolCounter,
                              interfaceConstants map (Sort sortOf _))
        symbolCounter = symbolCounter + 1
        tempPredicates += intPred

        val intLit = IAtom(intPred, interfaceConstants)

        val (newClauses1, preds1) = 
          splitWithIntPred(Clause(intLit, body, constraint1),
                           initialClause, None)
        val (newClauses2, preds2) = 
          splitWithIntPred(Clause(headAtom, List(intLit), constraint2),
                           initialClause,
                           for (it <- indexTree)
                           yield ((0 until (preds1 + 1)) :\ it) {
                                    (n:Int, t:Tree[Int]) => Tree(-1, List(t))
                                  })

        (newClauses1 ++ newClauses2, preds1 + preds2 + 1)

      } else {
        Timeout.withChecker(GlobalParameters.get.timeoutChecker) {
          val newClauses = fullDNF(clause, false)
          for (it <- indexTree) {
            for (newClause <- newClauses)
              clauseBackMapping.put(newClause, (initialClause, it))
          }
          (newClauses, 0)
        }
      }
  }

  private def fullDNF(clause : Clause, addBackMapping : Boolean = true)
                     (implicit p : SimpleAPI) : Seq[Clause] = {
    val Clause(headAtom, body, constraint) = clause

        // transform the clause constraint to DNF, and create a separate
        // clause for each disjunct

    val newClauses =
        if (ContainsSymbol isPresburger constraint) p.scope {
          import p._
          addConstantsRaw(SymbolCollector constantsSorted constraint)
          val disjuncts =
              PresburgerTools.nonDNFEnumDisjuncts(
                asConjunction(constraint))
          (for (d <- disjuncts; if !d.isFalse) yield
           Clause(headAtom, body, asIFormula(d))).toIndexedSeq
        } else {
          // TODO: this might not be effective at all
          for (conjunct <- HornReader.cnf_if_needed(
                             Transform2NNF(~constraint))) yield {
            Clause(headAtom, body, ~conjunct)
          }
        }

    if (addBackMapping) {
      val indexTree =
        Tree(-1, (for (n <- 0 until body.size) yield Leaf(n)).toList)
      for (newClause <- newClauses)
        clauseBackMapping.put(newClause, (clause, indexTree))
    }

    newClauses
  }

  private val SPLITTING_TO = 3000
  private val GLOBAL_SPLITTING_TO = 30000

  private val globalStartTime = System.currentTimeMillis

  private def cleverSplit(clause : Clause)
                         (implicit p : SimpleAPI) : Seq[Clause] =
    if (needsSplittingPos(clause.constraint)) {
      // first try the full splitting, but this might sometimes explode
      val startTime = System.currentTimeMillis
      def checker() : Unit = {
        GlobalParameters.get.timeoutChecker
        val currentTime = System.currentTimeMillis
        if (currentTime - startTime > SPLITTING_TO ||
            currentTime - globalStartTime > GLOBAL_SPLITTING_TO)
          Timeout.raise
      }

      Timeout.catchTimeout {
        Timeout.withChecker(checker _) { fullDNF(clause) }
      } {
        case _ => {
          val indexTree =
            Tree(-1, (for (n <- 0 until clause.body.size) yield Leaf(n)).toList)
          splitWithIntPred(clause, clause, Some(indexTree))._1
        }
      }
    } else {
      List(clause)
    }

  //////////////////////////////////////////////////////////////////////////////

  private def needsSplittingPos(f : IFormula) : Boolean = f match {
    case IBinFormula(IBinJunctor.Or, _, _) =>
      true
    case IBinFormula(IBinJunctor.And, f1, f2) =>
      needsSplittingPos(f1) || needsSplittingPos(f2)
    case INot(f1) =>
      needsSplittingNeg(f1)
    case _ =>
      false
  }

  private def needsSplittingNeg(f : IFormula) : Boolean = f match {
    case IBinFormula(IBinJunctor.And, _, _) =>
      true
    case IBinFormula(IBinJunctor.Or, f1, f2) =>
      needsSplittingNeg(f1) || needsSplittingNeg(f2)
    case INot(f1) =>
      needsSplittingPos(f1)
    case _ =>
      false
  }

  //////////////////////////////////////////////////////////////////////////////

  // Code for model-based transformation to DNF; not finished yet

  private def modelBased2DNF(f : IFormula) : Seq[IFormula] = {
    val consts = SymbolCollector constantsSorted f
    val res = new ArrayBuffer[IFormula]

    SimpleAPI.withProver { modelConstructor =>
    SimpleAPI.withProver { implicationChecker =>
      modelConstructor.addConstantsRaw(consts)
      implicationChecker.addConstantsRaw(consts)

      val flags = implicationChecker.createBooleanVariables(SizeVisitor(f))
      modelConstructor !! f
      implicationChecker ?? f

      while (modelConstructor.??? == ProverStatus.Sat) {
        GlobalParameters.get.timeoutChecker()

        val litCollector =
          new CriticalAtomsCollector(modelConstructor.partialModel)
        val criticalLits = litCollector.visit(f, ()) match {
          case Some((true, fors)) =>
            fors
          case _ =>
            throw new IllegalArgumentException("Could not dnf-transform " + f)
        }

        println(criticalLits)

        val neededCriticalLits = implicationChecker.scope {
          import implicationChecker._

          val neededFlags = flags take criticalLits.size
          for ((flag, lit) <- neededFlags zip criticalLits)
            !! (flag ==> lit)

          val flagValue = Array.fill(neededFlags.size)(true)

          for (n <- 0 until neededFlags.size) {
            scope {
              flagValue(n) = false
              for (j <- n until neededFlags.size)
                !! (neededFlags(j) <===> flagValue(j))
              ??? match {
                case ProverStatus.Valid =>
                  // nothing
                case _ =>
                  flagValue(n) = true
              }
            }

            !! (neededFlags(n) <===> flagValue(n))
          }

          and(for ((lit, true) <- criticalLits.iterator zip flagValue.iterator)
              yield lit)
        }

        println(neededCriticalLits)
println

        res += neededCriticalLits
println(res.size)
        modelConstructor !! ~neededCriticalLits
      }
    }}
//throw new Exception
    List()
  }

  //////////////////////////////////////////////////////////////////////////////

  private class CriticalAtomsCollector(model : SimpleAPI.PartialModel)
          extends CollectingVisitor[Unit, Option[(Boolean, Seq[IFormula])]] {

    override def preVisit(t : IExpression,
                          arg : Unit) : PreVisitResult = t match {
      case IBoolLit(value) =>
        ShortCutResult(Some((value, List())))
      case LeafFormula(f) => (model eval f) match {
        case Some(true) =>
          ShortCutResult(Some((true, List(f))))
        case Some(false) =>
          ShortCutResult(Some((false, List(~f))))
        case None =>
          ShortCutResult(None)
      }
      case _ =>
        KeepArg
    }

    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[Option[(Boolean, Seq[IFormula])]])
                : Option[(Boolean, Seq[IFormula])] = t match {
      case Disj(f1, f2) => subres match {
        case Seq(r1@Some((true, fors1)), r2@Some((true, fors2))) =>
          if (fors2.size < fors1.size) r2 else r1
        case Seq(r@Some((true, fors)), _) =>
          r
        case Seq(_, r@Some((true, fors))) =>
          r
        case Seq(Some((false, fors1)), Some((false, fors2))) =>
          Some((false, fors1 ++ fors2))
        case _ =>
          None
      }
      case Conj(f1, f2) => subres match {
        case Seq(r1@Some((false, fors1)), r2@Some((false, fors2))) =>
          if (fors2.size < fors1.size) r2 else r1
        case Seq(r@Some((false, fors)), _) =>
          r
        case Seq(_, r@Some((false, fors))) =>
          r
        case Seq(Some((true, fors1)), Some((true, fors2))) =>
          Some((true, fors1 ++ fors2))
        case _ =>
          None
      }
      case IBinFormula(IBinJunctor.Eqv, f1, f2) => subres match {
        case Seq(Some((v1, fors1)), Some((v2, fors2))) =>
          Some((v1 == v2, fors1 ++ fors2))
        case _ =>
          None
      }
      case INot(f) =>
        for ((value, fors) <- subres.head) yield (!value, fors)
      case t =>
        throw new IllegalArgumentException("Cannot handle " + t)
    }
  }

}
