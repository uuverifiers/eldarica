/**
 * Copyright (c) 2023 Philipp Ruemmer. All rights reserved.
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
import HornClauses._
import lazabs.horn.Util.{Dag, DagNode, DagEmpty}

import ap.parser._
import IExpression._
import ap.basetypes.UnionFind
import ap.theories.{ExtArray, TheoryRegistry}
import ap.types.MonoSortedPredicate
import Sort.:::

import scala.collection.mutable.{HashMap => MHashMap}

object ArraySplitter {

  private abstract class UFNode {
    def sort : Sort
  }

  private case object UnknownArray
          extends UFNode {
    val sort = ExtArray(List(Sort.Integer), Sort.Integer).sort
  }

  private case class PredArgument(pred : Predicate, argNum : Int)
          extends UFNode {
    lazy val sort = predArgumentSorts(pred)(argNum)
  }

  private case class ClauseExpr(clauseNum : Int, term : ITerm)
          extends UFNode {
    lazy val sort : Sort = Sort sortOf term
  }

}

/**
 * Preprocessor that separates non-interacting array variables by
 * creating a separate array theory for each of them.
 */
class ArraySplitter extends HornPreprocessor {
  import HornPreprocessor._
  import ClauseInliner._
  import ArraySplitter._
  import ExtArray.ArraySort

  val name : String = "cloning arrays"

  private val symClasses       = new UnionFind[UFNode]
  private val newArrayTheories = new MHashMap[UFNode, ExtArray]

  symClasses makeSet UnknownArray

  override def isApplicable(clauses : Clauses,
                            frozenPredicates : Set[Predicate]) : Boolean =
    (HornClauses allPredicates clauses) exists {
      p =>
        !(frozenPredicates contains p) &&
        (predArgumentSorts(p) exists (_.isInstanceOf[ArraySort]))
    }

  def process(clauses : Clauses, hints : VerificationHints,
              frozenPredicates : Set[Predicate])
             : (Clauses, VerificationHints, BackTranslator) = {

    createArrayTheories(clauses, frozenPredicates)

    if (newArrayTheories.isEmpty)
      return (clauses, hints, IDENTITY_TRANSLATOR)

    val (predMapping, changedClauses) = translateClauses(clauses)

    val newClauses = changedClauses.unzip._1
    val newHints   = hints.renamePredicates(predMapping)

    val clauseBackMapping =
      changedClauses.toMap
    val predBackMapping =
      (for ((a, b) <- predMapping.iterator) yield (b, a)).toMap

    (newClauses, newHints,
     new BTranslator(clauseBackMapping, predBackMapping))

  }

  //////////////////////////////////////////////////////////////////////////////

  private class BTranslator(clauseBackMapping : Map[Clause, Clause],
                            predBackMapping   : Map[Predicate, Predicate])
          extends BackTranslator {

    val theoryBackMapping =
      (for ((n, theory) <- newArrayTheories.iterator) yield {
         val ArraySort(oldTheory) = n.sort
         theory -> oldTheory
       }).toMap

    val translateExpr = new ExprBackTranslator(theoryBackMapping)

    def translate(solution : Solution) = {
      (for ((pred, f) <- solution.iterator) yield {
         val oldPred = predBackMapping.getOrElse(pred, pred)
         (oldPred -> translateExpr(f))
       }).toMap
    }

    def translate(cex : CounterExample) =
      for (p <- cex) yield {
        val (atom, clause) = p

        val oldPred   = predBackMapping.getOrElse(atom.pred, atom.pred)
        val oldClause = clauseBackMapping.getOrElse(clause, clause)

        (IAtom(oldPred, for (t <- atom.args) yield translateExpr(t)), oldClause)
      }

  }

  private class ExprBackTranslator(theoryBackMapping : Map[ExtArray, ExtArray])
          extends CollectingVisitor[Unit, IExpression] {

    def apply(t : ITerm) : ITerm       = visit(t, ()).asInstanceOf[ITerm]
    def apply(t : IFormula) : IFormula = visit(t, ()).asInstanceOf[IFormula]

    object ClonedArraySort {
      def unapply(sort : Sort) : Option[Sort] = sort match {
        case ArraySort(theory) =>
          for (oldTheory <- theoryBackMapping get theory) yield oldTheory.sort
        case _ =>
          None
      }
    }

    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult = {
      KeepArg
    }

    def postVisit(t : IExpression,
                  arg : Unit, subres : Seq[IExpression]) : IExpression =
      t match {

        case ISortedVariable(ind, ClonedArraySort(sort)) =>
          ISortedVariable(ind, sort)

        case ISortedQuantified(q, ClonedArraySort(sort), _) =>
          ISortedQuantified(q, sort, subres(0).asInstanceOf[IFormula])

        case ISortedEpsilon(ClonedArraySort(sort), _) =>
          ISortedEpsilon(sort, subres(0).asInstanceOf[IFormula])

        case IFunApp(f, _) =>
          TheoryRegistry.lookupSymbol(f) match {
            case Some(theory : ExtArray) =>
              (theoryBackMapping get theory) match {
                case Some(oldTheory) => {
                  val args = subres map (_.asInstanceOf[ITerm])
                  f match {
                    case theory.const  => IFunApp(oldTheory.const,  args)
                    case theory.select => IFunApp(oldTheory.select, args)
                    case theory.store  => IFunApp(oldTheory.store,  args)
                  }
                }
                case None =>
                  t update subres
              }
            case _ =>
              t update subres
          }

        case _ => t update subres
      }

  }

  //////////////////////////////////////////////////////////////////////////////

  private def translateClauses(clauses : Clauses)
                       : (Map[Predicate, Predicate], Seq[(Clause, Clause)]) = {
    val predsToUpdate =
      (for (key@PredArgument(pred, n) <- symClasses.elements;
            if newArrayTheories contains symClasses(key))
       yield pred).toSet

    val predMapping =
      (for (pred <- predsToUpdate.iterator) yield {
         val oldArgSorts =
           predArgumentSorts(pred)
         val newArgSorts =
           for ((oldSort, n) <- oldArgSorts.zipWithIndex) yield {
             val key = PredArgument(pred, n)
             if (symClasses contains key) {
               (newArrayTheories get symClasses(key)) match {
                 case Some(newTheory) => newTheory.sort
                 case _ => oldSort
               }
             } else {
               oldSort
             }
           }
         pred -> MonoSortedPredicate(pred.name, newArgSorts)
       }).toMap

    val changedClauses =
      for ((clause, clauseNum) <- clauses.zipWithIndex)
      yield (translateClause(clause, clauseNum, predMapping), clause)

    (predMapping, changedClauses)
  }

  private def translateClause(clause           : Clause,
                              clauseNum        : Int,
                              predMapping      : Map[Predicate, Predicate])
                                               : Clause = {
    val translateExpr = new ExprTranslator(clauseNum)

    def translateAtom(a : IAtom) : IAtom = {
      val oldPred = a.pred
      val newPred = predMapping.getOrElse(oldPred, oldPred)
      val newArgs = for (t <- a.args) yield translateExpr(t)
      IAtom(newPred, newArgs)
    }

    val newClause = Clause(translateAtom(clause.head),
                           clause.body map translateAtom,
                           translateExpr(clause.constraint))

    if (newClause == clause) {
      clause
    } else {
//      println("Updated: " + newClause)
      newClause
    }
  }

  private def getNewArrayTheory(n : UFNode) : Option[ExtArray] =
    if (symClasses contains n) {
      newArrayTheories get symClasses(n)
    } else {
      None
    }

  private class ExprTranslator(clauseNum : Int)
          extends CollectingVisitor[Unit, IExpression] {

    val constMapping = new MHashMap[ConstantTerm, ConstantTerm]

    def apply(t : ITerm) : ITerm       = visit(t, ()).asInstanceOf[ITerm]
    def apply(t : IFormula) : IFormula = visit(t, ()).asInstanceOf[IFormula]

    // TODO: variable binders
    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult = {
      KeepArg
    }

    def postVisit(t : IExpression,
                  arg : Unit, subres : Seq[IExpression]) : IExpression =
      t match {

        case t@IConstant(c) =>
          (constMapping get c) match {
            case Some(d) =>
              IConstant(d)
            case None => {
              getNewArrayTheory(ClauseExpr(clauseNum, t)) match {
                case Some(theory) => {
                  val d = theory.sort newConstant (c.name + "_new-" + theory.hashCode)
                  constMapping.put(c, d)
                  IConstant(d)
                }
                case None =>
                  t
              }
            }
          }

        case IFunApp(f@(ExtArray.Select(_) | ExtArray.Store(_)),
                     Seq(arTerm, _*)) =>
          getNewArrayTheory(ClauseExpr(clauseNum, arTerm)) match {
            case Some(theory) => {
              assert((Sort sortOf subres(0).asInstanceOf[ITerm]) == theory.sort)
              val newFun = f match {
                case ExtArray.Select(_) => theory.select
                case ExtArray.Store(_)  => theory.store
              }
              IFunApp(newFun, subres map (_.asInstanceOf[ITerm]))
            }
            case None =>
              t update subres
          }

        case _ =>
          // make sure that constant arrays belong to the right theory
          (t update subres) match {
            case Eq(s ::: ArraySort(theory1),
                    IFunApp(ExtArray.Const(theory2), c))
                if theory1 != theory2 =>
              Eq(s, IFunApp(theory1.const, c))
            case Eq(IFunApp(ExtArray.Const(theory2), c),
                    s ::: ArraySort(theory1))
                if theory1 != theory2 =>
              Eq(IFunApp(theory1.const, c), s)
            case t => t
          }
      }

  }

  //////////////////////////////////////////////////////////////////////////////

  private def createArrayTheories(clauses : Clauses,
                                  frozenPredicates : Set[Predicate]) : Unit = {
    for ((clause, clauseNum) <- clauses.iterator.zipWithIndex) {
      for (a <- List(clause.head) ++ clause.body) {
        val pred = a.pred
        val argSorts = predArgumentSorts(pred)

        for (((t : ITerm, ArraySort(_)), n)
               <- (a.iterator zip argSorts.iterator).zipWithIndex) {
          addTerms(t, clauseNum)
          union(PredArgument(pred, n), ClauseExpr(clauseNum, t))
          if (frozenPredicates contains pred)
            union(PredArgument(pred, n), UnknownArray)
        }

        addTerms(clause.constraint, clauseNum)
      }
    }

    val unknownClass =
      symClasses(UnknownArray)
    val renameableClasses =
      (for (c <- symClasses.representatives;
            if symClasses(c) != unknownClass)
       yield c).toVector
    val classesPerSort =
      renameableClasses.groupBy(_.sort)

    for ((ArraySort(theory), reprs) <- classesPerSort.iterator;
         if reprs.size > 1;
         repr <- reprs.iterator)
      newArrayTheories.put(repr,
                           new ExtArray(theory.indexSorts, theory.objSort))
  }

  private def union(n1 : UFNode, n2 : UFNode) : Unit = (n1, n2) match {
    case (ClauseExpr(_, IFunApp(ExtArray.Const(_), _)), _) |
         (_, ClauseExpr(_, IFunApp(ExtArray.Const(_), _))) =>
      // we ignore constant arrays, which can be cast to any theory
    case _ => {
      symClasses makeSetIfNew n1
      symClasses makeSetIfNew n2
      symClasses.union(n1, n2)
    }
  }

  private def addTerms(t : IExpression, clauseNum : Int) : Unit =
    TermClassAdder.visitWithoutResult(t, clauseNum)

  private object TermClassAdder extends CollectingVisitor[Int, Unit] {

    override def preVisit(t : IExpression,
                          clauseNum : Int) : PreVisitResult = t match {

      // TODO: handling of constant arrays could be more precise; see
      // splitting4.smt2

      case t : IVariableBinder => {
        addUnknownTerms(SymbolCollector.constantsSorted(t), clauseNum)
        ShortCutResult(())
      }

      case IFunApp(ExtArray.Select(_), Seq(arTerm, otherTerms @ _*)) => {
        addUnknownTerms(otherTerms, clauseNum)
        KeepArg
      }

      case t@IFunApp(ExtArray.Store(_),
                     Seq(arTerm : ITerm, otherTerms @ _*)) => {
        union(ClauseExpr(clauseNum, t), ClauseExpr(clauseNum, arTerm))
        addUnknownTerms(otherTerms, clauseNum)
        KeepArg
      }

      case Eq(s ::: ArraySort(_), t ::: ArraySort(_)) => {
        union(ClauseExpr(clauseNum, s), ClauseExpr(clauseNum, t))
        KeepArg
      }

      case t => {
        for (s <- t.subExpressions)
          if (s.isInstanceOf[ITerm])
            addUnknownTerm(s.asInstanceOf[ITerm], clauseNum)
        KeepArg
      }
    }

    private def addUnknownTerm(t : ITerm, clauseNum : Int) : Unit =
      (Sort sortOf t) match {
        case ArraySort(_) =>
          union(UnknownArray, ClauseExpr(clauseNum, t))
        case _ =>
          // nothing
      }

    private def addUnknownTerms(ts : Seq[ITerm], clauseNum : Int) : Unit =
      for (t <- ts)
        addUnknownTerm(t, clauseNum)

    def postVisit(t : IExpression,
                  clauseNum : Int, subres : Seq[Unit]) : Unit = ()
  }

}
