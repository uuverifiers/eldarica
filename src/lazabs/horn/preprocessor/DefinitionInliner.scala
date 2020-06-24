/**
 * Copyright (c) 2011-2020 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.HornClauses
import HornClauses._

import ap.theories.{ModuloArithmetic, ADT}
import ap.basetypes.IdealInt
import ap.parser._
import IExpression._
import ap.util.Seqs

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, LinkedHashMap, ArrayBuffer}

object ConstraintSimplifier {

  def rewriteConstraint(constraint : IFormula,
                        replacements : GMap[ITerm, ITerm]) =
    (new ConstraintRewriter(replacements)).visit(constraint, ())
                                          .asInstanceOf[IFormula]

  class ConstraintRewriter(replacements : GMap[ITerm, ITerm])
        extends CollectingVisitor[Unit, IExpression] {
    def postVisit(t : IExpression,
                  arg : Unit,
                  subres : Seq[IExpression]) : IExpression =
      (t update subres) match {
        case updatedT : ITerm =>
          (replacements get updatedT) match {
            case Some(c) => c
            case None    => updatedT
          }
        case updatedT =>
          updatedT
      }
  }

  /**
   * Extractor to identify equations or inequalities involving two
   * symbols with unit coefficients. The class should be used in
   * conjunction with the <code>*Tuple</code> classes below.
   */
  class BinaryIntFormula(opPred : IIntRelation.Value => Boolean) {
    def unapply(f : IFormula)
              : Option[(IIntRelation.Value, ITerm, ITerm, IdealInt)] = f match {
      case IIntFormula(op, t) if opPred(op) =>
        extractSyms(t) match {
          case null =>
            None
          case (a, b, offset) =>
            Some((op, a, b, offset))
        }
      case _ =>
        None
    }
  }

  object EqBinaryIntFormula extends BinaryIntFormula(_ == IIntRelation.EqZero)

  /**
   * Identify literals equivalent to <code>a == lit</code>.
   */
  object EqLitTuple {
    def unapply(t : (IIntRelation.Value, ITerm, ITerm, IdealInt))
              : Option[(ITerm, IdealInt)] =
      t match {
        case (_, null, null, _) =>
          None
        case (IIntRelation.EqZero, a, null, offset) =>
          Some((a, offset))
        case (IIntRelation.EqZero, null, b, offset) =>
          Some((b, -offset))
        case _ =>
          None
      }
  }

  /**
   * Identify literals equivalent to <code>a >= bound</code>.
   */
  object LowerBoundTuple {
    def unapply(t : (IIntRelation.Value, ITerm, ITerm, IdealInt))
              : Option[(ITerm, IdealInt)] =
      t match {
        case (_, null, _, _) =>
          None
        case (IIntRelation.GeqZero, a, null, offset) =>
          Some((a, offset))
        case _ =>
          None
      }
  }

  /**
   * Identify literals equivalent to <code>bound >= a</code>.
   */
  object UpperBoundTuple {
    def unapply(t : (IIntRelation.Value, ITerm, ITerm, IdealInt))
              : Option[(ITerm, IdealInt)] =
      t match {
        case (_, _, null, _) =>
          None
        case (IIntRelation.GeqZero, null, b, offset) =>
          Some((b, -offset))
        case _ =>
          None
      }
  }

  /**
   * Identify literals equivalent to <code>a == b + offset</code>.
   */
  object EqOffsetTuple {
    def unapply(t : (IIntRelation.Value, ITerm, ITerm, IdealInt))
              : Option[(ITerm, ITerm, IdealInt)] =
      t match {
        case (_, null, _, _) =>
          None
        case (_, _, null, _) =>
          None
        case (IIntRelation.EqZero, a, b, offset) =>
          Some((a, b, offset))
        case _ =>
          None
      }
  }

    private def extractSyms(t : ITerm) : (ITerm, ITerm, IdealInt) = t match {
      case IPlus(t1, t2) =>
        extractSyms(t1) match {
          case null =>
            null
          case res1 =>
            extractSyms(t2) match {
              case null =>
                null
              case res2 => (res1, res2) match {
                case ((a,    b,    offset1), (null, null, offset2)) =>
                  (a, b, offset1 + offset2)
                case ((a,    null, offset1), (null, b,    offset2)) =>
                  (a, b, offset1 + offset2)
                case ((null, b,    offset1), (a,    null, offset2)) =>
                  (a, b, offset1 + offset2)
                case ((null, null, offset1), (a,    b,    offset2)) =>
                  (a, b, offset1 + offset2)
                case _ =>
                  null
              }
            }
        }
      case ITimes(IdealInt.ZERO, s) =>
        (null, null, IdealInt.ZERO)
      case ITimes(IdealInt.ONE, s) =>
        extractSyms(s)
      case ITimes(IdealInt.MINUS_ONE, s) =>
        extractSyms(s) match {
          case null =>
            null
          case (a, b, offset) =>
            (b, a, -offset)
        }
      case IIntLit(offset) =>
        (null, null, -offset)
      case t =>
        (t, null, IdealInt.ZERO)
    }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Inline simple definitions found in the clause constraints
 */
class ConstraintSimplifier extends HornPreprocessor {
  import HornPreprocessor._
  import ConstraintSimplifier._

  val name : String = "constraint simplification"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val clauseMapping        = new MHashMap[Clause, Clause]
    val maybeEliminatedPreds = new MHashSet[Predicate]

    val newClauses =
      for (clause <- clauses;
           newClause =
             try {
               equationalRewriting(clause)
             } catch {
               case InconsistencyException => {
                 maybeEliminatedPreds ++= clause.predicates
                 null
               }
             };
           if newClause != null)
      yield {
        clauseMapping.put(newClause, clause)
        newClause
      }

    maybeEliminatedPreds -= HornClauses.FALSE

    val translator = new BackTranslator {
      def translate(solution : Solution) = {
        // if some predicates completely disappeared as the result of
        // eliminating clauses, those can be set to false
        solution ++ (for (p <- maybeEliminatedPreds.iterator;
                          if !(solution contains p))
                     yield (p -> i(false)))
      }
      def translate(cex : CounterExample) =
        for (p <- cex) yield (p._1, clauseMapping(p._2))
    }

    (newClauses, hints, translator)
  }

  private var symbolCounter = 0
  private def newConst(s : Sort) : IConstant = {
    val res = s newConstant ("app" + symbolCounter)
    symbolCounter = symbolCounter + 1
    IConstant(res)
  }

  private object InconsistencyException extends Exception

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Flatten nested function applications in the constraint by introducing
   * additional symbols.
   */
  private def flattenConstraint(constraint : IFormula) : Seq[IFormula] = {
    val flattener = new Flattener
    val conjuncts =
      LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)
    val newConjuncts =
      for (f <- conjuncts)
      yield flattener.visit(f, false).asInstanceOf[IFormula]
    newConjuncts ++
      (for ((s, t) <- flattener.extractedFuns.iterator) yield s === t)
  }

  private class Flattener extends CollectingVisitor[Boolean, IExpression] {
    val extractedFuns = new LinkedHashMap[IFunApp, IConstant]

    override def preVisit(t : IExpression,
                          extractFun : Boolean) : PreVisitResult = t match {
      case Eq(_ : IFunApp, SimpleTerm(_)) =>
        KeepArg
      case Conj(_, _) =>
        KeepArg
      case _ =>
        UniSubArgs(true)
    }

    def postVisit(t : IExpression, extractFun : Boolean,
                  subres : Seq[IExpression]) : IExpression =
      IExpression.updateAndSimplifyLazily(t, subres) match {
        case t : IFunApp if extractFun && ContainsSymbol.isClosed(t) =>
          extractedFuns.getOrElseUpdate(t, newConst(Sort sortOf t))
        case t =>
          t
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Detect linear equations that can be inlined, possibly eliminating
   * constant symbols.
   */
  private def inlineEquations(headSyms : scala.collection.Set[ConstantTerm],
                              body : List[IAtom],
                              conjuncts : Seq[IFormula],
                              persistentEqs : Seq[IFormula])
                            : Option[(List[IAtom],
                                      Seq[IFormula], Seq[IFormula])] = {
    val replacement      = new MHashMap[ConstantTerm, ITerm]
    val replacedConsts   = new MHashSet[ConstantTerm]
    val addPersistentEqs = new ArrayBuffer[IFormula]

    val remConjuncts = conjuncts filter {

      case eq@EqBinaryIntFormula(tuple) => tuple match {
        case EqLitTuple(IConstant(c), offset)
              if !(replacedConsts contains c)  => {
          replacement.put(c, offset)
          replacedConsts += c
          if (headSyms contains c)
            addPersistentEqs += eq
          false
        }

        case EqOffsetTuple(left@IConstant(c), right@IConstant(d), offset) =>
          if (c == d) {

            offset match {
              case IdealInt.ZERO =>
                // equation can be dropped
                false
              case _ =>
                // contradiction
                throw InconsistencyException
            }

          } else if (!(replacedConsts contains c) &&
                     !(replacedConsts contains d) &&
                     (Sort sortOf left) == (Sort sortOf right)) {

            if (!(headSyms contains c)) {
              replacement.put(c, right +++ offset)
            } else if (!(headSyms contains d)) {
              replacement.put(d, left --- offset)
            } else {
              addPersistentEqs += eq
              replacement.put(c, right +++ offset)
            }

            replacedConsts += c
            replacedConsts += d
            false

          } else {
            // keep this one
            true
          }

        case _ =>
          true
      }

      case _ =>
        true
    }

    if (remConjuncts.size == conjuncts.size && replacement.isEmpty)
      return None

    val newConjuncts =
      for (f <- remConjuncts;
           newF = SimplifyingConstantSubstVisitor(f, replacement);
           if !newF.isTrue)
      yield newF

    val newPersistentEqs =
      (for (f <- persistentEqs;
            newF = SimplifyingConstantSubstVisitor(f, replacement);
            if !newF.isTrue)
       yield newF) ++ addPersistentEqs

    if ((newPersistentEqs exists (_.isFalse)) ||
        (newConjuncts exists (_.isFalse)))
      throw InconsistencyException

    val newBody =
      for (a <- body)
      yield SimplifyingConstantSubstVisitor(a, replacement)
            .asInstanceOf[IAtom]

    Some((newBody, newConjuncts, newPersistentEqs))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Apply congruence closure to function applications.
   */
  private def congruenceClosure(conjuncts : Seq[IFormula])
                               : Option[Seq[IFormula]] = {
    val funApps        = new MHashMap[ITerm, ITerm]
    val newConjuncts   = new ArrayBuffer[IFormula]
    val otherConjuncts = new ArrayBuffer[IFormula]
    var changed        = false

    for (f <- conjuncts) f match {
      case Eq(fa : IFunApp, t : ITerm) =>
        (funApps get fa) match {
          case Some(s) => {
            changed = true
            newConjuncts += (s === t)
          }
          case None => {
            funApps.put(fa, t)
            newConjuncts += f
          }
        }
      case f =>
        otherConjuncts += f
    }

    for (f <- otherConjuncts) {
      val newF = rewriteConstraint(f, funApps)
      if (!(newF eq f)) {
        changed = true
        if (newF.isFalse)
          throw InconsistencyException
      }
      newConjuncts += newF
    }

    if (changed)
      Some(newConjuncts)
    else
      None
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Rewrite some cases of ADT expressions.
   */
  private def adtRewriting(conjuncts : Seq[IFormula])
                         : Option[Seq[IFormula]] = {
    val ctors =
      (for (Eq(IFunApp(ADT.Constructor(adt, num), args),
               c : IConstant) <- conjuncts)
       yield (c -> (adt, num, args))).toMap

    val simp = new ADTSimplifier(ctors)
    var changed = false

    val newConjuncts =
      for (f <- conjuncts) yield {
        val newF = simp.visit(f, ()).asInstanceOf[IFormula]
        if (!(newF eq f))
          changed = true
        newF
      }

    if (changed)
      Some(newConjuncts ++
            (for ((s, t) <- simp.sizeExpressions.iterator) yield s === t))
    else
      None
  }

  private class ADTSimplifier(ctors : GMap[IConstant, (ADT, Int, Seq[ITerm])])
          extends CollectingVisitor[Unit, IExpression] {
    val sizeExpressions = new LinkedHashMap[ITerm, ITerm]

    private def evalCtorTermSize(c : IConstant,
                                 adt : ADT, sortNum : Int,
                                 entry : Boolean) : ITerm =
      (ctors get c) match {
        case Some((`adt`, ctorNum, args))
             if adt.sortOfCtor(ctorNum) == sortNum => {
          val ctor =
            adt constructors ctorNum
          sum(for ((s : ADT.ADTProxySort, t) <-
                     ctor.argSorts.iterator zip args.iterator;
                   if s.adtTheory == adt)
              yield evalCtorTermSize(t.asInstanceOf[IConstant],
                                     adt, s.sortNum, false)) +++ 1
        }
        case _ =>
          if (entry) {
            null
          } else {
            val se = adt.termSize(sortNum)(c)
            sizeExpressions.getOrElseUpdate(se, newConst(Sort.Integer))
          }
      }

    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = (t, subres) match {

      case (IFunApp(ADT.Selector(adt, ctorNum, selNum), _),
            Seq(c : IConstant)) =>
        (ctors get c) match {
          case Some((`adt`, `ctorNum`, args)) =>
            args(selNum)
          case _ =>
            t update subres
        }

      case (IFunApp(ADT.TermSize(adt, sortNum), _),
            Seq(c : IConstant)) =>
        evalCtorTermSize(c, adt, sortNum, true) match {
          case null =>
            t update subres
          case s =>
            s
        }

      case _ =>
        t update subres
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Eliminate function applications that are no longer needed
   */
  private def gcFunctionApplications(
                       headSyms : scala.collection.Set[ConstantTerm],
                       body : List[IAtom],
                       conjuncts : Seq[IFormula])
                     : Option[Seq[IFormula]] = {
    val blockedConsts = new MHashSet[ConstantTerm]
    val defConsts     = new MHashSet[ConstantTerm]

    blockedConsts ++= headSyms
    for (a <- body)
      blockedConsts ++= SymbolCollector constants a

    for (f <- conjuncts) f match {
      case Eq(left : IFunApp, right@IConstant(c)) =>
        if ((Sort sortOf left) == (Sort sortOf right) && (defConsts add c))
          blockedConsts ++= SymbolCollector constants left
        else
          blockedConsts ++= SymbolCollector constants f
      case f =>
        blockedConsts ++= SymbolCollector constants f
    }

    val newConjuncts = conjuncts filter {
      case Eq(_ : IFunApp, IConstant(c)) =>
        blockedConsts contains c
      case _ =>
        true
    }

    if (newConjuncts.size < conjuncts.size)
      Some(newConjuncts)
    else
      None
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Simplify equations of the clause
   */
  private def equationalRewriting(clause : Clause) : Clause = {
    val Clause(head, oriBody, constraint) = clause

    // TODO: should we try to undo the flattening, as far as possible,
    // before translating clauses to internal form?

    val headSyms  = SymbolCollector constants head
    var body      = oriBody
    var conjuncts = flattenConstraint(constraint)

    if (conjuncts exists (_.isFalse))
      throw InconsistencyException
    val containsFunctions =
      !ContainsSymbol.isPresburger(constraint)

    var persistentEqs : Seq[IFormula] = List()

    var changed = containsFunctions
    var cont    = true
    while (cont) {
      cont = false

      for ((newBody, newConjuncts, newPersistentEqs) <-
             inlineEquations(headSyms, body, conjuncts, persistentEqs)) {
        body          = newBody
        conjuncts     = newConjuncts
        persistentEqs = newPersistentEqs
        changed       = true
        cont          = true
      }

      if (!cont && containsFunctions) {
        // check whether congruence closure is applicable

        for (newConjuncts <- congruenceClosure(conjuncts)) {
          conjuncts = newConjuncts
          changed   = true
          cont      = true
        }
      }

      if (!cont && containsFunctions) {
        // check whether ADT simplifications are possible

        for (newConjuncts <- adtRewriting(conjuncts)) {
          conjuncts = newConjuncts
          changed   = true
          cont      = true
        }
      }

      if (!cont && containsFunctions) {
        // check whether function applications can be eliminated

        for (newConjuncts <- gcFunctionApplications(headSyms, body, conjuncts)){
          conjuncts = newConjuncts
          changed   = true
          cont      = true
        }
      }
    }

    if (changed)
      Clause(head, body, and(conjuncts ++ persistentEqs))
    else
      clause
  }
}
