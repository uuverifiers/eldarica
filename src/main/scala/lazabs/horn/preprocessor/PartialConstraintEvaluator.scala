/**
 * Copyright (c) 2016-2026 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.bottomup.HornClauses._

import ap.parser._
import IExpression._
import ap.theories.ModuloArithmetic
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 ArrayBuffer, LinkedHashSet, LinkedHashMap}

object PartialConstraintEvaluator {

  /**
   * Check whether this term should be moved to the constraint and be
   * preprocessed.
   */
  def needsProcessing(t : ITerm) : Boolean = try {
    NeedsProcessingVisitor.visitWithoutResult(t, ())
    false
  } catch {
    case NeedsProcessingException => true
  }

  private object NeedsProcessingException extends Exception

  private object NeedsProcessingVisitor extends CollectingVisitor[Unit, Unit] {
    override def preVisit(t : IExpression,
                          arg : Unit) : PreVisitResult = t match {
      case _ : IFormula | _ : IFunApp =>
        throw NeedsProcessingException
      case _ =>
        KeepArg
    }
    def postVisit(t : IExpression, arg : Unit, subres : Seq[Unit]) : Unit = ()
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Evaluate literals in different theories (in particular, bit-vectors) to
   * integers.
   */
  object LiteralEvaluator extends CollectingVisitor[Unit, IExpression] {
    def apply(t : IFormula) =
      visit(t, ()).asInstanceOf[IFormula]

    def postVisit(t : IExpression,
                  arg : Unit,
                  subres : Seq[IExpression]) : IExpression =
      (t, subres) match {
        case (IFunApp(ModuloArithmetic.mod_cast, _),
              Seq(Const(l), Const(u), Const(value))) =>
          i(ModuloArithmetic.evalModCast(l, u, value))
        case _ =>
          t update subres
      }
  }

  /**
   * Integer constants that are interpreted as Boolean variables by using
   * them in an equation <code>c = 0</code>.
   */
  object BooleanVar {
    def apply(c : ConstantTerm) =
      EqZ(IConstant(c))
    def unapply(f : IFormula) : Option[ConstantTerm] =
      f match {
        case EqZ(IConstant(c)) => Some(c)
        case _                 => None
      }
  }

  object BooleanLit {
    def unapply(f : IFormula) : Boolean =
      f match {
        case BooleanVar(_)       => true
        case INot(BooleanVar(_)) => true
        case _                   => false
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  object ConstrClause {
    val TRUE  = new ConstrClause(List(IBoolLit(true)))
    val FALSE = new ConstrClause(List())

    def apply(lits : Seq[IFormula]) : ConstrClause = {
      // filter duplicates and detect tautologies
      val occurring = new MHashSet[IFormula]
      val newLits = new ArrayBuffer[IFormula]

      val litIt = lits.iterator
      while (litIt.hasNext) {
        val lit = litIt.next
        if (occurring.add(lit)) {
          if (lit.isTrue || occurring.contains(~lit))
            return TRUE
          newLits += lit
        }
      }

      new ConstrClause (newLits.toSeq)
    }

    def createWithoutCheck(lits : Seq[IFormula]) : ConstrClause =
      new ConstrClause(lits)
  }

  /**
   * Class for representing constraints in clausified form.
   */
  class ConstrClause private (val literals : Seq[IFormula]) {
    def resolve(that : ConstrClause, pivot : IFormula) : ConstrClause = {
      assert(this.containsLit(pivot) && that.containsLit(~pivot) ||
             this.containsLit(~pivot) && that.containsLit(pivot))
      if (this.containsLit(pivot))
        ConstrClause(this.literals.filterNot(_ == pivot) ++
                     that.literals.filterNot(_ == ~pivot))
      else
        ConstrClause(this.literals.filterNot(_ == ~pivot) ++
                     that.literals.filterNot(_ == pivot))
    }

    def ++(that : ConstrClause) : ConstrClause =
      ConstrClause(this.literals ++ that.literals)

    def containsLit(lit : IFormula) = this.literals.contains(lit)

    def toFormula                   = or(literals)

    def isTrue                      = containsLit(IBoolLit(true))
    def isFalse                     = literals.isEmpty

    def size                        = literals.size
    def isUnit                      = size == 1

    override def toString           = s"{${literals.mkString(", ")}}"
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Class for clausifying constraints.
   */
  class Clausifier {
    private var booleanVarCounter = 0

    private def freshBooleanVar() : IFormula = {
      val c = Sort.MultipleValueBool.newConstant("boolVar" + booleanVarCounter)
      booleanVarCounter = booleanVarCounter + 1
      BooleanVar(c)
    }

    val clauses = new ArrayBuffer[ConstrClause]

    /**
     * Plaisted-Greenbaum clausification.
     */
    def pgClausify(f : IFormula) : Unit = {
      def recClausify(f : IFormula, dual : Boolean) : IFormula =
        f match {
          case IBinFormula(j, f1, f2) => {
            val newDual = dual || j == IBinJunctor.Eqv
            val newF1   = recClausify(f1, newDual)
            val newF2   = recClausify(f2, newDual)
            val newF    = IBinFormula(j, newF1, newF2)
            val p       = freshBooleanVar()
            if (dual)
              stdClausify(p <=> newF)
            else
              stdClausify(p ==> newF)
            p
          }
          case IFormulaITE(cond, f1, f2) => {
            val newCond = recClausify(cond, true)
            val newF1   = recClausify(f1, dual)
            val newF2   = recClausify(f2, dual)
            val newF    = IFormulaITE(newCond, newF1, newF2)
            val p       = freshBooleanVar()
            if (dual)
              stdClausify(p <=> newF)
            else
              stdClausify(p ==> newF)
            p
          }
          case f =>
            f
        }

      for (g <- LineariseVisitor(Transform2NNF(f), IBinJunctor.And)) {
        val clauseLits =
          for (h <- LineariseVisitor(g, IBinJunctor.Or)) yield {
            h match {
              case h@BooleanLit() => h
              case h              => recClausify(h, false)
            }
          }
        clauses += ConstrClause(clauseLits)
      }
    }

    /**
     * Standard exponential-time clausification of a formula.
     */
    def stdClausify(f : IFormula) : Unit = {
      def cl(f : IFormula) : Seq[ConstrClause] =
        f match {
          case IBinFormula(IBinJunctor.And, f1, f2) =>
            cl(f1) ++ cl(f2)
          case IBinFormula(IBinJunctor.Or, f1, f2) => {
            val cls1 = cl(f1)
            val cls2 = cl(f2)
            for (c1 <- cls1; c2 <- cls2) yield (c1 ++ c2)
          }
          case IBinFormula(IBinJunctor.Eqv, f1, f2) =>
            cl(Transform2NNF(~f1) | f2) ++ cl(f1 | Transform2NNF(~f2))
          case IFormulaITE(cond, f1, f2) =>
            cl((cond ==> f1) & (Transform2NNF(~cond) ==> f2))
          case f =>
            List(ConstrClause(List(f)))
        }
      clauses ++= cl(Transform2NNF(f))
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  object ClauseDatabase {
    object UNSAT_EXCEPTION extends Exception("constraint is unsatisfiable")
  }

  /**
   * Class for representing sets of clauses that stem from constraints.
   */
  class ClauseDatabase(eliminableBooleanVars : Seq[IFormula]) {
    import ClauseDatabase._

    val eliminableBooleanVarsSet = eliminableBooleanVars.toSet
    val unitClauses = new LinkedHashMap[IFormula, Boolean]
    val clauses     = new ArrayBuffer[ConstrClause]

    def simplifyClauses() : Unit = {
      unitPropagate()
      elimBooleanVars()
    }

    def ++=(cls : Iterable[ConstrClause]) : Unit = clauses ++= cls

    def evalLit(lit : IFormula) : Option[Boolean] =
      lit match {
        case lit@BooleanVar(_)       => unitClauses.get(lit)
        case INot(lit@BooleanVar(_)) => unitClauses.get(lit).map(!_)
        case _                       => None
      }

    def unitPropagate() : Unit = {
      var unitClausesChanged = false
      val newClauses = new ArrayBuffer[ConstrClause]

      for (clause <- clauses) {
        val newClause = prop(clause)
        if (newClause.isTrue) {
          // drop clause
        } else if (newClause.isFalse) {
          throw UNSAT_EXCEPTION
        } else if (newClause.size == 1 &&
                   BooleanLit.unapply(newClause.literals.head)) {
          newClause.literals.head match {
            case lit@BooleanVar(_)       => unitClauses.put(lit, true)
            case INot(lit@BooleanVar(_)) => unitClauses.put(lit, false)
          }
          unitClausesChanged = true
        } else {
          newClauses += newClause
        }
      }

      clauses.clear
      clauses ++= newClauses
      
      if (unitClausesChanged)
        unitPropagate()
    }

    def prop(clause : ConstrClause) : ConstrClause = {
      val newLits = new ArrayBuffer[IFormula]
      val litIt = clause.literals.iterator
      while (litIt.hasNext) {
        val lit = litIt.next
        evalLit(lit) match {
          case Some(true) =>
            // clause can be dropped
            return ConstrClause.TRUE
          case Some(false) =>
            // literal can be dropped
          case None =>
            newLits += lit
        }
      }
      ConstrClause.createWithoutCheck(newLits.toSeq)
    }

    def elimBooleanVars() : Unit = {
      val posOccurrences, negOccurrences = new MHashMap[IFormula, Int]

      for (clause <- clauses; lit <- clause.literals)
        lit match {
          case lit@BooleanVar(_) if eliminableBooleanVarsSet(lit) =>
            posOccurrences.put(lit, posOccurrences.getOrElse(lit, 0) + 1)
          case INot(lit@BooleanVar(_)) if eliminableBooleanVarsSet(lit) =>
            negOccurrences.put(lit, negOccurrences.getOrElse(lit, 0) + 1)
          case _ =>
            // nothing
        }

      var bestDiff : Long = Long.MaxValue
      var bestLit : IFormula = null

      for (lit <- eliminableBooleanVars;
           if posOccurrences.contains(lit) || negOccurrences.contains(lit)) {
        val posNum = posOccurrences.getOrElse(lit, 0)
        val negNum = negOccurrences.getOrElse(lit, 0)
        val diff = (posNum.toLong - 1) * (negNum.toLong - 1)
        if (diff < bestDiff) {
          bestDiff = diff
          bestLit = lit
        }
      }

      if (bestLit != null && bestDiff < 3) {
        elimBooleanVar(bestLit)
        unitPropagate()
        elimBooleanVars()
      } else {
        unitClauses --= eliminableBooleanVars
      }
    }

    def elimBooleanVar(v : IFormula) : Unit = {
      val posOccurrences, negOccurrences, otherClauses =
        new ArrayBuffer[ConstrClause]
      val negV = ~v

      for (clause <- clauses) {
        if (clause.containsLit(v))
          posOccurrences += clause
        else if (clause.containsLit(negV))
          negOccurrences += clause
        else
          otherClauses += clause
      }

      clauses.clear
      clauses ++= otherClauses

      for (c1 <- posOccurrences; c2 <- negOccurrences) {
        val newClause = c1.resolve(c2, v)
        if (newClause.isFalse)
          throw UNSAT_EXCEPTION
        else if (!newClause.isTrue)
          clauses += newClause
      }
    }

    def toFormula : IFormula =
      and(unitClauses.iterator.map(p => if (p._2) p._1 else ~p._2)) &&&
      and(clauses.iterator.map(_.toFormula))

    override def toString =
      unitClauses.toString + "\n" + clauses.mkString("\n")
  }

}

/**
 * Simplification and partial evaluation of the constraints. This will also
 * replace the arguments of atoms with fresh constants.
 */
class PartialConstraintEvaluator extends HornPreprocessor {
  import HornPreprocessor._
  import PartialConstraintEvaluator._

  val name : String = "partial evaluation"

  private var symbolCounter = 0

  def process(clauses : Clauses, hints : VerificationHints,
              frozenPredicates : Set[Predicate])
             : (Clauses, VerificationHints, BackTranslator) = {
    val clauseMapping = new MHashMap[Clause, Clause]

    val newClauses =
      for (clause <- clauses;
           newClause = simpConstraint(clause);
           if !newClause.constraint.isFalse) yield {
        clauseMapping.put(newClause, clause)
        newClause
      }

    val translator = new BackTranslator {
      def translate(solution : Solution) =
        solution
      def translate(cex : CounterExample) =
        for (p <- cex) yield (p._1, clauseMapping(p._2))
    }

    (newClauses, hints, translator)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def simpConstraint(clause : Clause) : Clause = {
    val Clause(head@IAtom(headPred, headArgs), body, constraint) = clause

    var newConstraint = constraint
    val seenHeadArgs = new MHashSet[ConstantTerm]

    def newConst(s : Sort) = {
      val res = s newConstant ("arg" + symbolCounter)
      symbolCounter = symbolCounter + 1
      i(res)
    }

    val newHeadArgs =
      for ((t, tSort) <- headArgs zip predArgumentSorts(headPred))
      yield t match {
        case IConstant(c) if !(seenHeadArgs contains c) => {
          seenHeadArgs += c
          t
        }
        case t => {
          val newArg = newConst(tSort)
          newConstraint = newConstraint & (t === newArg)
          newArg
        }
      }

    val newBody = for (IAtom(pred, args) <- body) yield {
      val newArgs =
        for ((t, tSort) <- args zip predArgumentSorts(pred)) yield {
          if (needsProcessing(t)) {
            val newArg = newConst(tSort)
            newConstraint = newConstraint & (t === newArg)
            newArg
          } else {
            t
          }
        }
      IAtom(pred, newArgs)
    }

    val newHead = IAtom(headPred, newHeadArgs)

    val evaluatedConstraint =
      LiteralEvaluator(PartialEvaluator(~newConstraint))

    val evaluatedConstraint2 =
      clauseLevelSimplify(
        Transform2NNF(~evaluatedConstraint),
        SymbolCollector.constants(and(newHead +: newBody)).toSet)

    val processedConstraint =
      EquivExpander(~evaluatedConstraint2)

    var prenexConstraint =
      Transform2Prenex(Transform2NNF(processedConstraint))
    var varSubst : List[ITerm] = List()
    
    var cont = true
    while (cont) prenexConstraint match {
      case IQuantified(Quantifier.ALL, d) => {
        prenexConstraint = d
        varSubst = newConst(Sort.Integer) :: varSubst
      }
      case _ =>
        cont = false
    }

    val groundConstraint = subst(prenexConstraint, varSubst, 0)

    Clause(newHead, newBody, ~groundConstraint)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Check whether the given constraint can be simplified by turning it into
   * clauses and applying the unit propagation and resolution rules.
   * The set <code>nonLocalConsts</code> specifies the constants that are
   * mentioned in head and body atoms and have to be kept, whereas other
   * constants might get eliminated through resolution.
   */
  private def clauseLevelSimplify(
                constraint     : IFormula,
                nonLocalConsts : Set[ConstantTerm]) : IFormula = {
    val clausifier = new Clausifier
    clausifier.pgClausify(constraint)

    if (clausifier.clauses.forall(_.isUnit))
      // with only unit clauses, the applied simplications won't be effective
      return constraint

    val booleanVars = new LinkedHashSet[IFormula]
    val blockedConsts = new MHashSet[ConstantTerm]
    blockedConsts ++= nonLocalConsts

    // collect constants occurring in formulas that are not Boolean literals
    for (clause <- clausifier.clauses; lit <- clause.literals) {
      lit match {
        case BooleanLit() => // ignore
        case f            => blockedConsts ++= SymbolCollector.constants(f)
      }
    }

    // collect Boolean literals
    for (clause <- clausifier.clauses; lit <- clause.literals) {
      if (Seqs.disjoint(blockedConsts, SymbolCollector.constants(lit)))
        lit match {
          case lit@BooleanVar(_)       => booleanVars += lit
          case INot(lit@BooleanVar(_)) => booleanVars += lit
          case _                       => // ignore
        }
    }

    try {
      val clauseDB = new ClauseDatabase(booleanVars.toSeq)
      clauseDB ++= clausifier.clauses
      clauseDB.simplifyClauses()
      clauseDB.toFormula
    } catch {
      case ClauseDatabase.UNSAT_EXCEPTION =>
        IBoolLit(false)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private object BooleanVarCounter {
    def apply(f : IFormula) : Map[ConstantTerm, Int] = {
      val counter = new BooleanVarCounter
      counter.visitWithoutResult(f, ())
      counter.booleanVarOccurrences --= counter.blockedVars
      counter.booleanVarOccurrences.toMap
    }
  }

  private class BooleanVarCounter extends CollectingVisitor[Unit, Unit] {
    val booleanVarOccurrences = new MHashMap[ConstantTerm, Int]
    val blockedVars           = new MHashSet[ConstantTerm]

    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult =
      t match {
        case EqZ(IConstant(c)) => {
          booleanVarOccurrences.put(c, booleanVarOccurrences.getOrElse(c, 0) + 1)
          ShortCutResult(())
        }
        case IConstant(c) => {
          blockedVars += c
          KeepArg
        }
        case _ =>
          KeepArg
      }

    def postVisit(t : IExpression, arg : Unit, subres : Seq[Unit]) : Unit = ()
  }

}
