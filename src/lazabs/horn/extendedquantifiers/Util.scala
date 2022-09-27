package lazabs.horn.extendedquantifiers

import ap.parser.IExpression.Eq
import ap.parser.{CollectingVisitor, IAtom, IExpression, IFormula, IFunApp, ITerm}
import ap.theories.ExtArray
import ap.types.{MonoSortedPredicate, Sort}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}
import scala.collection.immutable.Map

object Util {
  case class ExtendedQuantifierInfo (exTheory  : ExtendedQuantifier,
                                     funApp    : IFunApp,
                                     arrayTerm : ITerm,
                                     loTerm    : ITerm,
                                     hiTerm    : ITerm)

  case class SelectInfo(a : ITerm, i : ITerm, o : ITerm,
                        theory : ExtArray)
  case class StoreInfo(oldA : ITerm, newA : ITerm, i : ITerm, o : ITerm,
                       theory : ExtArray)
  case class ConstInfo(newA : ITerm, o : ITerm, theory : ExtArray)


  def extractSelectInfo (conjunct : IFormula) : SelectInfo = {
    // todo: error checking?
    val Eq(IFunApp(f@ExtArray.Select(theory), Seq(a, i)), o) = conjunct
    SelectInfo(a, i, o, theory)
  }
  def extractStoreInfo (conjunct : IFormula) : StoreInfo = {
    // todo: error checking?
    val Eq(IFunApp(f@ExtArray.Store(theory), Seq(a1, i, o)), a2) = conjunct
    StoreInfo(a1, a2, i, o, theory)
  }
  def extractConstInfo (conjunct : IFormula) : ConstInfo = {
    // todo: error checking?
    val Eq(IFunApp(f@ExtArray.Const(theory), Seq(o)), a) = conjunct
    ConstInfo(a, o, theory)
  }

  /**
   * Class for collecting the extended quantifier applications
   * occurring in an expression.
   */
  object ExtQuantifierFunctionApplicationCollector {
    def apply(t : IExpression) : Seq[ExtendedQuantifierInfo] = {
      val apps = new ArrayBuffer[ExtendedQuantifierInfo]
      val c = new ExtQuantifierFunctionApplicationCollector (apps)
      c.visitWithoutResult(t, 0)
      apps
    }
  }
  class ExtQuantifierFunctionApplicationCollector(extQuantifierInfos : ArrayBuffer[ExtendedQuantifierInfo])
    extends CollectingVisitor[Int, Unit] {
    def postVisit(t : IExpression, boundVars : Int, subres : Seq[Unit]) : Unit =
      t match {
        case app@IFunApp(ExtendedQuantifier.ExtendedQuantifierFun(theory), Seq(a, lo, hi)) =>
          extQuantifierInfos +=
            ExtendedQuantifierInfo(theory, app, a, lo, hi)
        case _ => // nothing
      }
  }

  def isSelect (conjunct : IFormula) : Boolean = conjunct match {
    case Eq(IFunApp(f@ExtArray.Select(_), Seq(a, i)), o) => true
    case _ => false
  }
  def isStore (conjunct : IFormula) : Boolean = conjunct match {
    case Eq(IFunApp(f@ExtArray.Store(_), Seq(a1, i, o)), a2) => true
    case _ => false
  }
  def isConst (conjunct : IFormula) : Boolean = conjunct match {
    case Eq(IFunApp(f@ExtArray.Const(_), Seq(o)), a) => true
    case _ => false
  }
  def isExtQuans (conjunct : IFormula) : Boolean = conjunct match {
    case Eq(IFunApp(f@ExtendedQuantifier.ExtendedQuantifierFun(_), _), _) => true
    case _ => false
  }
  def getNewArrayTerm(conjunct : IFormula) : (Seq[ITerm], Seq[Sort]) =
    conjunct match {
      case Eq(IFunApp(f@ExtArray.Const(theory), _), a) =>
        (Seq(a), Seq(theory.sort))
      case Eq(IFunApp(f@ExtArray.Store(theory), _), a) =>
        (Seq(a), Seq(theory.sort))
      case _ => (Nil, Nil)
    }
  def getOriginalArrayTerm(conjunct : IFormula) : (Seq[ITerm], Seq[Sort]) =
    conjunct match {
      case Eq(IFunApp(f@ExtArray.Store(theory), Seq(a, _, _)), _) =>
        (Seq(a), Seq(theory.sort))
      case _ => (Nil, Nil)
    }

  def collectArgsSortsFromAtoms(atoms : Seq[IAtom]) : (Seq[ITerm], Seq[Sort]) = {
    val sorts : Seq[Sort] =
      (for(atom <- atoms) yield {
        atom.pred match {
          case p: MonoSortedPredicate => p.argSorts
          case p => Seq.fill(p.arity)(Sort.Integer)
        }
      }).flatten
    (atoms.flatMap(_.args), sorts)
  }

  def gatherExtQuans (clauses : Clauses) : Seq[ExtendedQuantifierInfo] =
    (for (Clause(head, body, constraint) <- clauses) yield {
      val exqs : Seq[ExtendedQuantifierInfo] =
        ExtQuantifierFunctionApplicationCollector(constraint)
      exqs
    }).flatten
}
