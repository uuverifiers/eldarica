package lazabs.horn.symex

import ap.DialogUtil
import ap.parser.IExpression.{ConstantTerm, Sort}
import ap.parser.PrincessLineariser
import ap.terfor.conjunctions.Conjunction
import ap.terfor.substitutions.ConstantSubst
import ap.types.SortedConstantTerm
import lazabs.horn.bottomup.RelationSymbol
import lazabs.horn.bottomup.Util.toStream
import lazabs.horn.symex.Symex.SymexException

object UnitClause {
  def apply(rs:                  RelationSymbol,
            constraint:          Conjunction,
            isPositive:          Boolean,
            headOccInConstraint: Int)(
      implicit symex_sf:         SymexSymbolFactory): UnitClause = {

    val differentOccArgsToRewrite = headOccInConstraint match {
      case 0        => Nil
      case otherOcc => rs.arguments(otherOcc)
    }
    val differentOccSubstMap: Map[ConstantTerm, ConstantTerm] =
      (differentOccArgsToRewrite zip rs
        .arguments(0)).toMap

    val otherConstantsToRewrite =
      constraint.constants -- (differentOccArgsToRewrite ++ rs.arguments(0))
    val constantSubstMap: Map[ConstantTerm, ConstantTerm] =
      (otherConstantsToRewrite zip symex_sf
        .localSymbolsForPred(pred = rs.pred,
                             numSymbols = otherConstantsToRewrite.size,
                             occ = 0)).toMap

    val predLocalConstraint =
      ConstantSubst(differentOccSubstMap ++ constantSubstMap, symex_sf.order)(
        constraint)
    new UnitClause(rs, predLocalConstraint, isPositive)
  }
}

/**
 * A class to represent Constrained Unit Clauses (CUCs)
 * Each unit clause has its own ordered set of local symbols for each
 * occurrence id. All constant symbols are replaced with these local
 * symbols when instantiating a unit clause.
 * @param constraint :
 * @param rs        :
 * @param sf         : symbol factory
 */
//noinspection MatchToPartialFunction
class UnitClause(val rs:         RelationSymbol,
                 val constraint: Conjunction,
                 val isPositive: Boolean)(implicit sf: SymexSymbolFactory) {
  // override equals
  //def subsumes(that: UnitClause): Boolean = {
  //  this.pred == that.pred &&
  //  SimpleAPI.withProver { p =>
  //    import p._
  //    scope {
  //      addConstants(
  //        sf.order.sort(
  //         running - not repeat any work
  //          this.constraint(0).constants ++ that.constraint(0).constants))
  //      implicit val order = sf.order
  //      addAssertion(!this.constraint(0) & that.constraint(0)) // negating is
  //      problematic, functions make it unsound
  //      ??? match { // check if cuc constraint is satisfiable
  //        case ProverStatus.Invalid | ProverStatus.Unsat => true
  //        case _                                         => false
  //      }
  //    }
  //  }
  //}

  override def equals(obj: Any): Boolean = {
    obj match {
      case that: UnitClause =>
        (this eq that) ||
          that.isPositive == this.isPositive &&
            that.rs == this.rs &&
            that.constraint == this.constraint
      case _ => false
    }
  }

  val constraintAtOcc: Stream[Conjunction] = toStream { occ =>
    occ match {
      case 0 => constraint
      case i if i > 0 =>
        val orderedLocalConstants: Seq[ConstantTerm] = sf.order.sort(
          constraint.constants) diff rs.arguments(0)
        val localConstantSorts: Seq[Sort] =
          orderedLocalConstants map {
            case sc: SortedConstantTerm => sc.sort
            case _ => Sort.Integer
          }
        // share the local constants - outside somewhere in the symbol factory -
        // second class to introduce local symbols maybe
        // we know for each pred how many copies we will need, sorts do not matter
        // at this level allocate upfront
        val newConstants: Seq[ConstantTerm] =
          sf.genConstants(rs.name, localConstantSorts, "c_" + occ.toString)
        val replacements: Map[ConstantTerm, ConstantTerm] =
          (orderedLocalConstants zip newConstants).toMap
        ConstantSubst(replacements, sf.order)(constraint)
      case negOcc =>
        throw new SymexException("Occurrence cannot be less than 0.")
    }
  }

  override def toString = {
    val constraintString = DialogUtil
      .asString {
        PrincessLineariser.printExpression(
          sf.postprocessing.processFormula(constraint))
      }
    (if (isPositive) rs.toString else "") + " :- " +
      (if (isPositive) "" else rs.toString) + constraintString
  }
}
