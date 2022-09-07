package lazabs.horn.symex

import ap.terfor.preds.Predicate
import lazabs.horn.bottomup.{HornClauses, NormClause, RelationSymbol, RelationSymbolPred, SymbolFactory, Util}
import ap.parser.{IAtom, IFormula}
import ap.terfor.conjunctions.Conjunction
import ap.theories.TheoryCollector
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.bottomup.Util.Dag

import scala.collection.mutable
import scala.collection.mutable.{ArrayBuffer, ListBuffer, HashMap => MHashMap,
  Stack => MStack, LinkedHashSet => MLinkedHashSet}

class SymExRelationSymbol(override val rawPred : Conjunction,
                          override val positive : Conjunction,
                          override val negative : Conjunction,
                          override val rs : RelationSymbol)
  extends RelationSymbolPred(rawPred, positive, negative, rs) {
  // RelationSymbolPred doesn't have the means to handle local symbols,
  // concrete states and predicates together.
}

object SymEx {
  /**
   * A class to represent Constrained Unit Clauses (CUCs)
   * @param constraint : todo
   * @param pred       : todo
   * @param sf         : symbol factory -> todo: do we need this?
   */
  case class CUC(pred       : SymExRelationSymbol,
                 constraint : Conjunction,
                 isPositive : Boolean,
                 parents : Set[Either[CUC, NormClause]])(implicit sf : SymbolFactory) {
    // todo: CUC operations
  }

  /**
   * Class to keep track of CUCs
   * Also keeps track of execution paths, i.e., clauses used to generate a CUC.
   */
  class CUCDatabase (preds : Set[SymExRelationSymbol]) {
    // for each predicate, keep an ordered set of inferred unit clauses
    // caution: the code in pop below will break if this map is made mutable and
    //           the predicates change over time!
    val inferredCUCsForPred : Map[SymExRelationSymbol, MLinkedHashSet[CUC]] =
      preds.map(pred => (pred, new MLinkedHashSet[CUC])).toMap

    val CUCs = new MLinkedHashSet[CUC]

    case class FrameInfo (numCUCs : Int,
                          numInferredCUCsForPred : Map[SymExRelationSymbol, Int])

    val frameStack = new MStack[FrameInfo]

    /**
     * Push a snapshot of the database into the stack.
     */
    def push() : Unit =
      frameStack push
        FrameInfo(numCUCs =
                    CUCs.size,
                  numInferredCUCsForPred =
                    inferredCUCsForPred.map{
                      case (pred, set) => (pred, set.size)
                    }.toMap
        )

    /**
     * Restore the database to its last pushed state.
     * @return number of dropped CUCs
     */
    def pop() : Int = {
      val frameInfo = frameStack.pop()
      val dropCount = CUCs.size - frameInfo.numCUCs
      CUCs dropRight dropCount
      inferredCUCsForPred.foreach{
        case (pred, set) =>
          val oldSize = frameInfo.numInferredCUCsForPred(pred)
          val newSize = inferredCUCsForPred(pred).size
          set dropRight (newSize - oldSize)
      }
      dropCount
    }
  }
}

abstract class SymEx[CC]
                    (implicit clause2ConstraintClause: CC => ConstraintClause) {

  import SymEx._

  /**
   * Method that returns the next clause to resolve against
   * @param  clauses: the set of original clauses
   * @return the picked clause for resolution
   */
  def clausesForResolution (clauses : Seq[(NormClause, CC)],
                            cucs    : Seq[CUC]) : Seq[]

  /**
   * Method that returns a sequence of CUCs to be used in hyper-resolution
   * on the clause picked with clauseForResolution.
   * Depth-first exploration can be achieved by returning the last cuc.
   * @param  cucs : A sequence of CUCs, sorted by increasing freshness,
   *                might be empty (i.e., do not use head or last).
   * @return The CUCs to be used in the next hyper-resolution step.
   */
  def unitClausesForResolution (cucs : Seq[CUC]) : Seq[CUC]



  def solve(iClauses : Iterable[CC]) :
  Either[Map[Predicate, IFormula], Dag[(IAtom, HornClauses.Clause)]] = {

    // first find out which theories are relevant
    val theories = {
      val coll = new TheoryCollector
      coll addTheory ap.types.TypeTheory
      for (c <- iClauses)
        c collectTheories coll
      coll.theories
    }

    if (theories.nonEmpty)
      println("Theories: " + (theories mkString ", "))

    implicit val symex_sf : SymbolFactory = new SymbolFactory(theories)

    val relationSymbols = {
      val preds =
        (for (c <- iClauses.iterator;
              lit <- (Iterator single c.head) ++ c.body.iterator;
              p = lit.predicate)
          yield p).toSet
      (for (p <- preds) yield (p -> RelationSymbol(p))).toMap
    }

    for (c <- iClauses) {
      val preds = for (lit <- c.head :: c.body.toList) yield lit.predicate
      for (p <- preds.distinct) {
        val rs = relationSymbols(p)
        for (i <- 0 until (preds count (_ == p)))
          rs arguments i
      }
    }

    // todo: We need to keep a history of which clauses are used in generating
    //       new clauses for the execution path.
    //       This means for the clauses in F, we need to maintain a sequence
    //       of ids to the original clauses.

    // translate clauses to internal form
    val normClauses: Seq[(NormClause, CC)] = (
      for (c <- iClauses) yield {
        lazabs.GlobalParameters.get.timeoutChecker() // todo: needed?
        (NormClause(c, (p) => relationSymbols(p)), c)
      }
      ).toSeq

    /**
     * Positive CUCs C ∨ p(t¯) or (p(t¯) :- ¬C) are in this context interpreted
     * as symbolic states, and represent sets of reachable program states:
     * p corresponds to a control state, t¯ is * the symbolic store, and C is
     * the negation of a path predicate.
     */

//    val positiveCUCs : Set[(CUC, CC)] =
//      normClauses.filter(c => c._1.body.isEmpty).map(c => toCUC(c)).toSet

    /**
     * Negative CUCs (C ∨ ¬p(t¯)) or (false :- ¬p(t¯), ¬C) describe states
     * from which error states are reachable.
     */

//    val negativeCUCs : Set[NormClause] = ???

    /**
     * Symbolic execution maintains a set F of CUCs, which is initialized to
     * F = ∅.
     */

    /**
     * F is the set of generated unit clauses.
     * It is implemented as a todo:??? in order to have an ordering of CUCs.
     */
    val F : ListBuffer[CUC] = new ListBuffer[CUC]

    /**In each iteration, symbolic execution will pick some clause
      * C ∈ H, unit clauses U1, . . . , Uk ∈ F, and apply the rule UHR to
      * derive a new unit clause U that is then added to F.
      */
    do {
      val clause = clauseForResolution(normClauses)
      val cucs   = unitClausesForResolution(F)
    } while (s)

    ???
  }
}


object Main extends App {
  import ap.api.SimpleAPI
  import ap.parser._
  import lazabs.horn.bottomup.HornClauses
  import IExpression._
  import HornClauses._
  /**
   * A simlpe example that encodes a simple set of clauses and directly attempts
   * to solve them. */
  SimpleAPI.withProver { p =>
    import p._
    {
      val p = createRelation("p", List(Sort.Integer))
      val x = createConstant("x")

      val clauses = List(
        p(0) :- true,
        p(x + 1) :- p(x),
        (x < 10) :- p(x)
      )

      println(clauses)

      // tSimpleWrapper.solve returns either an assignment of
      // uninterpreted predicates to relations or
      // a counterexample trace in the form of a DAG
      printResult(SymEx.solve(clauses))
      println("-" * 80)
    }
  }

  def printResult(res : Either[Map[Predicate, IFormula],
    Dag[(IAtom, HornClauses.Clause)]]) : Unit = {
    println
    res match {
      case Left(solution) =>
        println("sat\n")
        println("Solution (_n refers to the nth argument of a predicate):")
        for ((relation, formula) <- solution) {
          println(relation + ": " + formula)
        }
      case Right(cex) =>
        println("unsat\n")
        println("Counterexample:")
        cex.prettyPrint
        Util.show(cex map (_._1), "cex")
    }
  }

  def printClauses (clauses : Seq[HornClauses.Clause]) : Unit =
    clauses.foreach(clause => println (clause.toPrologString))

}