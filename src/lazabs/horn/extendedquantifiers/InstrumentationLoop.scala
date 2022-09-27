package lazabs.horn.extendedquantifiers

import ap.parser.IExpression.Predicate
import ap.parser.{IAtom, IFormula}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.{IncrementalHornPredAbs, NormClause, PredicateStore}
import lazabs.horn.bottomup.Util.{Dag, DagEmpty}
import lazabs.horn.preprocessor.DefaultPreprocessor
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

import scala.collection.mutable.{HashSet => MHashSet}

object InstrumentationLoop {
  class Result
  case class Safe(solution : Map[Predicate, Conjunction]) extends Result
  case class Unsafe(cex : Dag[(IAtom, Clause)]) extends Result
  case object Inconclusive extends Result
}

class InstrumentationLoop (clauses : Clauses,
                           initialPredicates : Map[Predicate, Seq[IFormula]],
                           predicateGenerator : Dag[AndOrNode[NormClause, Unit]] =>
                             Either[Seq[(Predicate, Seq[Conjunction])],
                               Dag[(IAtom, NormClause)]]) {
  import InstrumentationLoop._

  val preprocessor = new DefaultPreprocessor
  val (simpClauses, _, backTranslator1) =
    Console.withErr(Console.out) {
      preprocessor.process(clauses, EmptyVerificationHints)
    }

  println("="*80)
  println("Clauses before instrumentation")
  println("-"*80 )
  clauses.foreach(clause => println(clause.toPrologString))
  println("="*80 + "\n")

  val instrumenter = new SimpleExtendedQuantifierInstrumenter(
    simpClauses, EmptyVerificationHints, Set.empty)

  println("="*80)
  println("Clauses after instrumentation")
  println("-"*80 )
  instrumenter.instrumentedClauses.foreach(clause => println(clause.toPrologString))
  println("="*80 + "\n")

  val simpClauses2 = instrumenter.instrumentedClauses

  //    println("="*80)
  //    println("Clauses after instrumentation (simplified)")
  //    val (simpClauses2, _, backTranslator2) =
  //      Console.withErr(Console.out) {
  //        preprocessor.process(instrumenter.instrumentedClauses, EmptyVerificationHints)
  //      }
  //    simpClauses2.foreach(clause => println(clause.toPrologString))
  //    println("="*80)

  def pickInstrumentation(space : Set[Map[Predicate, Conjunction]]) :
  Map[Predicate, Conjunction] = space.last

  val incSolver =
    new IncrementalHornPredAbs(simpClauses2,
      initialPredicates,
      instrumenter.branchPredicates,
      predicateGenerator)

  // we have m predicates for m locations to instrument, corresponding to the instrumentation constraint.
  // each instrumentation predicate can be instantiated in n ways
  // i.e., the search space is n^m.
  // for the base case, we will have n = 2, with {instrument, noInstrument}, so the search space is 2^m

  val searchSpace = new MHashSet[Map[Predicate, Conjunction]]
  instrumenter.searchSpace.foreach(search =>
    searchSpace += search.toMap)

  println("Clauses instrumented, starting search for correct instrumentation.")

  var rawResult : Result = Inconclusive
  // todo: assume empty instrumentation is in searchSpace?
  while((searchSpace nonEmpty) && rawResult == Inconclusive) {
    val instrumentation = pickInstrumentation(searchSpace.toSet)
    println("Remaining search space size: " + searchSpace.size)
    println("Selected branches: " + instrumentation.map(instr =>
      instr._1.name + "(" + (instr._2.arithConj.positiveEqs.head.constant.intValue*(-1)) + ")").mkString(", "))

    // todo: assuming empty instrumentation is not in searchSpace below
    // left sol, right cex
    incSolver.checkWithSubstitution(instrumentation) match {
      case Right(cex) => {
        println("unsafe, iterating...")
        searchSpace -= instrumentation // todo; very stupid implementation that only removes the last instrumentation
        // backTranslator.translate(cex).prettyPrint
      }
      case Left(solution) =>
        rawResult = Safe(solution)
    }
  }

  /**
   * The result of CEGAR: either a solution of the Horn clauses, or
   * a counterexample DAG containing the predicates and clauses.
   */
  lazy val result : Either[Map[Predicate, IFormula],
    Dag[(IAtom, Clause)]] = rawResult match {
    case Safe(solution) =>
      Left(for ((p, c) <- solution)
        yield {
          (p, (new PredicateStore(incSolver.baseContext)).convertToInputAbsy(
            p, List(c)).head)
        })
    case Unsafe(trace) =>
      Right(trace)
    case Inconclusive =>
      Right(DagEmpty)
  }

}
