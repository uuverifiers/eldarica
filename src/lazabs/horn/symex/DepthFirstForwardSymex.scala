package lazabs.horn.symex

import ap.SimpleAPI
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.bottomup.{HornClauses, NormClause, RelationSymbol}

import scala.annotation.tailrec
import scala.collection.mutable.{
  ListBuffer,
  ArrayBuffer => MArrayBuffer,
  HashMap => MHashMap,
  HashSet => MHashSet,
  LinkedHashSet => MLinkedHashSet,
  Queue => MQueue,
  Stack => MStack
}

/**
 * This class implements a depth-first forward symbolic execution using the
 * SymEx framework.
 * @param clauses
 * @param clause2ConstraintClause
 * @tparam CC
 */
class DepthFirstForwardSymex[CC](clauses: Iterable[CC])(
    implicit clause2ConstraintClause:     CC => ConstraintClause)
    extends Symex(clauses)
    with SimpleSubsumptionChecker
    with ConstraintSimplifierUsingConjunctEliminator {

  import Symex._

  println("Starting depth-first forward symbolic execution (DFS)...\n")

  //val remainingClauses = new MLinkedHashSet[NormClause]
  //val explored         = new MHashMap[NormClause, List[Seq[UnitClause]]]

  //for ((normClause, _) <- normClauses)
  //  remainingClauses += normClause

  // keeps track of the remaining branches, has the same depth as the unit clause DB
  private val choicesStack = new MStack[MQueue[NormClause]]

  // this one saves the clauses to resolve against in case there is only a single
  // branch possible - added for performance (not to look up the choices twice)
  private val noChoiceStack = new MStack[NormClause]

  //def push(choices: MQueue[NormClause]) = {
  //  unitClauseDB.push()
  //  choiceStack.push(choices)
  //}
  //def pop() = {
  //  unitClauseDB.pop()
  //  choiceStack.pop()
  //}

  /**
   * Initialize the search by adding the facts. Each fact corresponds to a root
   * of a search tree, but we arrange this as a single search tree by pushing
   * in-between facts.
   */
  for (fact <- facts) {
    unitClauseDB add (fact, parents = (fact, Set())) // add each fact to the stack
    unitClauseDB.push() // we push regardless if there is a choice or not
    val possibleChoices = clausesWithRelationInBody(fact.rs)
    val choiceQueue     = new MQueue[NormClause]
    choiceQueue.enqueue(possibleChoices: _*)
    choicesStack push choiceQueue
    //println(
    //  "(CS) Pushed " + choicesStack.length + " (" + choicesStack.top.length + ")")
  }

  /**
   * This method is called from Symex, and should optionally return a nucleus
   * and electrons that can be hyper-resolved into another electron. The
   * sequence index i of the returned electrons should correspond to the atoms
   * at nucleus.body(i). Returns None if the search space is exhausted.
   */
  @tailrec
  final override def getClausesForResolution
    : Option[(NormClause, Seq[UnitClause])] = {
    if (unitClauseDB isEmpty) { // the search space is exhausted
      None
    } else {
      val electron = unitClauseDB.last // use last cuc to enforce depth-first exploration

      if (noChoiceStack nonEmpty) { // not a decision point
        //println("(NCS) Popped " + noChoiceStack.length)
        Some((noChoiceStack.pop(), Seq(electron)))
      } else if (choicesStack isEmpty) {
        //assert(unitClauseDB.size == 1) // we must be at the root node, search exhausted
        None
      } else {
        val possibleChoices = choicesStack.top
        possibleChoices.length match {
          case 0 => // no more resolution options for this cuc, backtrack
            choicesStack.pop()
            //println(
            //  "(CS) Popped " + choicesStack.length + " (" + choicesStack.top.length + ")")
            //val depth = unitClauseDB.pop()
            //assert(depth == choicesStack.size)
            getClausesForResolution
          case n =>
            if (n > 1) unitClauseDB.push
            val choice = possibleChoices.dequeue
            //println(
            //  "(CS) Dequeue " + choicesStack.length + " (" + choicesStack.top.length + ")")
            Some((choice, Seq(electron)))
        }
      }
    }
  }

  override def handleNewUnitClause(clause: UnitClause): Unit = {
    val possibleChoices = clausesWithRelationInBody(clause.rs)
    // "possible", because clauses might be nonlinear and we might not have all needed electrons in the DB.

    if (possibleChoices.exists(clause => clause.body.length > 1))
      ??? // todo: support nonlinear clauses, assuming they do not exist for now :-)

    possibleChoices.length match {
      case 0 =>
        println(
          "Warning: new unit clause has no clauses to resolve against " + clause)
      case 1 =>
        // this possible enqueues a unit clause with a different predicate than those
        // already in the queue, but is done for performance reasons
        // )to avoid a push to the choice stack)
        noChoiceStack push possibleChoices.head
      //println("(NCS) Pushed " + noChoiceStack.length)
      case _ => // a decision point
        val choiceQueue = new MQueue[NormClause]
        choiceQueue.enqueue(possibleChoices: _*)
        choicesStack push choiceQueue
      //println(
      //  "(CS) Pushed " + choicesStack.length + " (" + choicesStack.top.length + ")")
    }
  }

  override def handleForwardSubsumption(nucleus:   NormClause,
                                        electrons: Seq[UnitClause]): Unit = {
    println("  (DFS: handling forward subsumption.)\n")
  }

  override def handleBackwardSubsumption(subsumed: Set[UnitClause]): Unit = {
    //
  }

  override def handleFalseConstraint(nucleus:   NormClause,
                                     electrons: Seq[UnitClause]): Unit = {
    printInfo("  (DFS: backtracking.)\n")
    //println("choices b4")
    //choiceStack.foreach(println)
    ////choiceStack.pop()
    //println
    //println("choices after")
    //choiceStack.foreach(println)
    //println
    //
    val depth = unitClauseDB.pop()
    if (depth < choicesStack.size) {
      choicesStack.pop()
      //println("Popped (CS) " + choicesStack.length)
    } else if (depth == choicesStack.size) {
      // nothing
    } //else // depth > choicesStack.size, should not happen
    //assert(false)
  }
}
