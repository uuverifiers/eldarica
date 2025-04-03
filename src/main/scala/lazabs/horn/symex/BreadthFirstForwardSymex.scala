/**
 * Copyright (c) 2022-2025 Zafer Esen, Philipp Ruemmer. All rights reserved.
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
package lazabs.horn.symex

import ap.api.SimpleAPI.ProverStatus
import ap.parser.IAtom
import ap.util.{Combinatorics, Dijkstra}
import ap.terfor.preds.Predicate
import lazabs.horn.Util.Dag
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.bottomup.{HornClauses, NormClause, RelationSymbol}
import lazabs.horn.preprocessor.HornPreprocessor.Solution

import scala.collection.mutable.{HashSet => MHashSet, PriorityQueue,
                                 HashMap => MHashMap}

object BreadthFirstForwardSymex {

  def fix[T](f : T => T)(t : T) : T = {
    val next = f(t)
    if (t == next) t else fix(f)(next)
  }

}

/**
 * Implements a breadth-first forward symbolic execution using Symex.
 * @param maxDepth : Search will stop after deriving this many unit clauses
 *                   for a given predicate. Note that setting this value to
 *                   something other than None will yield an under-approximate
 *                   solution but will always terminate (like BMC).
 */
class BreadthFirstForwardSymex[CC](clauses  : Iterable[CC],
                                   maxDepth : Option[Int] = None)(
    implicit clause2ConstraintClause:       CC => ConstraintClause)
    extends Symex(clauses)
    with SimpleSubsumptionChecker
    with ConstraintSimplifierUsingConjunctEliminator {

  import Symex._
  import BreadthFirstForwardSymex._

  val initialTimeoutMs  = 50 // TODO: make this a setting
  val timeoutGrowthRate = 2  // TODO: make this a setting

  printInfo("Starting breadth-first forward symbolic execution (BFS)...\n")

  // Explore the state graph (the derived unit clauses) breadth-first. At
  // each depth there can be multiple choices for execution from a state
  // (the clauses to resolve with). Hence, we have a queue of states to resolve
  // with, and for each state a queue of branches to explore.
  //
  // Nonlinear clauses: there might be some paths that are accessible using more
  // than a single state, if other states we use are in the queue, we remove
  // from those states' queue the path that we are about to take.

  // The third argument of the tuple is the timeout (ms) used in sat checks.

  // The fourth argument is the cost of this expansion.

  private type QueueTuple = (NormClause, Seq[UnitClause], Long, Long)

  private implicit val queuePriority = Ordering.by[QueueTuple, Long](_._4)

  private val choicesQueue = new PriorityQueue[QueueTuple]

  private var enqueueCount : Long = 0

  private def enqueue(clause    : NormClause,
                      electrons : Seq[UnitClause],
                      timeoutMS : Long) : Unit = {
    val cost = clauseCost(clause, electrons, timeoutMS) + enqueueCount
//    println(electrons)
    printInfo(f"enqueuing, cost $cost, queue size: ${choicesQueue.size}")
//    printInfo(f"iteration count: ${iterationNumFor(electrons)}")
    choicesQueue.enqueue((clause, electrons, timeoutMS, -cost))
    enqueueCount = enqueueCount + 1
  }

  private def dequeue() : (NormClause, Seq[UnitClause], Long) = {
    val t = choicesQueue.dequeue
    (t._1, t._2, t._3)
  }

  /**
   * Map telling how far each of the predicates is away from an
   * assertion clause.
   */
  private lazy val distToAssertion : Map[Predicate, Int] = {
    val clauseGraph =
      new Dijkstra.WeightedGraph[Predicate] {
        def successors(p : Predicate) : Iterator[(Predicate, Int)] =
          for ((nc, _) <- normClauses.iterator;
               if nc.head._1.pred == p;
               (rs, _) <- nc.body.iterator)
          yield (rs.pred, 1)
      }

    Dijkstra.distances(clauseGraph, HornClauses.FALSE)
  }

  /**
   * Map telling how far each predicate is away from entry clauses.
   */
  private lazy val distFromEntry : Map[Predicate, Int] = {
    val initDist =
      (for (p <- preds.iterator) yield (p -> Int.MaxValue)).toMap

    def update(dist : Map[Predicate, Int]) : Map[Predicate, Int] = {
      val dists =
        for ((nc, _) <- normClauses) yield {
          (nc.head._1.pred,
           (Iterator(0) ++ nc.body.iterator.map(_._1.pred).map(dist)).max + 1)
        }
      dist ++ dists.groupBy(_._1).mapValues(s => s.map(_._2).min)
    }

    fix(update)(initDist)
  }

  private type IterationNum = Map[Predicate, Int]

  private val unitClauseIterationNum = new MHashMap[UnitClause, IterationNum]

  private def max(it1 : IterationNum, it2 : IterationNum) : IterationNum =
    (it1.keysIterator ++ it2.keysIterator)
      .map(p => p -> (it1.getOrElse(p, 0) max it2.getOrElse(p, 0)))
      .toMap

  private def extendIterationNum(num : IterationNum,
                                 p : Predicate) : IterationNum =
    num + (p -> (num.getOrElse(p, 0) + 1))

  private def maxIterationNum(num : IterationNum) : Long =
    (num.iterator.map(_._2) ++ Iterator(0)).max

  private def maxNIterationNum(num : IterationNum, n : Int) : Long =
    num.toSeq.map(_._2).sortBy(-_).take(n).sum

  private def iterationNumFor(u : UnitClause) : IterationNum =
    unitClauseIterationNum.get(u) match {
      case Some(r) => r
      case None => {
        val parentNum : IterationNum =
          unitClauseDB.parentsOption(u) match {
            case Some((_, parents)) => iterationNumFor(parents)
            case None               => Map()
          }
        val r = extendIterationNum(parentNum, u.rs.pred)
        unitClauseIterationNum.put(u, r)
        r
      }
    }

  private def iterationNumFor(us : Seq[UnitClause]) : IterationNum =
    us match {
      case Seq() => Map()
      case us    => us.iterator.map(iterationNumFor).reduceLeft(max)
    }

  /**
   * Determine the cost (negated priority) of elements put in the queue.
   */
  private def clauseCost(clause    : NormClause,
                         electrons : Seq[UnitClause],
                         timeoutMS : Long) : Long = {
    val headPred = clause.head._1.pred
    val increasedTimeout = timeoutMS > initialTimeoutMs

    // Check assertion clauses first
    (if (headPred == HornClauses.FALSE && !increasedTimeout) -100l else 0l) +
    // Postpone clauses with complicated constraints
    clause.constraint.opCount.toLong +
    // Postpone unit clauses with complicated constraints
    electrons.map(_.constraint.opCount.toLong).sum +
    // Postpone predicates that are far away from assertions
//    distToAssertion.getOrElse(clause.head._1.pred, 1000) * 10 +
    // Prefer predicates that are far away from entry
    distFromEntry.getOrElse(clause.head._1.pred, 1000) * -10 +
    // Penalize the maximum number of repetitions of a predicate
    maxIterationNum(extendIterationNum(iterationNumFor(electrons),
                                       headPred)) * 100 +
    // Penalize the top-3 number of repetitions of predicates
//    maxNIterationNum(extendIterationNum(iterationNumFor(electrons),
//                                        headPred), 3) * 1000000 +
    // Postpone checks with big timeout
    timeoutMS / initialTimeoutMs
  }

  private def clauseCostX(clause    : NormClause,
                          electrons : Seq[UnitClause],
                          timeoutMS : Long) : Long =
    0

  /*
   * Initialize the search by adding the facts (the initial states).
   * Each fact corresponds to a source in the search DAG.
   */
  for (fact <- facts) {
    unitClauseDB add (fact, parents = (factToNormClause(fact), Nil))
    handleNewUnitClause(fact)
  }

  def getClausesForResolution
    : Option[(NormClause, Seq[UnitClause], Long)] = {
    if (unitClauseDB.isEmpty || choicesQueue.isEmpty)
      None
    else {
      maxDepth match {
        case None => {
          Some(dequeue())
        }
        case Some(depth) =>
          var res : Option[(NormClause, Seq[UnitClause], Long)] = None
          var continue = true
          do {
            val candidate = dequeue()
            val rs        = candidate._1.head._1
            unitClauseDB.inferred(rs) match {
              case Some(cucs) if cucs.length >= depth =>
              // this is not a good candidate, continue
              case _ => // this is a good candidate, return
                continue = false
                res = Some(candidate)
            }
          } while (choicesQueue.nonEmpty && continue)
          res
      }
    }
  }

  override def handleNewUnitClause(electron : UnitClause) : Unit = {
    val possibleChoices = clausesWithRelationInBody(electron.rs)

    // for each possible choice, fix electron.rs, and resolve against
    // all previous derivations of other body literals
    for (nucleus <- possibleChoices) {
      // first find out if there are multiple occurrences of electron.rs
      val hasMultipleOccurrences = nucleus.body.count(_._1 == electron.rs) > 1

      val els = for ((rs, _) <- nucleus.body) yield {
        if (rs == electron.rs) {
          if (hasMultipleOccurrences)
            unitClauseDB.inferred(rs).getOrElse(Seq())
          else Seq(electron)
        } else unitClauseDB.inferred(rs).getOrElse(Seq())
      }
      for (choice <- Combinatorics.cartesianProduct(els.toList))
        enqueue(nucleus, choice, initialTimeoutMs)
    }

  }

  override def handleForwardSubsumption(nucleus   :   NormClause,
                                        electrons : Seq[UnitClause]) : Unit = {}

  override def handleBackwardSubsumption(subsumed : Set[UnitClause]) : Unit = {
    // todo: future work
  }

  override def handleFalseConstraint(nucleus   :   NormClause,
                                     electrons : Seq[UnitClause]) : Unit = {}

  override def solve() : Either[Solution, Dag[(IAtom, CC)]] = {
    var result : Either[Solution, Dag[(IAtom, CC)]] = null

    val touched = new MHashSet[NormClause]
    facts.foreach(fact => touched += factToNormClause(fact))

    // start traversal
    var ind : Long = 0
    while (result == null) {
      lazabs.GlobalParameters.get.timeoutChecker()
      ind += 1
      printInfo(ind + ".", false)
      getClausesForResolution match {
        case Some((nucleus, electrons, timeoutMs)) => {
          touched += nucleus
          val newElectron = hyperResolve(nucleus, electrons)
          printInfo("\t" + nucleus + "\n  +\n\t" + electrons.mkString("\n\t"))
          printInfo("  =\n\t" + newElectron)
          val isGoal = // TODO: do we need both disjuncts?
            (newElectron.rs.pred == HornClauses.FALSE) || (!newElectron.isPositive)

          if (isGoal) {
            val proverStatus =
              checkFeasibility(newElectron.constraint, Some(timeoutMs))
            if (proverStatus == ProverStatus.Unknown) { // TODO: use exception for timeouts, unknown might arise from non-timeouts?
              printInfo(s"  SAT check timed out ($timeoutMs ms), postponing...")
              enqueue(nucleus, electrons, timeoutMs*timeoutGrowthRate) // requeue
            } else if (hasContradiction(newElectron, proverStatus)) { // false :- true
              unitClauseDB.add(newElectron, (nucleus, electrons))
              result = Right(buildCounterExample(newElectron))
            }
          } else { // not a goal clause, no sat check needed
            if (newElectron.constraint.isFalse) { // only a simple check, replace with a sat check w/ short t/o?
              handleFalseConstraint(nucleus, electrons)
            } else if (checkForwardSubsumption(newElectron, unitClauseDB)) {
              printInfo("subsumed by existing unit clauses.")
              handleForwardSubsumption(nucleus, electrons)
            } else {
              val backSubsumed =
                checkBackwardSubsumption(newElectron, unitClauseDB)
              if (backSubsumed nonEmpty) {
                printInfo(
                  "subsumes " + backSubsumed.size + " existing unit clause(s)_...",
                  newLine = false)
                handleBackwardSubsumption(backSubsumed)
              }
              if (unitClauseDB.add(newElectron, (nucleus, electrons))) {
                printInfo("\n  (Added to database.)\n")
                handleNewUnitClause(newElectron)
              } else {
                printInfo("\n  (Derived clause already exists in the database.)")
                handleForwardSubsumption(nucleus, electrons)
              }
            }
          }
        }
        case None => // nothing left to explore, the clauses are SAT.
          printInfo("\t(Search space exhausted.)\n")

          // Untouched clauses can be either those which were unreachable,
          // or corner cases such as a single assertion which did not need
          // symbolic execution.
          // The only case we need to handle is assertions without body literals,
          // because assertions with uninterpreted body literals are always
          // solveable by interpreting the body literals as false.

          val untouchedClauses =
            (normClauses.map(_._1).toSet -- touched).filter(_.body.isEmpty)
          assert(untouchedClauses.forall(clause =>
            clause.head._1.pred == HornClauses.FALSE))
          if (untouchedClauses nonEmpty) {
            printInfo("\t(Dangling assertions detected, checking those too.)")
            for (clause <- untouchedClauses if result == null) {
              val cuc = // for the purpose of checking feasibility
                if (clause.body.isEmpty) {
                  new UnitClause(RelationSymbol(HornClauses.FALSE),
                    clause.constraint,
                    false)
                } else toUnitClause(clause)
              unitClauseDB.add(cuc, (clause, Nil))
              if (hasContradiction(cuc, checkFeasibility(cuc.constraint, timeoutMs = None))) {
                result = Right(buildCounterExample(cuc))
              }
            }
            if (result == null) { // none of the assertions failed, so this is SAT
              result = Left(buildSolution())
            }
          } else {
            result = Left(buildSolution())
          }
        case other =>
          throw new SymexException(
            "Cannot hyper-resolve clauses: " + other.toString)
      }
    }
    result
  }
}
