/**
 * Copyright (c) 2011-2021 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.bottomup

import ap.PresburgerTools
import ap.parser._
import ap.terfor.{TermOrder, TerForConvenience}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.terfor.substitutions.ConstantSubst
import ap.proof.ModelSearchProver
import ap.util.Seqs

import Util._
import DisjInterpolator.{AndOrNode, AndNode, OrNode}

import scala.collection.mutable.{LinkedHashSet, LinkedHashMap, ArrayBuffer,
                                 HashSet => MHashSet, HashMap => MHashMap,
                                 ArrayStack}
import scala.util.Sorting

object CEGAR {

  case class AbstractEdge(from : Seq[AbstractState], to : AbstractState,
                          clause : NormClause, assumptions : Conjunction) {
    override def toString = "<" + (from mkString ", ") + "> -> " + to + ", " + clause
  }

  case class Counterexample(from : Seq[AbstractState], clause : NormClause)
             extends Exception("Predicate abstraction counterexample")

  object CounterexampleMethod extends Enumeration {
    val FirstBestShortest, RandomShortest, AllShortest,
        MaxNOrShortest = Value
  }

  val MaxNOr = 5

}

class CEGAR[CC <% HornClauses.ConstraintClause]
           (context : HornPredAbsContext[CC],
            predStore : PredicateStore[CC],
            predicateGenerator : Dag[AndOrNode[NormClause, Unit]] =>
                                    Either[Seq[(Predicate, Seq[Conjunction])],
                                           Dag[(IAtom, NormClause)]],
            counterexampleMethod : CEGAR.CounterexampleMethod.Value =
              CEGAR.CounterexampleMethod.FirstBestShortest) {

  import CEGAR._
  import context._
  import predStore._

  var predicateGeneratorTime : Long = 0
  var iterationNum = 0

  // Abstract states that are used for matching and instantiating clauses
  val activeAbstractStates = 
    (for (rs <- relationSymbols.values)
       yield (rs -> new LinkedHashSet[AbstractState])).toMap

  // Abstract states that are maximum (have a minimum number of
  // constraints in form of assumed predicates), and therefore not
  // subsumed by any other states
  val maxAbstractStates = 
    (for (rs <- relationSymbols.values)
       yield (rs -> new LinkedHashSet[AbstractState])).toMap

  // Subsumed abstract states, mapped to the subsuming (more general) state
  val forwardSubsumedStates, backwardSubsumedStates =
    new LinkedHashMap[AbstractState, AbstractState]

  val abstractEdges =
    new ArrayBuffer[AbstractEdge]

  //////////////////////////////////////////////////////////////////////////////

  val nextToProcess = new PriorityStateQueue

  // Expansions that have been postponed due to backwards subsumption
  val postponedExpansions =
    new ArrayBuffer[(Seq[AbstractState], NormClause, Conjunction, nextToProcess.TimeType)]

  // seed the ARG construction using the clauses with empty bodies (facts)
  for ((clause@NormClause(constraint, Seq(), _), _) <- normClauses)
    nextToProcess.enqueue(List(), clause, constraint)

  //////////////////////////////////////////////////////////////////////////////
  // The main loop

  val cegarStartTime = System.currentTimeMillis

  val rawResult : Either[Map[Predicate, Conjunction], Dag[(IAtom, CC)]] =
    /* SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>
        inferenceAPIProver = p */ {

    if (lazabs.GlobalParameters.get.log) {
      println
      println("Starting CEGAR ...")
    }

    import TerForConvenience._
    var res : Either[Map[Predicate, Conjunction], Dag[(IAtom, CC)]] = null

    while (!nextToProcess.isEmpty && res == null) {
      lazabs.GlobalParameters.get.timeoutChecker()

/*
      // The invariants supposed to be preserved by the subsumption mechanism
      assert(
        (maxAbstractStates forall {
          case (rs, preds) => (preds subsetOf activeAbstractStates(rs)) &&
                              (preds forall { s => activeAbstractStates(rs) forall {
                                                   t => s == t || !subsumes(t, s) } }) }) &&
        (backwardSubsumedStates forall {
          case (s, t) => s != t && subsumes(t, s) &&
                         (activeAbstractStates(s.rs) contains s) &&
                         !(maxAbstractStates(s.rs) contains s) &&
                         (activeAbstractStates(t.rs) contains t) }) &&
        (forwardSubsumedStates forall {
          case (s, t) => s != t && subsumes(t, s) &&
                         !(activeAbstractStates(s.rs) contains s) &&
                         (activeAbstractStates(t.rs) contains t) }) &&
        (activeAbstractStates forall {
          case (rs, preds) =>
                         preds forall { s => (maxAbstractStates(rs) contains s) ||
                         (backwardSubsumedStates contains s) } }) &&
        (postponedExpansions forall {
          case (from, _, _, _) => from exists (backwardSubsumedStates contains _) })
      )
*/

      val expansion@(states, clause, assumptions, _) = nextToProcess.dequeue

      if (states exists (backwardSubsumedStates contains _)) {
        postponedExpansions += expansion
      } else {
        try {
          for (e <- genEdge(clause, states, assumptions))
            addEdge(e)
        } catch {
          case Counterexample(from, clause) => {
            // we might have to process this case again, since
            // the extracted counterexample might not be the only one
            // leading to this abstract state
            nextToProcess.enqueue(states, clause, assumptions)

            val clauseDag = extractCounterexample(from, clause)
            iterationNum = iterationNum + 1

            if (lazabs.GlobalParameters.get.log) {
    	      println
              print("Found counterexample #" + iterationNum + ", refining ... ")

              if (lazabs.GlobalParameters.get.logCEX) {
                println
                clauseDag.prettyPrint
              }
            }
        
            {
              val predStartTime = System.currentTimeMillis
              val preds = predicateGenerator(clauseDag)
              predicateGeneratorTime =
                predicateGeneratorTime + System.currentTimeMillis - predStartTime
              preds
            } match {
              case Right(trace) => {
                if (lazabs.GlobalParameters.get.log)
                  print(" ... failed, counterexample is genuine")
                val clauseMapping = normClauses.toMap
                res = Right(for (p <- trace) yield (p._1, clauseMapping(p._2)))
              }
              case Left(newPredicates) => {
                if (lazabs.GlobalParameters.get.log)
                  println(" ... adding predicates:")
                addPredicates(newPredicates)
              }
            }
          }
        }
      }
    }
  
    if (res == null) {
      assert(nextToProcess.isEmpty)

      implicit val order = sf.order
    
      res = Left((for ((rs, preds) <- maxAbstractStates.iterator;
                       if (rs.pred != HornClauses.FALSE)) yield {
        val rawFor = disj(for (AbstractState(_, fors) <- preds.iterator) yield {
          conj((for (f <- fors.iterator) yield f.rawPred) ++
               (Iterator single relationSymbolBounds(rs)))
        })
        val simplified = //!QuantifierElimProver(!rawFor, true, order)
                         PresburgerTools elimQuantifiersWithPreds rawFor

        val symMap =
          (rs.arguments.head.iterator zip (
             for (i <- 0 until rs.arity) yield v(i)).iterator).toMap
        val subst = ConstantSubst(symMap, order)
             
        rs.pred -> subst(simplified)
      }).toMap)
    }

//    inferenceAPIProver = null

    res
  }

//  private var inferenceAPIProver : SimpleAPI = null

  val cegarEndTime = System.currentTimeMillis

  //////////////////////////////////////////////////////////////////////////////

  def printStatistics(hornPredAbsStartTime : Long) = {
    println(
         "--------------------------------- Statistics -----------------------------------")
    println("CEGAR iterations:                                      " + iterationNum)
    println("Total CEGAR time (ms):                                 " + (cegarEndTime - hornPredAbsStartTime))
    println("Setup time (ms):                                       " + (cegarStartTime - hornPredAbsStartTime))
    println("Final number of abstract states:                       " +
            (for ((_, s) <- maxAbstractStates.iterator) yield s.size).sum)
    println("Final number of matched abstract states:               " +
            (for ((_, s) <- activeAbstractStates.iterator) yield s.size).sum)
    println("Final number of abstract edges:                        " + abstractEdges.size)

    val predNum =
      (for ((_, s) <- predicates.iterator) yield s.size).sum
    val totalPredSize =
      (for ((_, s) <- predicates.iterator; p <- s.iterator)
       yield TreeInterpolator.nodeCount(p.rawPred)).sum
    val averagePredSize =
      if (predNum == 0) 0.0 else (totalPredSize.toFloat / predNum)
    println("Number of generated predicates:                        " + predNum)
    println(f"Average predicate size (# of sub-formulas):            $averagePredSize%.2f")
    println("Predicate generation time (ms):                        " + predicateGeneratorTime)

    println("Number of implication checks:                          " + implicationChecks)
    println
    println("Number of implication checks (setup):                  " + implicationChecksSetup)
    println("Number of implication checks (positive):               " + implicationChecksPos)
    println("Number of implication checks (negative):               " + implicationChecksNeg)
    println("Time for implication checks (setup, ms):               " + implicationChecksSetupTime)
    println("Time for implication checks (positive, ms):            " + implicationChecksPosTime)
    println("Time for implication checks (negative, ms):            " + implicationChecksNegTime)

    if (hasher.isActive) {
//      println
//      println("Number of state/clause matchings:                      " + matchCount)
//      println("Time for state/clause matchings (ms):                  " + matchTime)
      println
      hasher.printStatistics

      val hasherChecksNum = hasherChecksMiss + hasherChecksHit
      val hasherChecksRate =
        if (hasherChecksNum == 0)
          0
        else
          hasherChecksHit * 100 / hasherChecksNum
      println("Hasher hits/misses:                                    " +
              hasherChecksHit + "/" + hasherChecksMiss + " (" +
              hasherChecksRate + "%)")
    }

/*    println
    println("Number of subsumed abstract states:            " +
            (for ((_, s) <- activeAbstractStates.iterator;
                  t <- s.iterator;
                  if (s exists { r => r != t && subsumes(r, t) })) yield t).size) */
    println(
         "--------------------------------------------------------------------------------")
  }

  //////////////////////////////////////////////////////////////////////////////

  def subsumes(a : AbstractState, b : AbstractState) : Boolean =
    a.rs == b.rs &&
    (a.preds.size <= b.preds.size) &&
    (a.predHashCodeSet subsetOf b.predHashCodeSet) &&
    (a.predSet subsetOf b.predSet)

  def strictlySubsumes(a : AbstractState, b : AbstractState) : Boolean =
    (a.predSet.size < b.predSet.size) && subsumes(a, b)

  //////////////////////////////////////////////////////////////////////////////

  def addEdge(newEdge : AbstractEdge) = {
    addState(newEdge.to)
    abstractEdges += newEdge
//    println("Adding edge: " + newEdge)
    if (lazabs.GlobalParameters.get.log)
      print(".")
  }
  
  def addState(state : AbstractState) = if (!(forwardSubsumedStates contains state)) {
    val rs = state.rs
    if (!(activeAbstractStates(rs) contains state)) {
      // check whether the new state is subsumed by an old state
      (maxAbstractStates(rs) find (subsumes(_, state))) match {
        case Some(subsumingState) =>
//          println("Subsumed: " + state + " by " + subsumingState)
          forwardSubsumedStates.put(state, subsumingState)

        case None => {

//          println("Adding state: " + state)

          // This state has to be added as a new state. Does it
          // (backward) subsume older states?
          val subsumedStates =
            maxAbstractStates(rs).iterator.filter(subsumes(state, _)).toArray

          if (!subsumedStates.isEmpty) {
//            println("Backward subsumed by " + state + ": " + (subsumedStates mkString ", "))
            maxAbstractStates(rs) --= subsumedStates
            for (s <- subsumedStates)
              backwardSubsumedStates.put(s, state)
          }

          nextToProcess.incTime
    
          findNewMatches(state)

          activeAbstractStates(rs) += state
          maxAbstractStates(rs) += state
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  def addPredicates(preds : Seq[(Predicate, Seq[Conjunction])]) = {
    val predsToAdd = preparePredicates(preds)

    if (predsToAdd.isEmpty)
      throw new Exception("Predicate generation failed")

    // update the edges of the reachability graph with the new predicates;
    // but only consider the edges that will still be reachable afterwards

    val edgesFromState =
      (for (n <- 0 until abstractEdges.size;
            AbstractEdge(from, _, _, _) = abstractEdges(n);
            s <- from)
       yield (s, n)) groupBy (_._1)

    val newStates = new ArrayBuffer[AbstractState]
    val reachable = new MHashSet[AbstractState]

    val edgesDone = new MHashSet[Int]
    val edgesTodo = new ArrayStack[Int]
    
    for (n <- 0 until abstractEdges.size)
      if (abstractEdges(n).from.isEmpty)
        edgesTodo += n

    while (!edgesTodo.isEmpty) {
      val n = edgesTodo.pop

      if (!(edgesDone contains n)) {
        val AbstractEdge(from, to, clause, assumptions) = abstractEdges(n)
        if (from forall reachable) {
          edgesDone += n

          for (rsPreds <- predsToAdd get to.rs) hasher.scope {
            addHasherAssertions(clause, from)
            lazy val prover = emptyProver.assert(assumptions, clause.order)
            val reducer = sf reducer assumptions
            
            val additionalPreds =
              for (pred <- rsPreds;
                   if predIsConsequenceWithHasher(pred, clause.head._2,
                                                  reducer, prover,
                                                  clause.order))
              yield pred
                
            if (!additionalPreds.isEmpty) {
              val newS = AbstractState(to.rs, to.preds ++ additionalPreds)
              newStates += newS
              abstractEdges(n) = AbstractEdge(from, newS, clause, assumptions)
//              print("/")
//              println("Updating edge: " + abstractEdges(n))
            }
          }
        
          val newTo = abstractEdges(n).to
          reachable += newTo

          for (outgoing <- edgesFromState get newTo)
            for ((_, nextN) <- outgoing)
              edgesTodo += nextN
        }
      }
    }

    // Garbage collection; determine whether previously subsumed
    // states have become unsubsumed

    val (forwardUnsubsumedStates,
         backwardUnsubsumedStates) = removeGarbage(reachable)

    for (s <- backwardUnsubsumedStates)
      (activeAbstractStates(s.rs) find { t => strictlySubsumes(t, s) }) match {
        case Some(subsumingState) =>
          backwardSubsumedStates.put(s, subsumingState)
        case None =>
          maxAbstractStates(s.rs) += s
      }

    for (s <- forwardUnsubsumedStates.toSeq sortBy (_.preds.size))
      addState(s)
    for (s <- newStates)
      if (reachable contains s)
        addState(s)

    // Postponed expansions might have to be reactivated

    val (remainingExp, reactivatedExp) =
      postponedExpansions partition (_._1 exists (backwardSubsumedStates contains _))
    postponedExpansions reduceToSize 0
    postponedExpansions ++= remainingExp

    for ((states, clause, assumptions, time) <- reactivatedExp)
      nextToProcess.enqueue(states, clause, assumptions, time)
  }

  //////////////////////////////////////////////////////////////////////////////

  def findNewMatches(state : AbstractState) : Unit = {
    val startTime = System.currentTimeMillis

    val rs = state.rs

    import TerForConvenience._

    for ((clause, occ, index) <- relationSymbolOccurrences(rs)) {

      val byStates : Array[Seq[AbstractState]] =
        (for (((bodyRs, _), ind) <- clause.body.iterator.zipWithIndex)
         yield ind match {
           case `index` =>
             List(state)
           case ind if (ind < index && bodyRs == rs) =>
             activeAbstractStates(bodyRs).toSeq ++ List(state)
           case _ =>
             activeAbstractStates(bodyRs).toSeq
         }).toArray

      if (byStates exists (_.isEmpty)) {

        // nothing to do

      } else {

        implicit val _ = clause.order

        val initialAssumptions =
          sf.reduce(conj(List(clause.constraint) ++ (state instances occ)))
  
        if (!initialAssumptions.isFalse) {

          if ((byStates count (_.size > 1)) >= 2)
            matchClausePrereduce(state, initialAssumptions, clause,
                                 index, occ, byStates)
          else
            matchClauseSimple(state, initialAssumptions, clause,
                              index, occ, byStates)
        }
      }
    }

    matchCount = matchCount + 1
    matchTime = matchTime + (System.currentTimeMillis - startTime)
  }

  //////////////////////////////////////////////////////////////////////////////

  def matchClauseSimple(fixedState : AbstractState,
                        initialAssumptions : Conjunction,
                        clause : NormClause,
                        fixedIndex : Int, occ : Int,
                        byStates : Array[Seq[AbstractState]]) : Unit = {
    import TerForConvenience._
    implicit val _ = clause.order

    val NormClause(constraint, body, head) = clause

    def findPreStates(i : Int,
                      chosenStates : List[AbstractState],
                      assumptions : Conjunction) : Unit =
      if (i < 0) {
        nextToProcess.enqueue(chosenStates, clause, assumptions)
      } else if (i == fixedIndex) {
        findPreStates(i - 1, fixedState :: chosenStates, assumptions)
      } else {
        val (_, occ) = body(i)
        for (state <- byStates(i)) {
          val newAssumptions =
            sf.reduce(conj(List(assumptions) ++ (state instances occ)))
          if (!newAssumptions.isFalse)
            findPreStates(i - 1, state :: chosenStates, newAssumptions)
        }
      }

    findPreStates(body.size - 1, List(), initialAssumptions)
  }

  //////////////////////////////////////////////////////////////////////////////

  def matchClausePrereduce(state : AbstractState,
                           initialAssumptions : Conjunction,
                           clause : NormClause,
                           fixedIndex : Int, occ : Int,
                           byStates : Array[Seq[AbstractState]]) : Unit = {
    import TerForConvenience._
    implicit val _ = clause.order

    val NormClause(constraint, body, head) = clause

    val relevantRS =
      (for (p@(t, i) <- body.iterator.zipWithIndex;
            if (i != fixedIndex)) yield p).toSeq.sortBy {
        case (_, i) => byStates(i).size
      }

    var currentAssumptions = initialAssumptions
    var preReducer = sf reducer currentAssumptions

    var foundInconsistency = false
    val availableStates =
      (for (((rs, occ), i) <- relevantRS.iterator; if (!foundInconsistency)) yield {
         val states =
           (for (s <- byStates(i).iterator;
                 simp = preReducer(s predConjunction occ);
                 if (!simp.isFalse)) yield (s, simp)).toArray
         if (states.isEmpty) {
           foundInconsistency = true
         } else if (states.size == 1) {
           currentAssumptions = sf reduce conj(List(currentAssumptions, states(0)._2))
           if (currentAssumptions.isFalse)
             foundInconsistency = true
           else
             preReducer = sf reducer currentAssumptions
         }
         (states, i)
       }).toArray

    if (foundInconsistency)
      return

/*
    {
      val tableSize = body.size
      val statesTable =
        Array.ofDim[Array[(List[AbstractState], Conjunction)]](tableSize)
      statesTable(fixedIndex) = Array((List(state), Conjunction.TRUE))

      for ((x, i) <- availableStates)
        statesTable(i) = for ((s, simp) <- x) yield (List(s), simp)

      var stride = 1
      while (2 * stride < tableSize) {
        var index = 0
        while (index + stride < tableSize) {
          val states1 = statesTable(index)
          val states2 = statesTable(index + stride)
          statesTable(index) =
            (for ((s1, simp1) <- states1.iterator;
                  (s2, simp2) <- states2.iterator;
                  simp =
                    if (simp1.isTrue)
                      simp2
                    else if (simp2.isTrue)
                      simp1
                    else
                      preReducer(conj(List(simp1, simp2)));
                  if (!simp.isFalse))
             yield (s1 ++ s2, simp)).toArray
          index = index + 2 * stride
        }
        stride = stride * 2
      }

      for ((chosenStates1, simp1) <- statesTable(0);
           (chosenStates2, simp2) <- statesTable(stride)) {
        val allAssumptions =
          sf.reduce(conj(List(currentAssumptions, simp1, simp2)))
        if (!allAssumptions.isFalse) {
          val allChosenStates = chosenStates1 ++ chosenStates2
          nextToProcess.enqueue(allChosenStates, clause, allAssumptions)
        }
      }
    }
*/

    Sorting.stableSort(availableStates,
                       (x : (Array[(AbstractState, Conjunction)], Int)) => x._1.size)

    val chosenStates = Array.ofDim[AbstractState](clause.body.size)
    chosenStates(fixedIndex) = state

    val N = availableStates.size

    def findPreStates(i : Int,
                      assumptions : Conjunction) : Unit =
      if (i == N) {
        val cs = chosenStates.toList
        nextToProcess.enqueue(cs, clause, assumptions)
      } else {
        val (candidates, bodyNum) = availableStates(i)
        if (candidates.size == 1) {
          // the constraint has already been taken into account
          chosenStates(bodyNum) = candidates(0)._1
          findPreStates(i + 1, assumptions)
        } else {
          for ((state, simpStatePreds) <- candidates) {
            val newAssumptions =
              sf.reduce(conj(List(assumptions, simpStatePreds)))
            if (!newAssumptions.isFalse) {
              chosenStates(bodyNum) = state
              findPreStates(i + 1, newAssumptions)
            }
          }
        }
      }
    
    findPreStates(0, currentAssumptions)

  }

  //////////////////////////////////////////////////////////////////////////////

/*
  def matchClauseGlobal(state : AbstractState,
                        initialAssumptions : Conjunction,
                        clause : NormClause,
                        fixedIndex : Int, fixedOcc : Int,
                        combinationsDone : MHashSet[(Seq[AbstractState], NormClause)])
                       : Unit = inferenceAPIProver.scope {
    val p = inferenceAPIProver
    import p._
    import TerForConvenience._

    val rs = state.rs

    val NormClause(constraint, body, head) = clause

    addConstants(clause.order sort clause.order.orderedConstants)
    addAssertion(initialAssumptions)

    // add assertions for the possible matches
    val selectors =
      (for (((brs, occ), i) <- body.iterator.zipWithIndex)
       yield if (i == fixedIndex) {
         List()
       } else {
         val flags = createBooleanVariables(activeAbstractStates(brs).size)

         implicit val _ = order
         addAssertion(
           disj(for ((s, IAtom(p, _)) <-
                       activeAbstractStates(brs).iterator zip flags.iterator)
                  yield conj((s instances occ) ++ List(p(List())))))
         flags
       }).toIndexedSeq

     implicit val _ = order

     while (??? == ProverStatus.Sat) {
       val (chosenStates, assumptionSeq, sels) =
         (for (((brs, occ), i) <- body.iterator.zipWithIndex) yield
            if (i == fixedIndex) {
              (state, state instances occ, IExpression.i(true))
            } else {
              val selNum = selectors(i) indexWhere (evalPartial(_) == Some(true))
              val selState = activeAbstractStates(brs).iterator.drop(selNum).next
              (selState, selState instances occ, selectors(i)(selNum))
            }).toList.unzip3

       if (combinationsDone add (chosenStates, clause))
         nextToProcess.enqueue(chosenStates, clause,
           conj((for (l <- assumptionSeq.iterator; f <- l.iterator) yield f) ++ (
                  Iterator single constraint))
         )

       val blockingClause = !conj(for (IAtom(p, _) <- sels.iterator) yield p(List()))

       addAssertion(blockingClause)
     }
  }
*/

  //////////////////////////////////////////////////////////////////////////////

  def removeGarbage(reachable : MHashSet[AbstractState])
                 : (Iterable[AbstractState], Iterable[AbstractState]) = {
    val remainingEdges = for (e@AbstractEdge(from, to, _, _) <- abstractEdges;
                              if (from forall reachable))
                         yield e
    abstractEdges reduceToSize 0
    abstractEdges ++= remainingEdges
    
    for ((_, preds) <- activeAbstractStates)
      preds retain reachable
    for ((_, preds) <- maxAbstractStates)
      preds retain reachable
    
    nextToProcess removeGarbage reachable

    // Remove garbage from postponed expansion steps

    val remainingPostponedExpansions =
      for (exp@(from, _, _, _) <- postponedExpansions;
           if (from forall reachable))
      yield exp
    postponedExpansions reduceToSize 0
    postponedExpansions ++= remainingPostponedExpansions

    // Previously subsumed states might become relevant again

    val forwardUnsubsumedStates, backwardUnsubsumedStates =
      new ArrayBuffer[AbstractState]
    val remainingSubsumedStates =
      new ArrayBuffer[(AbstractState, AbstractState)]

    for (p@(state, subsumingState) <- forwardSubsumedStates)
      if (reachable contains state) {
        if (reachable contains subsumingState)
          remainingSubsumedStates += p
        else
          forwardUnsubsumedStates += state
      }

    forwardSubsumedStates.clear
    forwardSubsumedStates ++= remainingSubsumedStates

    remainingSubsumedStates.clear

    for (p@(state, subsumingState) <- backwardSubsumedStates)
      if (reachable contains state) {
        if (reachable contains subsumingState)
          remainingSubsumedStates += p
        else
          backwardUnsubsumedStates += state
      }

    backwardSubsumedStates.clear
    backwardSubsumedStates ++= remainingSubsumedStates

    (forwardUnsubsumedStates, backwardUnsubsumedStates)
  }

  def genEdge(clause : NormClause,
              from : Seq[AbstractState], assumptions : Conjunction) = {
    val startTime = System.currentTimeMillis
    lazy val prover = emptyProver.assert(assumptions, clause.order)

    hasher.scope {
      addHasherAssertions(clause, from)
      val hasherSat = hasher.isSat

      val valid =
        if (hasherSat) {
          hasherChecksHit = hasherChecksHit + 1
          false
        } else {
          val res = isValid(prover)
          if (!res)
            hasherChecksMiss = hasherChecksMiss + 1
          res
        }
    
      implicationChecks = implicationChecks + 1
      implicationChecksSetup = implicationChecksSetup + 1
      implicationChecksSetupTime =
        implicationChecksSetupTime + (System.currentTimeMillis - startTime)

      if (valid) {
        // assumptions are inconsistent, nothing to do
        None
      } else {
        // assumptions are consistent
        clause.head._1.pred match {
          case HornClauses.FALSE =>
            throw new Counterexample(from, clause)
          case _ => {
            val state = genAbstractState(assumptions,
                                         clause.head._1, clause.head._2,
                                         prover, clause.order)
            Some(AbstractEdge(from, state, clause, assumptions))
          }
        }
      }
    }
  }

  def genAbstractState(assumptions : Conjunction,
                       rs : RelationSymbol, rsOcc : Int,
                       prover : => ModelSearchProver.IncProver,
                       order : TermOrder) : AbstractState = {
    val startTime = System.currentTimeMillis
    val reducer = sf reducer assumptions
    implicationChecksSetupTime =
      implicationChecksSetupTime + (System.currentTimeMillis - startTime)
    
    val predConsequences =
      (for (pred <- predicates(rs).iterator;
            if predIsConsequenceWithHasher(pred, rsOcc,
                                           reducer, prover, order))
       yield pred).toVector
    AbstractState(rs, predConsequences)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def extractCounterexample(from : Seq[AbstractState], clause : NormClause)
                           : Dag[AndOrNode[NormClause, Unit]] = {
    // find minimal paths to reach the abstract states
    val distances = new MHashMap[AbstractState, Int]
    
    def maxDistance(states : Iterable[AbstractState]) =
      Seqs.max(states.iterator map (distances.getOrElse(_, Integer.MAX_VALUE / 2)))

    def maxDistancePlus1(states : Iterable[AbstractState]) =
      if (states.isEmpty) 0 else (maxDistance(states) + 1)
    
    var changed = true
    while (changed) {
      changed = false
      
      for (AbstractEdge(from, to, _, _) <- abstractEdges)
        if (from.isEmpty) {
          distances.put(to, 0)
        } else {
          val oldDist = distances.getOrElse(to, Integer.MAX_VALUE)
          val newDist = maxDistance(from) + 1
          if (newDist < oldDist) {
            distances.put(to, newDist)
            changed = true
          }
        }
    }

    val cex = counterexampleMethod match {

      //////////////////////////////////////////////////////////////////////////

      case CounterexampleMethod.FirstBestShortest => {
        var cex : Dag[AndOrNode[NormClause, Unit]] = DagEmpty
        val cexNodes = new MHashMap[AbstractState, Int]

        def addStateToDag(s : AbstractState) : Unit =
          if (!(cexNodes contains s)) {
            val AbstractEdge(from, _, clause, _) =
              Seqs.min(for (e@AbstractEdge(_, `s`, _, _) <- abstractEdges.iterator) yield e,
                       (e:AbstractEdge) => maxDistancePlus1(e.from))
            for (t <- from) addStateToDag(t)
            assert(!(cexNodes contains s))
            cexNodes.put(s, cex.size)
            cex = DagNode(AndNode(clause),
                          (for (t <- from.iterator) yield (cex.size - cexNodes(t))).toList,
                          cex)
        }

        for (t <- from) addStateToDag(t)
        cex = DagNode(AndNode(clause),
                      (for (t <- from.iterator) yield (cex.size - cexNodes(t))).toList,
                      cex)
        cex
      }

      //////////////////////////////////////////////////////////////////////////

      case CounterexampleMethod.AllShortest |
           CounterexampleMethod.RandomShortest |
           CounterexampleMethod.MaxNOrShortest => {
        var cex : Dag[AndOrNode[NormClause, Unit]] = DagEmpty
        var orNum = 0
        val cexNodes = new MHashMap[AbstractState, Int]

        def addStateToDag(s : AbstractState) : Unit =
          if (!(cexNodes contains s)) {
            val minDistance =
              (for (AbstractEdge(from, `s`, _, _) <- abstractEdges.iterator)
               yield maxDistancePlus1(from)).min
            val minEdges =
              for (e@AbstractEdge(from, `s`, _, _) <- abstractEdges;
                   if (maxDistancePlus1(from) == minDistance)) yield e

            val selectedEdges = counterexampleMethod match {
              case CounterexampleMethod.AllShortest |
                   CounterexampleMethod.MaxNOrShortest =>
                minEdges
              case CounterexampleMethod.RandomShortest =>
                List(minEdges(rand nextInt minEdges.size))
            }

            // recursively add all the children
            val definedEdges = 
              (for ((e@AbstractEdge(from, _, _, _), i) <-
                       selectedEdges.iterator.zipWithIndex;
                    if (i == 0 ||
                        counterexampleMethod != CounterexampleMethod.MaxNOrShortest ||
                        orNum < MaxNOr)) yield {
                 for (t <- from)
                   addStateToDag(t)
                 e
               }).toList

            val definedEdges2 = counterexampleMethod match {
              case CounterexampleMethod.MaxNOrShortest if (orNum >= MaxNOr) =>
                List(definedEdges.head)
              case _ =>
                definedEdges
            }

            for (AbstractEdge(from, _, clause, _) <- definedEdges2)
              cex = DagNode(AndNode(clause),
                            (for (t <- from.iterator) yield (cex.size - cexNodes(t))).toList,
                            cex)

            assert(!(cexNodes contains s))
            if (definedEdges2.size == 1) {
              cexNodes.put(s, cex.size - 1)
            } else {
              cexNodes.put(s, cex.size)
              cex = DagNode(OrNode(()), (1 to definedEdges2.size).toList, cex)
              orNum = orNum + 1
            }
        }

        for (t <- from) addStateToDag(t)
        cex = DagNode(AndNode(clause),
                      (for (t <- from.iterator) yield (cex.size - cexNodes(t))).toList,
                      cex)

        counterexampleMethod match {
          case CounterexampleMethod.MaxNOrShortest =>
            // then the counterexample might contain unconnected stuff
            cex.elimUnconnectedNodes
          case _ =>
            cex
        }
      }

      //////////////////////////////////////////////////////////////////////////
      
    }

//    println
//    cex.prettyPrint

    cex
  }

}
