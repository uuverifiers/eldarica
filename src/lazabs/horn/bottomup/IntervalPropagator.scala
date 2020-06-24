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

package lazabs.horn.bottomup

import ap.basetypes.IdealInt
import ap.parameters.ReducerSettings
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{ConstantTerm, TermOrder, TerForConvenience,
                  Term, Formula}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction, Quantifier}
import ap.terfor.arithconj.ArithConj
import ap.PresburgerTools

import scala.collection.mutable.{HashMap => MHashMap, LinkedHashSet,
                                 HashSet => MHashSet}

object IntervalPropagator {

  val EMPTY_INTERVAL = (Some(IdealInt.ONE), Some(IdealInt.ZERO))
  val WIDENING_THRESHOLD = 5
  val INTERVAL_PROP_THRESHOLD = 20

  def isConsistent(ints : Seq[(Option[IdealInt], Option[IdealInt])]) =
    ints forall {
      case (Some(a), Some(b)) if (a > b) => false
      case _ => true
    }

  private val smallConstant = new ConstantTerm ("smallConstant")

  def extractBounds(c : ConstantTerm,
                    constr : Conjunction,
                    order : TermOrder)
                 : (Option[IdealInt], Option[IdealInt]) =
    extractBoundsHelp(c, constr, order) match {
      case r@(Some(_), Some(_)) =>
        r
      case _ => {
        // replace c with a minimal constant in the ordering to extract
        // more information from the constraint
        implicit val _ = order
        import TerForConvenience._
        val newConstr =
          ReduceWithConjunction(c === smallConstant, order)(constr)
        extractBoundsHelp(smallConstant, newConstr, order)
      }
    }

  private def extractBoundsHelp(c : ConstantTerm, constr : Conjunction,
                                order : TermOrder)
                             : (Option[IdealInt], Option[IdealInt]) =
    (constr.arithConj.positiveEqs.toMap get c) match {
      case Some(lc) if (lc.constants.size == 1) =>
        // equation defining the value of the constant: c + offset = 0
        (Some(-lc.constant), Some(-lc.constant))
      case _ => {
        val inEqs = constr.arithConj.inEqs
        (inEqs.findLowerBound(LinearCombination(c, order)),
         for (b <- inEqs.findLowerBound(-LinearCombination(c, order)))
         yield -b)
      }
    }

  def joinBounds(a : (Option[IdealInt], Option[IdealInt]),
                 b : (Option[IdealInt], Option[IdealInt])) =
    (for (x <- a._1; y <- b._1) yield (x min y),
     for (x <- a._2; y <- b._2) yield (x max y))

  def widen(oldBound : Option[IdealInt],
            newBound : Option[IdealInt],
            oldUpdateCount : Int) : (Option[IdealInt], Int) =
    if (oldBound == newBound)
      (oldBound, oldUpdateCount)
    else if (oldUpdateCount >= WIDENING_THRESHOLD)
      (None, oldUpdateCount + 1)
    else
      (newBound, oldUpdateCount + 1)

  def toFormulas(c : ConstantTerm,
                 bounds : (Option[IdealInt], Option[IdealInt]),
                 order : TermOrder) : Iterator[Formula] = {
    implicit val _ = order
    import TerForConvenience._

    (for (b <- bounds._1.iterator) yield (c >= b)) ++
    (for (b <- bounds._2.iterator) yield (c <= b))
  }

}

class IntervalPropagator(clauses : IndexedSeq[HornPredAbs.NormClause],
                         reducerSettings : ReducerSettings) {

  import HornPredAbs._
  import IntervalPropagator._

  val elimOrders = (for (clause <- clauses) yield {
    (clause.order restrict Set()) extend (
      List(smallConstant) ++ clause.headSyms ++
      clause.bodySyms.flatten ++ clause.localSymbols)
  }).toIndexedSeq

  def reduce(c : Conjunction) =
    ReduceWithConjunction(Conjunction.TRUE, c.order, reducerSettings)(c)

  val extendedConstraints =
    (for ((NormClause(constraint, _, _), order) <-
            clauses.iterator zip elimOrders.iterator) yield {
       lazabs.GlobalParameters.get.timeoutChecker()
       reduce(constraint sortBy order)
     }).toArray

  val rsBoundCache =
    new MHashMap[RelationSymbol, Seq[(Option[IdealInt], Option[IdealInt])]]

  val clausesWithHead = (0 until clauses.size) groupBy (i => clauses(i).head._1)

  val clausesWithBodyRS =
    ((for (num <- 0 until clauses.size; (b, _) <- clauses(num).body)
      yield (num, b)) groupBy (_._2)) mapValues (_ map (_._1))

  def extractIntervals(rs : RelationSymbol,
                       occ : Int,
                       order : TermOrder) : Iterator[Formula] = {
    val bounds = rsBoundCache.getOrElseUpdate(rs, {
      val clausesH =
        for (num <- clausesWithHead.getOrElse(rs, List());
             if (!extendedConstraints(num).isFalse))
        yield num

      if (clausesH.isEmpty)
        List(EMPTY_INTERVAL)
      else
        (for (constNum <- (0 until rs.arity).iterator) yield {
           (for (clauseNum <- clausesH.iterator)
            yield extractBounds(clauses(clauseNum).headSyms(constNum),
                                extendedConstraints(clauseNum),
                                elimOrders(clauseNum))) reduce (joinBounds _)
         }).toIndexedSeq
    })

    if (isConsistent(bounds)) {
      for ((b, const) <- bounds.iterator zip (rs arguments occ).iterator;
           f <- toFormulas(const, b, order))
      yield f
    } else {
      Iterator single Conjunction.FALSE
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  val clauseQueue = new LinkedHashSet[Int]

  val modifiedClauses = new MHashSet[Int]

  //////////////////////////////////////////////////////////////////////////////
  // Abstract interpretation, to propagate possible values of predicate
  // arguments

  {
    if (lazabs.GlobalParameters.get.log)
      print("Constant and interval propagation ")

    val rsBoundUpdateNum = new MHashMap[RelationSymbol, Seq[(Int, Int)]] {
      override def default(rs : RelationSymbol) : Seq[(Int, Int)] =
        for (_ <- 0 until rs.arity) yield (0, 0)
    }

    for (NormClause(_, body, head) <- clauses.iterator;
         rs <- body.iterator.map(_._1) ++ (Iterator single head._1))
      rsBoundCache.put(rs, List(EMPTY_INTERVAL))

    def computeNewConstraint(clause : NormClause,
                             clauseNum : Int) : Conjunction = {
      val NormClause(_, body, _) = clause

      val bodyIntervals = for ((rs, _) <- body) yield rsBoundCache(rs)
      if (bodyIntervals forall (isConsistent(_))) {
        val oldConstr = extendedConstraints(clauseNum)
        implicit val order = elimOrders(clauseNum)
        import TerForConvenience._

        val intervalConstrs =
          for (((rs, occ), ivs) <- body.iterator zip bodyIntervals.iterator;
               (c, iv) <- (rs arguments occ).iterator zip ivs.iterator;
               f <- toFormulas(c, iv, order))
          yield f

        if (intervalConstrs.hasNext)
          reduce(conj((Iterator single oldConstr) ++ intervalConstrs))
        else
          oldConstr
      } else {
        Conjunction.FALSE
      }
    }

    for ((NormClause(_, Seq(), _), clauseNum) <- clauses.iterator.zipWithIndex)
      clauseQueue += clauseNum

    while (!clauseQueue.isEmpty) {
      lazabs.GlobalParameters.get.timeoutChecker()

      val clauseNum = clauseQueue.head
      clauseQueue -= clauseNum

      val clause@NormClause(_, body, (headRS, headOcc)) = clauses(clauseNum)

      val newConstr = computeNewConstraint(clause, clauseNum)
      if (!newConstr.isFalse) {
        val oldHeadIntervals =
          rsBoundCache(headRS)
        val newHeadIntervals =
          for (c <- headRS arguments headOcc)
          yield extractBounds(c, newConstr, elimOrders(clauseNum))

        val oldBoundUpdateNum = rsBoundUpdateNum(headRS)
        val (newBoundUpdateNum, joinedIntervals) =
          if (isConsistent(oldHeadIntervals))
            (for (((u1, u2), (ob@(ob1, ob2), iv2)) <-
                     oldBoundUpdateNum.iterator zip
                       (oldHeadIntervals.iterator zip newHeadIntervals.iterator))
             yield {
               val (nb1, nb2) = joinBounds(ob, iv2)
               val (fb1, nu1) = widen(ob1, nb1, u1)
               val (fb2, nu2) = widen(ob2, nb2, u2)
               ((nu1, nu2), (fb1, fb2))
             }).toIndexedSeq.unzip
          else
            (oldBoundUpdateNum, newHeadIntervals)

        if (joinedIntervals != oldHeadIntervals) {
/*          println
          println("updating: " + headRS)
          println("old: " + oldHeadIntervals)
          println("new: " + joinedIntervals) */
          if (lazabs.GlobalParameters.get.log)
            print("+")

          rsBoundCache.put(headRS, joinedIntervals)
          rsBoundUpdateNum.put(headRS, newBoundUpdateNum)

          clauseQueue ++= clausesWithBodyRS.getOrElse(headRS, List())
        }
      }
    }

    // update clause constraints where new bounds could be derived
    for ((clause@NormClause(_, _, (headRS, _)), clauseNum) <-
            clauses.iterator.zipWithIndex) {
      val oldConstr = extendedConstraints(clauseNum)
      val newConstr = computeNewConstraint(clause, clauseNum)
      if (newConstr != oldConstr) {
//println("old constr: " +extendedConstraints(clauseNum)) 
        extendedConstraints(clauseNum) = newConstr
//println("new constr: " +extendedConstraints(clauseNum)) 
        modifiedClauses += clauseNum
      }

      // clauses with satisfiable constraint are processes further
      if (!newConstr.isFalse)
        clauseQueue += clauseNum
    }

    rsBoundCache.clear
  }

  //////////////////////////////////////////////////////////////////////////////
  // Constraint propagation, to narrow the ranges of predicate arguments

  {
    val clauseUpdateCount = Array.fill(clauses.size)(0)

    while (!clauseQueue.isEmpty) {
      lazabs.GlobalParameters.get.timeoutChecker()

      val clauseNum = clauseQueue.head
      clauseQueue -= clauseNum

      val oldUpdateCount = clauseUpdateCount(clauseNum)

      if (oldUpdateCount < INTERVAL_PROP_THRESHOLD) {
        clauseUpdateCount(clauseNum) = oldUpdateCount + 1

        val oldConstr = extendedConstraints(clauseNum)
        if (!oldConstr.isFalse) {
          val clause@NormClause(_, body, (headRS, _)) = clauses(clauseNum)

          implicit val order = elimOrders(clauseNum)
          import TerForConvenience._

          val newConstraints =
            for ((rs, occ) <- body.iterator;
                 c <- extractIntervals(rs, occ, order)) yield c
  
          if (newConstraints.hasNext) {
            val newConstr = reduce(
              conj((Iterator single oldConstr) ++ newConstraints))
  
            if (oldConstr != newConstr) {
/*              println
              println("old: " + oldConstr)
              println("new: " + newConstr) */
              if (lazabs.GlobalParameters.get.log)
                print("-")
  
              extendedConstraints(clauseNum) = newConstr
              rsBoundCache remove headRS

              modifiedClauses += clauseNum
              clauseQueue ++= clausesWithBodyRS.getOrElse(headRS, List())
            }
          }
        }
      }
    }

    if (lazabs.GlobalParameters.get.log) {
      println
      println
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Assemble results

  val result : Seq[(HornPredAbs.NormClause, HornPredAbs.NormClause)] =
    (for ((clause, clauseNum) <- clauses.iterator.zipWithIndex;
          if (!extendedConstraints(clauseNum).isFalse)) yield {
       if (modifiedClauses contains clauseNum) {
         val newConstr = reduce(extendedConstraints(clauseNum) sortBy clause.order)
         (clause updateConstraint newConstr, clause)
       } else {
         (clause, clause)
       }
     }).toList

  val rsBounds : Map[RelationSymbol, Conjunction] =
    clausesWithHead transform {
      case (rs, _) =>
        reduce(Conjunction.conj(extractIntervals(rs, 0, rs.sf.order), rs.sf.order))
    }

}
