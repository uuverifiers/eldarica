/**
 * Copyright (c) 2011-2015 Philipp Ruemmer. All rights reserved.
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
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.{ConstantTerm, TermOrder, TerForConvenience,
                  Term, Formula}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction, Quantifier}
import ap.terfor.arithconj.ArithConj
import ap.PresburgerTools

import scala.collection.mutable.{HashMap => MHashMap}

object IntervalPropagator {

  val EMPTY_INTERVAL = (Some(IdealInt.ONE), Some(IdealInt.ZERO))
  val WIDENING_THRESHOLD = 5

  def isConsistent(ints : Seq[(Option[IdealInt], Option[IdealInt])]) =
    ints forall {
      case (Some(a), Some(b)) if (a > b) => false
      case _ => true
    }

  def extractBounds(c : ConstantTerm,
                    constr : Conjunction,
                    order : TermOrder) : (Option[IdealInt], Option[IdealInt]) = {
    (for (lc <- constr.arithConj.positiveEqs.toMap get c;
          if (lc.constants.size == 1))
     yield (Some(-lc.constant), Some(-lc.constant))) getOrElse {
      val inEqs = constr.arithConj.inEqs
      (inEqs.findLowerBound(LinearCombination(c, order)),
       for (b <- inEqs.findLowerBound(-LinearCombination(c, order))) yield -b)
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

class IntervalPropagator(clauses : IndexedSeq[HornPredAbs.NormClause]) {

  import HornPredAbs._
  import IntervalPropagator._

  val elimOrders = (for (clause <- clauses) yield {
    (clause.order restrict Set()) extend (
      clause.headSyms ++ clause.bodySyms.flatten ++ clause.localSymbols)
  }).toIndexedSeq

  def reduce(c : Conjunction) =
    ReduceWithConjunction(Conjunction.TRUE, c.order)(c)

  val extendedConstraints =
    (for ((NormClause(constraint, _, _), order) <-
            clauses.iterator zip elimOrders.iterator) yield {
       lazabs.GlobalParameters.get.timeoutChecker()
       reduce(constraint sortBy order)
     }).toArray

  val rsBoundCache =
    new MHashMap[RelationSymbol, Seq[(Option[IdealInt], Option[IdealInt])]]

  val clausesWithHead = (0 until clauses.size) groupBy (i => clauses(i).head._1)

  def extractIntervals(rs : RelationSymbol,
                       occ : Int,
                       order : TermOrder) : Iterator[Formula] = {
    val bounds = rsBoundCache.getOrElseUpdate(rs, {
      val clausesH = clausesWithHead.getOrElse(rs, List())

      if (clausesH.isEmpty)
        List.fill(rs.arity)((None, None))
      else
        (for (constNum <- (0 until rs.arity).iterator) yield {
           (for (clauseNum <- clausesH.iterator)
            yield extractBounds(clauses(clauseNum).headSyms(constNum),
                                extendedConstraints(clauseNum),
                                elimOrders(clauseNum))) reduce (joinBounds _)
         }).toIndexedSeq
    })

    for ((b, const) <- bounds.iterator zip (rs arguments occ).iterator;
         f <- toFormulas(const, b, order))
    yield f
  }

  //////////////////////////////////////////////////////////////////////////////

  val versions            = Array.fill(clauses.size)(0)
  val checkedInputVersion = Array.fill(clauses.size)(-1)
  var currentVersion      = 1

  //////////////////////////////////////////////////////////////////////////////
  // Abstract interpretation, to propagate possible values of predicate
  // arguments

  {
    print("Constant and interval propagation ")

    val rsBoundUpdateNum = new MHashMap[RelationSymbol, Seq[(Int, Int)]] {
      override def default(rs : RelationSymbol) : Seq[(Int, Int)] =
        for (_ <- 0 until rs.arity) yield (0, 0)
    }

    for (NormClause(_, body, head) <- clauses.iterator;
         rs <- body.iterator.map(_._1) ++ (Iterator single head._1))
      rsBoundCache.put(rs,
                       for (_ <- 0 until (rs.arity max 1)) yield EMPTY_INTERVAL)

    val rsVersions = new MHashMap[RelationSymbol, Int] {
      override def default(rs : RelationSymbol) : Int = 0
    }

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

    var changed = true

    while (changed) {
      changed = false
      lazabs.GlobalParameters.get.timeoutChecker()

      for ((clause@NormClause(_, body, (headRS, headOcc)), clauseNum) <-
               clauses.iterator.zipWithIndex) {
        val maxInputVersion =
          (0 /: (for ((rs, _) <- body.iterator) yield rsVersions(rs))) (_ max _)
        
        if (checkedInputVersion(clauseNum) < maxInputVersion) {
          checkedInputVersion(clauseNum) = maxInputVersion

          val newConstr = computeNewConstraint(clause, clauseNum)
          if (!newConstr.isFalse) {
            val oldHeadIntervals =
              rsBoundCache(headRS)
            val newHeadIntervals =
              for (c <- headRS arguments headOcc)
              yield extractBounds(c, newConstr, newConstr.order)

            val oldBoundUpdateNum = rsBoundUpdateNum(headRS)
            val (newBoundUpdateNum, joinedIntervals) =
              if (isConsistent(oldHeadIntervals))
                (for (((u1, u2), (ob@(ob1, ob2), iv2)) <-
                         oldBoundUpdateNum.iterator zip
                           (oldHeadIntervals.iterator zip
                              newHeadIntervals.iterator))
                 yield {
                   val (nb1, nb2) = joinBounds(ob, iv2)
                   val (fb1, nu1) = widen(ob1, nb1, u1)
                   val (fb2, nu2) = widen(ob2, nb2, u2)
                   ((nu1, nu2), (fb1, fb2))
                 }).toIndexedSeq.unzip
              else
                (oldBoundUpdateNum, newHeadIntervals)

            if (joinedIntervals != oldHeadIntervals) {
/*              println
              println("updating: " + headRS)
              println("old: " + oldHeadIntervals)
              println("new: " + joinedIntervals) */
              print("+")

              rsBoundCache.put(headRS, joinedIntervals)
              rsBoundUpdateNum.put(headRS, newBoundUpdateNum)
              rsVersions.put(headRS, currentVersion)
              currentVersion = currentVersion + 1

              changed = true
            }
          }
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
        versions(clauseNum) = 1
      }
      checkedInputVersion(clauseNum) = -1
    }

    rsBoundCache.clear
  }

  //////////////////////////////////////////////////////////////////////////////
  // Constraint propagation, to narrow the ranges of predicate arguments

  {
    var changed = true

    while (changed) {
      changed = false
      lazabs.GlobalParameters.get.timeoutChecker()

      for ((clause@NormClause(_, body, head), clauseNum) <-
               clauses.iterator.zipWithIndex) {
        val maxInputVersion =
          (0 /: (for ((rs, _) <- body.iterator;
                      num <- clausesWithHead.getOrElse(rs, List()).iterator)
                 yield versions(num))) (_ max _)
        
        if (checkedInputVersion(clauseNum) < maxInputVersion) {
          checkedInputVersion(clauseNum) = maxInputVersion

          val oldConstr = extendedConstraints(clauseNum)
  
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
              print("-")
  
              extendedConstraints(clauseNum) = newConstr
              rsBoundCache remove head._1
              versions(clauseNum) = currentVersion
              currentVersion = currentVersion + 1

              changed = true
            }
          }
        }
      }
    }

    println
  }

  //////////////////////////////////////////////////////////////////////////////
  // Assemble results

  val result =
    (for ((clause, clauseNum) <- clauses.iterator.zipWithIndex;
          if (!extendedConstraints(clauseNum).isFalse)) yield {
       if (versions(clauseNum) > 0) {
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
