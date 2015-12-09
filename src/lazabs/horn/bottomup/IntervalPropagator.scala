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

class IntervalPropagator(clauses : Seq[HornPredAbs.NormClause]) {

  import HornPredAbs._

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

  val clausesWithHead = (0 until clauses.size) groupBy (i => clauses(i).head._1)

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

  def toFormulas(c : ConstantTerm,
                 bounds : (Option[IdealInt], Option[IdealInt]),
                 order : TermOrder) : Iterator[Formula] = {
    implicit val _ = order
    import TerForConvenience._

    (for (b <- bounds._1.iterator) yield (c >= b)) ++
    (for (b <- bounds._2.iterator) yield (c <= b))
  }

  def extractIntervals(rs : RelationSymbol,
                       occ : Int,
                       order : TermOrder) : Iterator[Formula] = {
    val clausesH = clausesWithHead.getOrElse(rs, List())
    for ((const, constNum) <- (rs arguments occ).iterator.zipWithIndex;
         f <- if (clausesH.isEmpty) {
                Iterator.empty
              } else {
                val bounds =
                 (for (clauseNum <- clausesH.iterator)
                  yield extractBounds(clauses(clauseNum).headSyms(constNum),
                                      extendedConstraints(clauseNum),
                                      elimOrders(clauseNum))) reduce (joinBounds _)
                toFormulas(const, bounds, order)
              })
    yield f
  }

  val versions            = Array.fill(clauses.size)(0)
  val checkedInputVersion = Array.fill(clauses.size)(-1)

  {
    print("Constant and interval propagation ")

    var changed = true
    var currentVersion = 1

    while (changed) {
      changed = false
      lazabs.GlobalParameters.get.timeoutChecker()

      for ((NormClause(_, body, _), clauseNum) <- clauses.iterator.zipWithIndex) {
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
              print(".")
  
              extendedConstraints(clauseNum) = newConstr
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
