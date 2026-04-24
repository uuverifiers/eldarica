/**
 * Copyright (c) 2026 Zafer Esen. All rights reserved.
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

import ap.parser.IExpression.ConstantTerm
import ap.terfor.Term
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.terfor.substitutions.ConstantSubst
import lazabs.horn.bottomup.{NormClause, RelationSymbol}

import scala.collection.mutable.{HashMap  => MHashMap,
                                 HashSet  => MHashSet}

/**
 * An atom in a goal clause, identified by its relation symbol and
 * occurrence index. Variables are derived from the occurrence via
 * rs.arguments(occ).
 */
case class GoalAtom(rs : RelationSymbol, occ : Int) {
  def vars : Seq[ConstantTerm] = rs.arguments(occ)
}

/**
 * A (possibly non-unit) goal clause: head = FALSE, body = atoms,
 * with a shared constraint. Always in normalized form (canonical
 * occurrences, fresh residuals).
 *
 * Use the companion object factory methods to create instances.
 *
 * @param origin        the assertion clause that started this chain
 * @param parent        the goal clause before the last resolution step
 * @param parentClause  the clause used in the last resolution step
 * @param parentAtomIdx index of the atom that was resolved
 */
class GoalClause private (
    val atoms          : List[GoalAtom],
    val constraint     : Conjunction,
    val depth          : Int,
    val origin         : NormClause,
    val parent         : Option[GoalClause] = None,
    val parentClause   : Option[NormClause] = None,
    val parentAtomIdx  : Int                = -1) {

  override def equals(obj : Any) : Boolean = obj match {
    case that : GoalClause =>
      (this eq that) ||
        this.atoms == that.atoms &&
          this.constraint == that.constraint
    case _ => false
  }

  override def hashCode : Int =
    atoms.hashCode * 31 + constraint.hashCode

  /**
   * Resolve atom at `atomIdx` against clause `nc`.
   * @return a new goal clause.
   * @param simplify constraint simplifier to use
   */
  def resolveAtom(atomIdx  : Int,
                  nc       : NormClause,
                  simplify : (Conjunction, Set[Term], Boolean) => Conjunction)(
      implicit sf : SymexSymbolFactory) : GoalClause = {
    val atom      = atoms(atomIdx)
    var remaining = atoms.take(atomIdx) ++ atoms.drop(atomIdx + 1)
    var c         = constraint

    // occurrences reserved by the clause (head + body)
    val clauseOccs : Map[Predicate, Set[Int]] = {
      val m = new MHashMap[Predicate, MHashSet[Int]]
      m.getOrElseUpdate(nc.head._1.pred, new MHashSet) += nc.head._2
      for ((rs, occ) <- nc.body)
        m.getOrElseUpdate(rs.pred, new MHashSet) += occ
      m.mapValues(_.toSet).toMap
    }

    // move remaining atoms whose occ clashes with the clause
    val usedOccs = new MHashMap[Predicate, MHashSet[Int]]
    for ((pred, occs) <- clauseOccs)
      usedOccs.getOrElseUpdate(pred, new MHashSet) ++= occs
    for (a <- remaining)
      usedOccs.getOrElseUpdate(a.rs.pred, new MHashSet) += a.occ
    usedOccs.getOrElseUpdate(atom.rs.pred, new MHashSet) += atom.occ

    var moveSubst = Map[ConstantTerm, ConstantTerm]()
    remaining = remaining.map { a =>
      val occupied = clauseOccs.getOrElse(a.rs.pred, Set())
      if (!occupied.contains(a.occ)) a
      else {
        val pool = usedOccs(a.rs.pred)
        val safe =
          Iterator.from(0).find(!pool.contains(_)).get
        pool += safe
        moveSubst ++= (a.vars zip a.rs.arguments(safe))
        GoalAtom(a.rs, safe)
      }
    }
    if (moveSubst.nonEmpty)
      c = ConstantSubst(moveSubst, sf.order)(c)

    // align resolved atom with clause head
    c = ConstantSubst((atom.vars zip nc.headSyms).toMap, sf.order)(c)

    // conjoin with clause constraint, collect body atoms
    val combined = Conjunction.conj(Seq(c, nc.constraint), sf.order)
    val newBodyAtoms = nc.body.map { case (rs, occ) =>
      GoalAtom(rs, occ)
    }
    val newAtoms = remaining ++ newBodyAtoms

    // eliminate variables not in any remaining atom
    val remainingVars = newAtoms.flatMap(_.vars).toSet
    val eliminable = (combined.constants -- remainingVars)
                          .map(_.asInstanceOf[Term])
    val simplified = simplify(combined, eliminable, true)

    GoalClause(newAtoms, simplified, depth + 1,
               origin, Some(this), Some(nc), atomIdx)
  }
}

/**
 * Database for goal clauses, mirroring UnitClauseDB.
 */
class GoalClauseDB {
  private var goals : Vector[GoalClause] = Vector()

  def size     : Int     = goals.size
  def isEmpty  : Boolean = goals.isEmpty
  def nonEmpty : Boolean = goals.nonEmpty
  def allGoals : Vector[GoalClause] = goals

  def add(g : GoalClause) : Boolean = {
    if (goals contains g) false
    else { goals = goals :+ g; true }
  }
}

object GoalClause {

  /**
   * Create a normalized goal clause.
   */
  def apply(atoms          : List[GoalAtom],
            constraint     : Conjunction,
            depth          : Int,
            origin         : NormClause,
            parent         : Option[GoalClause] = None,
            parentClause   : Option[NormClause] = None,
            parentAtomIdx  : Int                = -1)(
      implicit sf : SymexSymbolFactory) : GoalClause =
    normalize(atoms, constraint, depth, origin,
              parent, parentClause, parentAtomIdx)

  /**
   * Create an initial goal clause from an assertion (head = FALSE).
   */
  def fromAssertion(nc : NormClause)(
      implicit sf : SymexSymbolFactory) : GoalClause = {
    val atoms = nc.body.map { case (rs, occ) =>
      GoalAtom(rs, occ)
    }.toList
    apply(atoms, nc.constraint, 0, nc)
  }

  // ------------------------------------------------------------------

  /**
   * Normalize a goal clause to canonical form:
   *  (1) assign sequential occurrences 0, 1, ... per predicate,
   *      skipping any occ whose argument variables already appear
   *      as residuals in the constraint
   *  (2) freshen remaining residual constants
   */
  private def normalize(
      atoms         : List[GoalAtom],
      constraint    : Conjunction,
      depth         : Int,
      origin        : NormClause,
      parent        : Option[GoalClause],
      parentClause  : Option[NormClause],
      parentAtomIdx : Int)(
      implicit sf : SymexSymbolFactory) : GoalClause = {

    if (atoms.isEmpty)
      return new GoalClause(atoms, constraint, depth, origin,
                            parent, parentClause, parentAtomIdx)

    val atomVars = atoms.flatMap(_.vars).toSet
    val residualsInConstraint = constraint.constants -- atomVars

    val predCounts = new MHashMap[Predicate, Int]
    var occSubst   = Map[ConstantTerm, ConstantTerm]()

    val normalizedAtoms = atoms.map { atom =>
      var targetOcc = predCounts.getOrElse(atom.rs.pred, 0)
      while (atom.rs.arguments(targetOcc).exists(
               residualsInConstraint.contains))
        targetOcc += 1
      predCounts(atom.rs.pred) = targetOcc + 1
      if (atom.occ == targetOcc) atom
      else {
        occSubst ++= (atom.rs.arguments(atom.occ) zip
                       atom.rs.arguments(targetOcc))
        GoalAtom(atom.rs, targetOcc)
      }
    }

    val c1 = if (occSubst.isEmpty) constraint
             else ConstantSubst(occSubst, sf.order)(constraint)

    val allArgVars = normalizedAtoms.flatMap(_.vars).toSet
    val residuals  = sf.order.sort(c1.constants -- allArgVars)

    val c2 =
      if (residuals.isEmpty) c1
      else {
        val fresh = sf.duplicateConstants(residuals)
        ConstantSubst((residuals zip fresh).toMap, sf.order)(c1)
      }

    new GoalClause(normalizedAtoms, c2, depth, origin,
                   parent, parentClause, parentAtomIdx)
  }
}
