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

import ap.parser._
import HornClauses.ConstraintClause
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.{Term, TermOrder, ConstantTerm, VariableTerm, TerForConvenience}
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.substitutions.{ConstantSubst, VariableSubst}
import ap.util.Seqs

import scala.collection.mutable.ArrayBuffer

  object NormClause {
    def apply[CC](c : CC, predMap : Predicate => RelationSymbol)
             (implicit sf : SymbolFactory,
              conv : CC => ConstraintClause)
             : NormClause = {
      assert(c.localVariableNum == 0) // currently only this case is supported

      var rss = List[RelationSymbol]()
      
      val (lits, litSyms) = (for (lit <- c.body ++ List(c.head)) yield {
        val rs = predMap(lit.predicate)
        val occ = rss count (_ == rs)
        rss = rs :: rss
        ((rs, occ), rs.arguments(occ))
      }).unzip
      
      // use a local order to speed up the conversion in case of many symbols
//      val syms = (for ((rs, occ) <- lits.iterator;
//                       c <- rs.arguments(occ).iterator) yield c).toSet
//      val localOrder = sf.order restrict syms

      val constraint =
        sf.preprocess(
          c.instantiateConstraint(litSyms.last, litSyms.init, List(),
                                  sf.signature))

      val skConstraint =
        skolemise(constraint, false, List())
      val finalConstraint =
        if (skConstraint eq constraint)
          constraint
        else
          sf reduce skConstraint

      NormClause(finalConstraint, lits.init, lits.last)
    }

  private def skolemise(c : Conjunction,
                        negated : Boolean,
                        substTerms : List[Term])
                       (implicit sf : SymbolFactory) : Conjunction = {
    import TerForConvenience._

    val newSubstTerms = c.quans match {
      case Seq() =>
        substTerms
      case quans => {
        val N = quans.size
        Seqs.prepend(
          for ((q, n) <- quans.zipWithIndex) yield q match {
            case Quantifier.EX if !negated => sf.genSkolemConstant
            case Quantifier.ALL if negated => sf.genSkolemConstant
            case _ => v(n)
          },
          for (t <- substTerms) yield t match {
            case VariableTerm(ind) => VariableTerm(ind + N)
            case t => t
          })
      }
    }

    val newNegConjs =
      c.negatedConjs.update(
        for (d <- c.negatedConjs) yield skolemise(d, !negated, newSubstTerms),
        sf.order)

    if (newSubstTerms.isEmpty) {
      c.updateNegatedConjs(newNegConjs)(sf.order)
    } else {
      val subst = VariableSubst(0, newSubstTerms, sf.order)
      Conjunction(c.quans,
                  subst(c.arithConj),
                  subst(c.predConj),
                  newNegConjs,
                  sf.order)
    }
  }
  }

  case class NormClause(constraint : Conjunction,
                        body : Seq[(RelationSymbol, Int)],
                        head : (RelationSymbol, Int))
                       (implicit sf : SymbolFactory) {
    val headSyms : Seq[ConstantTerm] =
      head._1.arguments(head._2)
    val bodySyms : Seq[Seq[ConstantTerm]] =
      for ((rs, occ) <- body) yield (rs arguments occ)
    val order = sf.order restrict (
      constraint.constants ++ headSyms ++ bodySyms.flatten)
    val localSymbols : Seq[ConstantTerm] =
      order.sort(constraint.constants -- headSyms -- bodySyms.flatten)
    val allSymbols =
      (localSymbols.iterator ++ headSyms.iterator ++ (
          for (cl <- bodySyms.iterator; c <- cl.iterator) yield c)).toSeq

    // indexes of the bodySyms constants that actually occur in the
    // constraint and are therefore relevant
    val relevantBodySyms : Seq[Seq[Int]] =
      for (syms <- bodySyms) yield
        (for ((c, i) <- syms.iterator.zipWithIndex;
              if (constraint.constants contains c)) yield i).toSeq

    def freshConstraint(implicit sf : SymbolFactory)
                       : (Conjunction, Seq[ConstantTerm], Seq[Seq[ConstantTerm]]) = {
      val newLocalSyms =
        sf duplicateConstants localSymbols
      val newHeadSyms = 
        sf duplicateConstants headSyms
      val newBodySyms =
        for (cs <- bodySyms) yield (sf duplicateConstants cs)
      
      val newSyms =
        newLocalSyms.iterator ++ newHeadSyms.iterator ++ (
          for (syms <- newBodySyms.iterator; c <- syms.iterator) yield c)
      val subst = ConstantSubst((allSymbols.iterator zip newSyms).toMap, sf.order)
      (subst(constraint), newHeadSyms, newBodySyms)
    }

    def substituteSyms(newLocalSyms : Seq[ConstantTerm],
                       newHeadSyms : Seq[ConstantTerm],
                       newBodySyms : Seq[Seq[ConstantTerm]])
                      (implicit order : TermOrder) : Conjunction = {
      val newSyms =
        newLocalSyms.iterator ++ newHeadSyms.iterator ++ (
          for (syms <- newBodySyms.iterator; c <- syms.iterator) yield c)
      val subst = ConstantSubst((allSymbols.iterator zip newSyms).toMap, order)
      subst(constraint)
    }

    def updateConstraint(newConstraint : Conjunction) =
      NormClause(newConstraint, body, head)

    def substituteRS(subst : Map[RelationSymbol, Conjunction]) : NormClause = {
      val newConstraints = new ArrayBuffer[Conjunction]
      val remBody = body filter {
        case (rs, occ) =>
          (subst get rs) match {
            case Some(f) => {
              newConstraints += VariableSubst(0, rs.arguments(occ), order)(f)
              false
            }
            case None =>
              true
          }
      }

      val newHead =
        (subst get head._1) match {
          case Some(f) => {
            newConstraints +=
              !VariableSubst(0, head._1.arguments(head._2), order)(f)
            (RelationSymbol(HornClauses.FALSE), 0)
          }
          case None =>
            head
        }

      if (newConstraints.isEmpty) {
        this
      } else {
        newConstraints += constraint
        NormClause(sf reduce Conjunction.conj(newConstraints, order),
                   remBody, newHead)
      }
    }

    override def toString =
      "" + head._1.toString(head._2) +
      " :- " + ((for ((rs, occ) <- body) yield rs.toString(occ)) mkString ", ") +
      " | " + constraint
  }
