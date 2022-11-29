/**
 * Copyright (c) 2022 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import ap.{DialogUtil, PresburgerTools, SimpleAPI}
import ap.terfor.preds.Predicate
import lazabs.horn.bottomup.{HornClauses, NormClause, RelationSymbol, Util}
import ap.parser.{
  IAtom,
  IExpression,
  IFormula,
  InputAbsy2Internal,
  PrincessLineariser
}
import ap.terfor.{ComputationLogger, Term, TermOrder}
import ap.terfor.conjunctions.{
  ConjunctEliminator,
  Conjunction,
  ReduceWithConjunction
}
import ap.theories.{Theory, TheoryCollector}
import lazabs.horn.bottomup.HornClauses.{Clause, ConstraintClause}
import lazabs.horn.bottomup.PredicateStore.QuantifierInPredException
import lazabs.horn.bottomup.Util.{Dag, toStream}
import IExpression._
import ap.api.SimpleAPI.ProverStatus
import ap.terfor.arithconj.ModelElement
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.substitutions.{ConstantSubst, VariableSubst}
import ap.types.SortedConstantTerm

import scala.annotation.tailrec
import scala.collection.mutable.{
  ListBuffer,
  ArrayBuffer => MArrayBuffer,
  HashMap => MHashMap,
  HashSet => MHashSet,
  LinkedHashSet => MLinkedHashSet,
  Stack => MStack
}

object Symex {
  class SymexException(msg: String) extends Exception(msg)

  var printInfo = true

  def printInfo(s: String, newLine: Boolean = true): Unit = {
    if (printInfo)
      print(s + (if (newLine) "\n" else ""))
  }

  implicit def toUnitClause(normClause: NormClause)(
      implicit sf:                      SymexSymbolFactory): UnitClause = {
    normClause match {
      case NormClause(constraint, Nil, (rel, 0)) // a fact
          if rel.pred != HornClauses.FALSE =>
        UnitClause(rel, constraint, isPositive = true, headOccInConstraint = 0)
      case NormClause(constraint, Seq((rel, 0)), (headRel, 0))
          if headRel.pred == HornClauses.FALSE =>
        UnitClause(rel, constraint, isPositive = false, headOccInConstraint = 0)
      case _ =>
        throw new UnsupportedOperationException(
          "Trying to create a unit clause from a non-unit clause!" + normClause)
    }
  }

}

abstract class Symex[CC](iClauses:    Iterable[CC])(
    implicit clause2ConstraintClause: CC => ConstraintClause
) extends SubsumptionChecker
    with ConstraintSimplifier {

  import Symex._

  val theories: Seq[Theory] = {
    val coll = new TheoryCollector
    coll addTheory ap.types.TypeTheory
    for (c <- iClauses)
      c collectTheories coll
    coll.theories
  }

  if (theories.nonEmpty)
    printInfo("Theories: " + (theories mkString ", ") + "\n")

  val preds: Set[Predicate] =
    (for (c   <- iClauses.iterator;
          lit <- (Iterator single c.head) ++ c.body.iterator;
          p = lit.predicate)
      yield p).toSet

  // We keep a prover initialized with all the symbols running, which we will
  // use to check the satisfiability of constraints.
  // Note that the prover must be manually shut down for clean-up.
  implicit val prover = SimpleAPI.spawn
  prover.addTheories(theories)
  prover.addRelations(preds)

  // Keeps track of all the terms and adds new symbols to the prover
  // must be initialized after normClauses are generated.
  implicit val symex_sf: SymexSymbolFactory =
    new SymexSymbolFactory(theories, prover)

  val relationSymbols: Map[Predicate, RelationSymbol] =
    (for (p <- preds) yield (p -> RelationSymbol(p))).toMap

  // translate clauses to internal form
  val normClauses: Seq[(NormClause, CC)] = (
    for (c <- iClauses) yield {
      lazabs.GlobalParameters.get.timeoutChecker() // todo: needed?
      (NormClause(c, p => relationSymbols(p)), c)
    }
  ).toSeq

  val clausesWithRelationInBody: Map[RelationSymbol, Seq[NormClause]] =
    (for (rel <- relationSymbols.values) yield {
      (rel,
       normClauses.filter(_._1.body.exists(brel => brel._1 == rel)).map(_._1))
    }).toMap

  val clausesWithRelationInHead: Map[RelationSymbol, Seq[NormClause]] =
    (for (rel <- relationSymbols.values) yield {
      (rel, normClauses.filter(_._1.head._1 == rel).map(_._1))
    }).toMap

  val predicatesAndMaxOccurrences: Map[Predicate, Int] =
    for ((rp, clauses) <- clausesWithRelationInHead)
      yield (rp.pred, clauses.map(_.head._2).max)

  // this must be done before we can use the symbol factory during resolution
  symex_sf.initialize(predicatesAndMaxOccurrences.toSet)

  val facts: Set[NormClause] =
    (for ((normClause, _) <- normClauses
          if normClause.body.isEmpty && normClause.head._1.pred != HornClauses.FALSE)
      yield { normClause }).toSet

  val goals: Set[NormClause] =
    (for ((normClause, _) <- normClauses
          if normClause.head._1.pred == HornClauses.FALSE && normClause.body.length == 1)
      yield { normClause }).toSet

  // picks the next clauses to apply hyper-resolution on (nucleus + electrons).
  // this method decides the traversal method (of the tree of CUCs).
  // if non-empty, returns a nucleus and electrons that hyper-resolve to another electron.
  // there is one electron per body literal in the normal clause
  def getClausesForResolution: Option[(NormClause, Seq[UnitClause])]

  // todo: move hyperresolution to outside this class
  /**
   * Applies hyper-resolution to a clause using the input unit clauses
   * This implementation only infers positive CUCs
   *
   * @return resulting CUC.
   *         "FALSE :- constraint" is also considered a unit clause.
   */
  private def hyperResolve(nucleus:   NormClause,
                           electrons: Seq[UnitClause]): UnitClause = {

    assert(electrons.length == nucleus.body.length)

    // assumptions:
    //  constants in a nucleus are distinct from all constants of unit clauses
    val constraintFromElectrons =
      for (((rp, occ), ind) <- nucleus.body.zipWithIndex) yield {
        //println("rp: " + rp)
        //println("el: " + electrons(ind).rel)
        assert(rp == electrons(ind).rs)
        // we do not need to replace arguments of rp by construction
        // but we need to rewrite the constraint of the electron if occ is not 0
        if ((electrons(ind)
              .constraintAtOcc(occ)
              .constants intersect nucleus.head._1.arguments.head.toSet) nonEmpty)
          electrons(ind).constraintAtOcc(occ + 1)
        else
          electrons(ind).constraintAtOcc(occ)
      }

    val unsimplifiedConstraint =
      Conjunction.conj(constraintFromElectrons ++ Seq(nucleus.constraint),
                       symex_sf.order)

    val localSymbols =
      (unsimplifiedConstraint.constants -- nucleus.headSyms)
        .map(_.asInstanceOf[Term])
    //println("local symbols: " + localSymbols)
    // todo; first build conj of formulas, then take the consts from that -- head syms
    // todo: take reducer from the sf - should fix - make this an option?

    val simplifiedConstraint =
      simplifyConstraint(unsimplifiedConstraint,
                         localSymbols,
                         reduceBeforeSimplification = true)

    // In the simplified constraint:
    //   1. If nucleus head predicate arguments are not at occurrence 0,
    //   they must be replaced with occurrence 0 terms.
    //   2. If any non-constant terms belonging to other electrons remain,
    //   they must be replaced with predicate-local symbols.

    //// 1. Detect if we need to rewrite head predicate arguments
    //val nucleusSubst: Map[ConstantTerm, ConstantTerm] =
    //  if (nucleus.head._2 != 0) { // if head occurrence is not 0
    //    (nucleus.headSyms zip nucleus.head._1.arguments(0)).toMap
    //  } else Map()

    // 2. Detect non-local terms from the electrons remaining in the constraint.
    // This includes local and non-local symbols in those electrons.
    // todo: this will also rewrite when the clause is recursive, can we optimize?
    //val remainingArgs = nucleus.body.flatMap {
    //  case (rp, occ) =>
    //    rp.arguments(occ).toSet.intersect(simplifiedConstraint.constants)
    //}

    //   Get one local symbol for each remaining arg
    //val electronSubst: Map[ConstantTerm, ConstantTerm] =
    //  (remainingArgs zip symex_sf
    //    .localSymbolsForPred(pred = nucleus.head._1.pred,
    //                         numSymbols = remainingArgs.length,
    //                         occ = 0)).toMap
    //
    //val newConstraint = ConstantSubst(nucleusSubst ++ electronSubst,
    //                                  symex_sf.order)(simplifiedConstraint)

    //new UnitClause(nucleus.head._1, newConstraint, isPositive = true) // todo: currently only positive CUCs are generated
    UnitClause(rs = nucleus.head._1,
               constraint = simplifiedConstraint,
               isPositive = true,
               headOccInConstraint = nucleus.head._2)
  }

  //result = Either[Map[Predicate, IFormula], Dag[(IAtom, HornClauses.Clause)
  // ]] =
  //{ // todo: disjunction of all the unit clauses
  // first find out which theories are relevant

  /**
   * Positive CUCs C ∨ p(t¯) or (p(t¯) :- ¬C) are in this context interpreted
   * as symbolic states, and represent sets of reachable program states:
   * p corresponds to a control state, t¯ is * the symbolic store, and C is
   * the negation of a path predicate.
   */
  /**
   * Symbolic execution maintains a set F of CUCs, which is initialized to
   * F = ∅.
   */
  //    val allPreds = iClauses.flatMap(_.predicates).map(pred => {
  //      val rs = relationSymbols(pred)
  //      for (f <- preds) {
  //        val intF = IExpression.subst(f, rs.argumentITerms.head.toList, 0)
  //        val (rawF, posF, negF) = rsPredsToInternal(intF)
  //      }
  //    })

  val unitClauseDB = new UnitClauseDB(relationSymbols.values.toSet)

  def solve(): Unit = {
    val allSymbols = normClauses.flatMap(_._1.allSymbols).distinct
    println(allSymbols)

    var continueSearch = true
    // start traversal
    var ind = 0
    while (continueSearch) {
      continueSearch = false
      ind += 1
      printInfo(ind + ".", false)
      getClausesForResolution match {
        case Some((nucleus, electrons)) => {
          val newElectron = hyperResolve(nucleus, electrons)
          printInfo("\t" + nucleus + "\n  +\n\t" + electrons.mkString("\n\t"))
          printInfo("  =\n\t" + newElectron)
          if (hasContradiction(newElectron)) { // false :- true
            printInfo("")
            printInfo("UNSAT")
            def printCEX(maybeParents: Option[(NormClause, Set[UnitClause])],
                         depth:        Int = 0): Unit = {
              maybeParents match {
                case Some(parents) =>
                  println(depth + ". " + parents._1)
                  val offset = depth.toString.length + 2
                  val prefix = " " * offset
                  println(prefix + parents._2.mkString("\n" + prefix))
                  parents._2.foreach(cuc => {
                    unitClauseDB.parentsOption(cuc) match {
                      case Some(parents) =>
                        printCEX(Some(parents._2), depth + 1)
                      case None => // nothing
                    }
                  })
                case None => // nothing
              }
            }
            println("-" * 80)
            println("Counterexample: ")
            printCEX(Some(nucleus, electrons.toSet))
            println("-" * 80)
            // todo: print CEX
          } else if (constraintIsFalse(newElectron)) {
            //printInfo("Constraint is false for derived unit clause!")
            printInfo("")
            // todo: assumes we will never generate CUCs that are empty
            handleFalseConstraint(nucleus, electrons)
            continueSearch = true
          } else if (checkForwardSubsumption(newElectron, unitClauseDB)) {
            printInfo("subsumed by existing unit clauses.")
            handleForwardSubsumption(nucleus, electrons)
            continueSearch = true
          } else {
            val backSubsumed =
              checkBackwardSubsumption(newElectron, unitClauseDB)
            if (backSubsumed nonEmpty) {
              printInfo(
                "subsumes " + backSubsumed.size + " existing unit clause(s)_...",
                false)
              handleBackwardSubsumption(backSubsumed)
            }
            if (unitClauseDB.add(newElectron, (nucleus, electrons.toSet))) {
              printInfo("\n  (Added to database.)\n")
              handleNewUnitClause(newElectron)
            } else {
              printInfo("\n  (Derived clause already exists in the database.)")
              handleForwardSubsumption(nucleus, electrons)
            }
            continueSearch = true
          }
        }
        case None => // nothing left to explore, the clauses
          // are SAT.
          println("\t(Search space exhausted.)\n")
          println("SAT")
        // update result variable
        case other =>
          throw new SymexException(
            "Cannot hyper-resolve clauses: " + other.toString)
      }
    }
  }

  // methods handling derivation of useless clauses (merge?)
  def handleForwardSubsumption(nucleus:   NormClause,
                               electrons: Seq[UnitClause]): Unit

  def handleBackwardSubsumption(subsumed: Set[UnitClause]): Unit

  def handleNewUnitClause(clause: UnitClause): Unit

  def handleFalseConstraint(nucleus:   NormClause,
                            electrons: Seq[UnitClause]): Unit

  // true if cuc = "FALSE :- c" and c is satisfiable, false otherwise.
  private def hasContradiction(cuc: UnitClause)(
      implicit prover:              SimpleAPI): Boolean = {
    cuc.rs.pred == HornClauses.FALSE &&
    prover.scope {
      prover.addAssertion(cuc.constraint)
      prover.??? match { // check if cuc constraint is satisfiable
        case ProverStatus.Valid | ProverStatus.Sat     => true
        case ProverStatus.Invalid | ProverStatus.Unsat => false
        case s => {
          Console.err.println(
            "Warning: Verification of constraint was not possible:"
          )
          Console.err.println(cuc)
          Console.err.println("Checker said: " + s)
          true
        }
      }
    }
  }

  private def constraintIsFalse(cuc: UnitClause)(
      implicit prover:               SimpleAPI): Boolean = {
    prover.scope {
      // todo: globally keep track of which constants we are using (use
      //  symbolfactory)
      prover.addAssertion(cuc.constraint)
      val result = prover.??? match { // check if cuc constraint is satisfiable
        case ProverStatus.Valid | ProverStatus.Sat     => false // ok
        case ProverStatus.Invalid | ProverStatus.Unsat => true
        case s => {
          Console.err.println(
            "Warning: Verification of constraint was not possible:"
          )
          Console.err.println(cuc)
          Console.err.println("Checker said: " + s)
          false
        }
      }
      result
    }
  }
}

// todo: ctor order is different with traits, syntax for ordering ctors
