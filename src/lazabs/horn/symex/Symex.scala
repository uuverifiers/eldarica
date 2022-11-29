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

import ap.api.SimpleAPI.ProverStatus
import ap.SimpleAPI
import ap.terfor.preds.Predicate
import ap.terfor.Term
import ap.terfor.conjunctions.Conjunction
import ap.theories.{Theory, TheoryCollector}
import lazabs.horn.bottomup.{HornClauses, NormClause, RelationSymbol}
import lazabs.horn.bottomup.HornClauses.ConstraintClause
import lazabs.horn.preprocessor.HornPreprocessor.CounterExample

object Symex {
  sealed trait Result
  case object Sat extends Result { // todo: can we construct a solution?
    override def toString: String = "SAT"
  }
  //case class Unsat(counterExample: CounterExample) extends Result
  case class Unsat(
      cex:        (NormClause, Set[UnitClause]),
      getParents: UnitClause => Option[(NormClause, Set[UnitClause])])
      extends Result {
    private def toStringHelper(
        maybeParents: Option[(NormClause, Set[UnitClause])],
        depth:        Int = 0): String = {
      maybeParents match {
        case Some(parents) =>
          val offset = depth.toString.length + 2
          val prefix = " " * offset
          "\n" + depth + ". " + parents._1 + "\n" +
            prefix + parents._2.mkString("\n" + prefix) ++
            parents._2
              .map(cuc => toStringHelper(getParents(cuc), depth + 1))
              .mkString("\n" + depth)
        case None => ""
      }
    }
    override def toString: String = {
      "UNSAT\nCounterexample\n" + "-" * 80 +
        toStringHelper(Some(cex)) + "\n" + "-" * 80
    }
  }

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
          "Trying to create a unit clause from a non-unit clause: " + normClause)
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
  implicit val prover: SimpleAPI = SimpleAPI.spawn
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
      lazabs.GlobalParameters.get.timeoutChecker()
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

  /**
   * Returns optionally a nucleus and electrons that can be hyper-resolved into
   * another electron. The sequence indices i of returned electrons correspond
   * to atoms at nucleus.body(i). Returns None if the search space is exhausted.
   */
  def getClausesForResolution: Option[(NormClause, Seq[UnitClause])]

  /**
   * Applies hyper-resolution using nucleus and electrons and returns the
   * resulting unit clause.
   * @note This implementation only infers positive CUCs.
   * @note "FALSE :- constraint" is considered a unit clause.
   * @todo Move out of this class.
   */
  private def hyperResolve(nucleus:   NormClause,
                           electrons: Seq[UnitClause]): UnitClause = {

    assert(electrons.length == nucleus.body.length)

    val constraintFromElectrons =
      for (((rp, occ), ind) <- nucleus.body.zipWithIndex) yield {
        assert(rp == electrons(ind).rs) // todo:
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

    val simplifiedConstraint =
      simplifyConstraint(unsimplifiedConstraint,
                         localSymbols,
                         reduceBeforeSimplification = true)

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

  //    val allPreds = iClauses.flatMap(_.predicates).map(pred => {
  //      val rs = relationSymbols(pred)
  //      for (f <- preds) {
  //        val intF = IExpression.subst(f, rs.argumentITerms.head.toList, 0)
  //        val (rawF, posF, negF) = rsPredsToInternal(intF)
  //      }
  //    })

  val unitClauseDB = new UnitClauseDB(relationSymbols.values.toSet)

  def solve(): Result = {
    var result: Result = null
    // start traversal
    var ind = 0
    while (result == null) {
      ind += 1
      printInfo(ind + ".", false)
      getClausesForResolution match {
        case Some((nucleus, electrons)) => {
          val newElectron = hyperResolve(nucleus, electrons)
          printInfo("\t" + nucleus + "\n  +\n\t" + electrons.mkString("\n\t"))
          printInfo("  =\n\t" + newElectron)
          if (hasContradiction(newElectron)) { // false :- true
            result =
              Unsat((nucleus, electrons.toSet), unitClauseDB.parentsOption)
          } else if (constraintIsFalse(newElectron)) {
            printInfo("")
            // todo: assumes we will never generate CUCs that are empty
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
          }
        }
        case None => // nothing left to explore, the clauses
          // are SAT.
          printInfo("\t(Search space exhausted.)\n")
          result = Sat
        // update result variable
        case other =>
          throw new SymexException(
            "Cannot hyper-resolve clauses: " + other.toString)
      }
    }
    result
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
