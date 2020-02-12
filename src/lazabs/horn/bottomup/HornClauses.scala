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

import ap.PresburgerTools
import ap.parser._
import ap.theories.{Theory, TheoryCollector, TheoryRegistry}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.TermOrder
import ap.Signature
import ap.parameters.PreprocessingSettings
import HornPredAbs.predArgumentSorts

import scala.collection.mutable.{HashMap => MHashMap}

object HornClauses {

  import IExpression._

  // Predicate to encode the head symbol "false" (to avoid case distinctions
  // everywhere later)
  val FALSE = new Predicate ("FALSE", 0)
  
  def allPredicates(clauses : Iterable[Clause]) : Set[Predicate] =
    (for (clause <- clauses.iterator;
          p <- clause.predicates.iterator) yield p).toSet - HornClauses.FALSE

  def allTermsSimple(terms : Iterable[ITerm]) : Boolean =
    terms forall {
      case SimpleTerm(_) => true
      case _             => false
    }

  case class Clause(head : IAtom, body : List[IAtom], constraint : IFormula) {
    lazy val constants =
      SymbolCollector constants (and(body) & constraint & head)
    
    private lazy val headCanDirectlyBeInlined =
      (head.args forall (_.isInstanceOf[IConstant])) &&
      (head.args.toSet.size == head.args.size)

    private lazy val localConstants =
      (constants -- (for (IConstant(c) <- head.args.iterator) yield c)
       ).toSeq.sortWith(_.name < _.name)

    lazy val allAtoms = head :: body

    lazy val bodyPredicates =
      (for (IAtom(p, _) <- body.iterator) yield p).toSet
    lazy val predicates =
      (for (IAtom(p, _) <- (Iterator single head) ++ body.iterator) yield p).toSet

    lazy val theories : Seq[Theory] = {
      val coll = new TheoryCollector
      coll(head)
      for (a <- body)
        coll(a)
      coll(constraint)
      coll.theories
    }

    def hasUnsatConstraint : Boolean = constraint.isFalse

    /**
     * Inline the given head arguments, and return the resulting set of body
     * literals, and the new constraint.
     */
    def inline(args : Seq[ITerm]) : (Seq[IAtom], IFormula) =
      if (headCanDirectlyBeInlined && allTermsSimple(args)) {
        val replacement =
          new MHashMap[ConstantTerm, ITerm]
        for (c <- localConstants)
          replacement.put(c, i(c.clone))

        val it1 = head.args.iterator
        val it2 = args.iterator
        while (it1.hasNext)
          replacement.put(it1.next.asInstanceOf[IConstant].c, it2.next)

        (for (a <- body) yield SimplifyingConstantSubstVisitor(a, replacement)
                                      .asInstanceOf[IAtom],
         SimplifyingConstantSubstVisitor(constraint, replacement))
      } else {
        val (Clause(IAtom(_, defHeadArgs), newBody, newConstraint), _) = refresh
        (newBody, newConstraint & (args === defHeadArgs))
      }

    /**
     * Given clauses p(...) :- q(...) (this) and q(...) :- body,
     * generate a clause p(...) :- body by inlining.
     */
    def mergeWith(that : Clause) : Clause = {
      assert(body.size == 1)
      val Clause(IAtom(thatHeadPred, thatHeadArgs),
                 thatBody, thatConstraint) = that
      val List(IAtom(thisBodyPred, thisBodyArgs)) = body
      assert(thisBodyPred == thatHeadPred)

      if ((thisBodyArgs forall (_.isInstanceOf[IConstant])) &&
          (thisBodyArgs.toSet.size == thisBodyArgs.size) &&
          allTermsSimple(thatHeadArgs)) {
        // can directly inline

        val replacement =
          new MHashMap[ConstantTerm, ITerm]
        val definedConsts =
          (for (IConstant(c) <- thisBodyArgs.iterator) yield c).toSet
        for (c <- constants)
          if (!(definedConsts contains c))
            replacement.put(c, i(c.clone))

        for ((IConstant(c), t) <-
               thisBodyArgs.iterator zip thatHeadArgs.iterator)
          replacement.put(c, t)

        Clause(SimplifyingConstantSubstVisitor(head, replacement)
                  .asInstanceOf[IAtom],
               thatBody,
               SimplifyingConstantSubstVisitor(constraint, replacement) &&&
                  thatConstraint)
      } else {
        val (Clause(newHead, List(IAtom(_, newBodyArgs)), newConstraint), _) =
          refresh
        Clause(newHead, thatBody,
               newConstraint &&&
               thatConstraint &&&
               (newBodyArgs === thatHeadArgs))
      }
    }

    def refresh : (Clause, Seq[ConstantTerm]) = {
      val consts =
        constants.toSeq.sortWith(_.name < _.name)
      val newConsts =
        for (c <- consts) yield c.clone
      val replacement =
        (consts.iterator zip newConsts.iterator).toMap

      (Clause(ConstantSubstVisitor.rename(head, replacement)
                 .asInstanceOf[IAtom],
              for (a <- body)
                 yield ConstantSubstVisitor.rename(a, replacement)
                         .asInstanceOf[IAtom],
              ConstantSubstVisitor.rename(constraint, replacement)),
       newConsts)
    }
    
    private def substitute(m : MHashMap[ConstantTerm, ITerm]) = {
      Clause(
          ConstantSubstVisitor(head, m).asInstanceOf[IAtom],
          for (a <- body) yield ConstantSubstVisitor(a, m).asInstanceOf[IAtom],
          ConstantSubstVisitor(constraint, m)
          )
    }
    // normalize the clause: replace every predicate P(terms) with P(vars) and add vars=terms to constraints
    def normalize() : Clause = {
      
      // refresh all variables
      val consts = constants.toSeq.sortWith(_.name < _.name)
      val replacement = new MHashMap[ConstantTerm, ITerm]
      val newLocalConsts = for (c <- consts) yield {
        val newC = c.clone
        replacement.put(c, i(newC))
        newC
      }
      
      val aux = this.substitute(replacement)
      var f : IFormula = aux.constraint
      
      var x = 1
      def normalizeAtom(a : IAtom) : IAtom = {
        IAtom(a.pred,
          for ((t, tSort) <- a.args zip predArgumentSorts(a.pred)) yield {
            t match {
              case IConstant(c) => IConstant(c)
              case _ => {
                val ic = i(tSort newConstant ("aux_"+x))
                x = x+1
                f = f &&& (ic === t)
                ic
              }
            }
          })
      }
      
      Clause(
          normalizeAtom(aux.head),
          for (a <- aux.body) yield normalizeAtom(a),
          f
          )
    }

    def toPrologString : String = ap.DialogUtil.asString {
      if (head.pred == FALSE)
        print("false")
      else
        PrincessLineariser printExpression head
      var sep = " :- "
      for (a <- body) {
        print(sep)
        PrincessLineariser printExpression a
        sep = ", "
      }
      if (constraint != i(true)) {
        print(sep)
        PrincessLineariser printExpression constraint
      }
      print(".")
    }

    def toFormula : IFormula = {
      import IExpression._

      val headFor : IFormula = head.pred match {
        case FALSE => false
        case _ => head
      }

      val matrix = (and(body) &&& constraint) ===> headFor
      quanConsts(Quantifier.ALL, constants.toSeq, matrix)
    }

    def toSMTString : String = SMTLineariser asString this.toFormula
  }

  class PrologApplier(constr : IFormula) {
    def :-(f : IFormula*) : Clause = {
      val bodyLits = LineariseVisitor(Transform2NNF(and(f) &&& constr),
                                      IBinJunctor.And)

      val (atoms, constraints) = bodyLits partition {
        case IAtom(p, _) => !TheoryRegistry.lookupSymbol(p).isDefined
        case INot(IAtom(p, _)) => !TheoryRegistry.lookupSymbol(p).isDefined
        case _ => false
      }

      val (negAtoms, posAtoms) = atoms partition (_.isInstanceOf[INot])

      Clause(negAtoms match {
               case Seq()                => FALSE()
               case Seq(INot(a : IAtom)) => a
             },
             (posAtoms map (_.asInstanceOf[IAtom])).toList,
             and(constraints))
    }
  }

  implicit def toPrologSyntax(f : IFormula) = new PrologApplier(!f)
  implicit def toPrologSyntax(b : Boolean)  = new PrologApplier(!b)

  //////////////////////////////////////////////////////////////////////////////

  def sLit(p : Predicate) = new Literal {
    val predicate = p
    val relevantArguments = 0 until p.arity
  }

  trait Literal {
    /**
     * Predicate representing this relation variable
     */
    val predicate : Predicate

    /**
     * Argument sorts of the predicate
     */
    lazy val argumentSorts : Seq[Sort] =
      predArgumentSorts(predicate)

    /**
     * (Ordered) list of arguments that are relevant for a clause,
     * i.e., the arguments that actually occur in the clause constraint.
     */
    val relevantArguments : Seq[Int]

    override def toString = predicate.toString
  }

  trait ConstraintClause {
    def head : Literal
    def body : Seq[Literal]
    def localVariableNum : Int
    def instantiateConstraint(headArguments : Seq[ConstantTerm],
                              bodyArguments: Seq[Seq[ConstantTerm]],
                              localVariables : Seq[ConstantTerm],
                              sig : Signature) : Conjunction
    def instantiateConstraint(headArguments : Seq[ConstantTerm],
                              bodyArguments: Seq[Seq[ConstantTerm]],
                              localVariables : Seq[ConstantTerm],
                              order : TermOrder) : Conjunction =
      instantiateConstraint(headArguments, bodyArguments, localVariables,
                            Signature(Set(), Set(), order.orderedConstants, order))
    def collectTheories(coll : TheoryCollector) : Unit = {}
    override def toString = head.toString + " :- " + body.mkString(", ")
  }

  //////////////////////////////////////////////////////////////////////////////

  trait IConstraintClause extends ConstraintClause {
    def instantiateConstraint(headArguments : Seq[ConstantTerm],
                              bodyArguments: Seq[Seq[ConstantTerm]],
                              localVariables : Seq[ConstantTerm],
                              sig : Signature) : Conjunction = {
      import IExpression._

      val f = iInstantiateConstraint(headArguments, bodyArguments, localVariables)
    
      // preprocessing: e.g., encode functions as predicates
      val (inputFormulas, _, signature2) =
        Preprocessing(!f,
                      List(),
                      sig,
                      PreprocessingSettings.DEFAULT)
      val order2 = signature2.order
      ReduceWithConjunction(Conjunction.TRUE, order2)(
        Conjunction.conj(
          for (f <- inputFormulas)
          yield Conjunction.negate(
                  InputAbsy2Internal(removePartName(f), order2),
                  order2),
          order2))
    }
    def iInstantiateConstraint(headArguments : Seq[ConstantTerm],
                               bodyArguments: Seq[Seq[ConstantTerm]],
                               localVariables : Seq[ConstantTerm]) : IFormula
  }
  
  //////////////////////////////////////////////////////////////////////////////

  implicit def eitherClause[CC1 <% ConstraintClause, CC2 <% ConstraintClause]
                           (c : Either[CC1, CC2]) : ConstraintClause = c match {
    case Left(c) => c
    case Right(c) => c
  }

  implicit def clause2ConstraintClause(c : Clause) : ConstraintClause = new ConstraintClause {
/*    private val (headSymbols, bodySymbols, localVariables, constraint) = {
      val coll = new TheoryCollector
      collectTheories(coll)

      val sf = new SymbolFactory(coll.theories)

      val headSymbols =
        sf.genConstants("head", c.head.pred.arity, "")
      val bodySymbols =
        for (a <- c.body) yield sf.genConstants("body", a.pred.arity, "")

      val headEqs =
        c.head.args === headSymbols
      val bodyEqs =
        and(for ((bArgs, bAtom) <- bodySymbols.iterator zip c.body.iterator)
            yield (bAtom.args === bArgs))

      val internal =
        sf.toInternal(quanConsts(Quantifier.EX, c.constants,
                                 c.constraint & headEqs & bodyEqs))

      // get rid of existential quantifiers
      val prenex = PresburgerTools toPrenex internal
      val EXnum =
        prenex.quans.size - prenex.quans.lastIndexOf(Quantifier.ALL) - 1

      val localVariables = sf.genConstants("local", EXnum, "")

      val constraint = prenex instantiate 

      (headSymbols, bodySymbols)
    } */

    def head : Literal = sLit(c.head.pred)
    def body : Seq[Literal] = for (a <- c.body) yield sLit(a.pred)
    def localVariableNum : Int = 0
    def instantiateConstraint(headArguments : Seq[ConstantTerm],
                              bodyArguments: Seq[Seq[ConstantTerm]],
                              localVariables : Seq[ConstantTerm],
                              sig : Signature) : Conjunction = {
      val headEqs =
        c.head.args === headArguments
      val bodyEqs =
        and(for ((bArgs, bAtom) <- bodyArguments.iterator zip c.body.iterator)
            yield (bAtom.args === bArgs))

      // TODO: check whether any quantifiers are left in the contraint, which could
      // be eliminated right away

      HornPredAbs.toInternal(quanConsts(Quantifier.EX, c.constants,
                                        c.constraint & headEqs & bodyEqs),
                             sig)
    }
    override def collectTheories(coll : TheoryCollector) : Unit = {
      coll(c.head)
      for (a <- c.body)
        coll(a)
      coll(c.constraint)
    }
  }

}
