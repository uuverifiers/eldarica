/**
 * Copyright (c) 2018-2019 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.preprocessor

import ap.parser._
import ap.basetypes.IdealInt

import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.Util.{UnionFind, IntUnionFind}

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 LinkedHashSet, ArrayBuffer, LinkedHashMap}

object AbstractAnalyser {
  import HornClauses.Clause
  import SymbolSplitter.ClausePropagator
  import IExpression.{Predicate, ConstantTerm}

  /**
   * Abstract domains used during propagation
   */
  trait AbstractDomain {
    val name : String

    /** The type of abstract elements in this domain */
    type Element

    /** The abstract bottom element */
    def bottom(p : Predicate) : Element
    
    /** Compute the join (union) of two abstract elements */
    def join(a : Element, b : Element) : Element

    /** Test whether an abstract element is bottom */
    def isBottom(b : Element) : Boolean

    /** Create an abstract transformer for the given clause */
    def transformerFor(clause : Clause) : AbstractTransformer[Element]

    /** Inline the abstract value of a clause body literal by possibly
     *  modifying the literal, and adding a further constraint to the clause */
    def inline(a : IAtom, value : Element) : (IAtom, IFormula)

    /** Augment a solution constraint by the information expressed in an
     *  abstract value */
    def augmentSolution(sol : IFormula, value : Element) : IFormula
  }

  /**
   * Transformer that computes the abstract value of a clause head given
   * the abstract values for the body literals.
   */
  trait AbstractTransformer[Element] {
    def transform(bodyValues : Seq[Element]) : Element
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Abstract domain for constant propagation
   */
  class ConstantPropDomain extends AbstractDomain {
    type Element = Option[Seq[Option[ITerm]]]

    val name = "constant"

    def bottom(p : Predicate) : Element = None

    def isBottom(b : Element) : Boolean = b.isEmpty

    def join(a : Element, b : Element) : Element =
      a match {
        case None => b
        case Some(aArgs) => b match {
          case None => a
          case Some(bArgs) =>
            Some(for (p <- aArgs zip bArgs) yield p match {
                   case (s@Some(x), Some(y)) if x == y => s
                   case _                              => None
                 })
        }
      }

    def transformerFor(clause : Clause) = new AbstractTransformer[Element] {
      private val prop = new ClausePropagator(clause)
      private val Clause(head, body, _) = clause

      def transform(bodyVals : Seq[Element]) : Element =
        if (bodyVals exists (_.isEmpty)) {
          None
        } else {
          try {
            for ((IAtom(_, args), cArgs) <-
                   body.iterator zip bodyVals.iterator;
                 (IConstant(c), Some(t)) <-
                   args.iterator zip cArgs.get.iterator)
              prop.assign(c, t)

            prop.propagate

            Some(prop constantArgs head)
          } catch {
            case ClausePropagator.InconsistentAssignment =>
              None
          } finally {
            prop.reset
          }
        }
    }

    import IExpression._

    private var symCounter = 0

    def inline(a : IAtom, value : Element) : (IAtom, IFormula) =
      value match {
        case None =>
          // this clause can be deleted, it is not reachable
          (a, false)
        case Some(cArgs) => {
          val IAtom(p, args) = a
          var newConstraint = i(true)

          val newArgs =
            (for (((a, ca), n) <-
                    (args.iterator zip cArgs.iterator).zipWithIndex)
             yield ca match {
               case None => a
               case Some(t) => {
                 newConstraint = newConstraint &&& (a === t)
                 // in this case we can replace the old argument with a fresh
                 // constant, its value is determined anyway
                 val name = p.name + "_anon_" + symCounter
                 symCounter = symCounter + 1
                 IConstant(new ConstantTerm (name))
               }
             }).toVector

          (IAtom(p, newArgs), newConstraint)
        }
      }
    
    def augmentSolution(sol : IFormula, value : Element) : IFormula =
      value match {
        case None =>
          sol
        case Some(constantArgs) => {
          val subst =
            (for ((arg, ind) <- constantArgs.iterator.zipWithIndex)
             yield (arg getOrElse v(ind))).toList
          val simpSol = SimplifyingVariableSubstVisitor(sol, (subst, 0))

          and(for ((Some(t), ind) <- constantArgs.iterator.zipWithIndex)
              yield SymbolSplitter.solutionEquation(ind, t)) &&&
          simpSol
        }
      }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Abstract domain for constant propagation
   */
  class EqualityPropDomain extends AbstractDomain {
    type Element = Option[Partitioning]

    val name = "equality"

    /**
     * Class to represent a partitioning of the arguments of a predicate.
     */
    class Partitioning(val arity : Int) {
      val eqvClass = new IntUnionFind (arity)

      override def toString =
        (for ((_, els) <- allClasses)
         yield "{" + (els mkString ", ") + "}") mkString ", "

      def apply(n : Int) = eqvClass(n)

      lazy val allClasses = {
        val res = new LinkedHashMap[Int, ArrayBuffer[Int]]
        for (n <- 0 until arity)
          res.getOrElseUpdate(this(n), new ArrayBuffer[Int]) += n
        res
      }

      def <=(that : Partitioning) : Boolean =
        (0 until arity) forall {
          n => this(n) == this(that(n))
        }

      /**
       * Compute the partitioning consisting of all intersections of
       * classes from <code>this</code> and <code>that</code>
       */
      def intersections(that : Partitioning) : Partitioning = {
        assert(this.arity == that.arity)
        
        if (this <= that) {
          that
        } else if (that <= this) {
          this
        } else {
          val res = new Partitioning(arity)
          val sinks = Array.fill[Int](arity)(-1)

          for ((_, els) <- that.allClasses)
            if (els.size > 1) {
              for (el <- els) {
                val parent = this(el)
                sinks(parent) match {
                  case -1 =>
                    sinks(parent) = el
                  case sink =>
                    res.eqvClass.union(el, sink)
                }
              }
              for (el <- els)
                sinks(this(el)) = -1
            }
          
          res
        }
      }

      override def equals(that : Any) = that match {
        case that : Partitioning =>
          (this eq that) ||
          (this.arity == that.arity && this <= that && that <= this)
        case _ =>
          false
      }

      override def hashCode =
        throw new UnsupportedOperationException
    }

    def bottom(p : Predicate) : Element = None

    def isBottom(b : Element) : Boolean = b.isEmpty

    def join(a : Element, b : Element) : Element =
      a match {
        case None => b
        case Some(aPartitioning) => b match {
          case None => a
          case Some(bPartitioning) =>
            Some(aPartitioning intersections bPartitioning)
        }
      }
        
    def transformerFor(clause : Clause) = new AbstractTransformer[Element] {
      val Clause(head, body, constraint) = clause
      val constantClasses = new UnionFind[ConstantTerm]

      for (c <- clause.constants)
        constantClasses makeSet c

      // we only use equations between constants for propagation
      for (f <- LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And))
        f match {
          case IExpression.Eq(IConstant(c), IConstant(d)) =>
            constantClasses.union(c, d)
          case _ =>
            // nothing
        }

      def transform(bodyVals : Seq[Element]) : Element =
        if (bodyVals exists (_.isEmpty)) {
          None
        } else {
          val localClasses = constantClasses.clone

          for ((IAtom(_, args), Some(partitioning)) <-
                 body.iterator zip bodyVals.iterator;
               (IConstant(c), n) <-
                 args.iterator.zipWithIndex)
            partitioning(n) match {
              case `n`    => // trivial equation
              case parent => args(parent) match {
                case IConstant(d) =>
                  localClasses.union(c, d)
                case _ =>
                  // the argument corresponding to the parent node is not a
                  // constant, so we cannot use it to create an equation.
                  // Search for another element in the equivalence class that
                  // is a constant
                  for (d <-
                       (for (n <- partitioning.allClasses(parent).iterator)
                        yield args(n)) collectFirst { case IConstant(d) => d })
                    localClasses.union(c, d)
              }
            }

          val headPartitioning = new Partitioning (head.pred.arity)

          val sinks = new MHashMap[ConstantTerm, Int]
          for ((IConstant(c), n) <- head.args.iterator.zipWithIndex) {
            val constSink = localClasses(c)
            (sinks get constSink) match {
              case None =>
                sinks.put(constSink, n)
              case Some(ind) =>
                headPartitioning.eqvClass.union(ind, n)
            }
          }

          Some(headPartitioning)
        }
    }

    import IExpression._

    private var symCounter = 0

    def inline(a : IAtom, value : Element) : (IAtom, IFormula) =
      value match {
        case None =>
          // this clause can be deleted, it is not reachable
          (a, false)
        case Some(partitioning) => {
          val IAtom(p, args) = a

          // map equivalent arguments to the left-most argument of the
          // equivalence class; anonymise all other arguments
          val redundantArgs =
            (for ((_, cl) <- partitioning.allClasses.iterator;
                  if cl.size > 1;
                  sortedCL = cl.toVector.sorted;
                  n <- sortedCL.tail.iterator)
             yield n).toSet

          val newArgs =
            (for ((arg, n) <- args.iterator.zipWithIndex) yield {
               if (redundantArgs contains n) {
                 val name = p.name + "_anon_" + symCounter
                 symCounter = symCounter + 1
                 IConstant(new ConstantTerm (name))
               } else {
                 arg
               }
             }).toVector

          val newConstraint = and(
            for ((arg, n) <- args.iterator.zipWithIndex;
                 parent = partitioning(n);
                 if parent != n)
            yield (arg === args(parent)))

          (IAtom(p, newArgs), newConstraint)
        }
      }

    def augmentSolution(sol : IFormula, value : Element) : IFormula =
      value match {
        case None =>
          sol
        case Some(partitioning) => {
          val subst =
            (for (ind <- 0 until partitioning.arity)
             yield v(partitioning(ind))).toList
          val simpSol = SimplifyingVariableSubstVisitor(sol, (subst, 0))

          and(
            for (ind <- (0 until partitioning.arity).iterator;
                 parent = partitioning(ind);
                 if parent != ind)
            yield (v(ind) === v(parent))) &&&
          simpSol
        }
      }

  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Abstract analyser instantiated to perform constant propagation.
   */
  def ConstantPropagator = new AbstractAnalyser(new ConstantPropDomain)

  /**
   * Abstract analyser instantiated to perform equality propagation.
   */
  def EqualityPropagator = new AbstractAnalyser(new EqualityPropDomain)

}

////////////////////////////////////////////////////////////////////////////////

/**
 * A simple fixed-point loop using some abstract domain.
 */
class AbstractAnalyser(domain : AbstractAnalyser.AbstractDomain)
      extends HornPreprocessor {
  import HornPreprocessor._
  import HornClauses.Clause
  import IExpression.{Predicate, ConstantTerm}

  val name : String = domain.name + " propagation"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val allPreds = HornClauses allPredicates clauses
    
    val clauseSeq = clauses.toVector
    val clausesWithBodyPred =
      (for ((clause, n) <- clauseSeq.zipWithIndex;
            if clause.head.pred != HornClauses.FALSE;
            IAtom(p, _) <- clause.body)
       yield (p, n)) groupBy (_._1)

    val propagators =
      for (clause <- clauseSeq) yield (domain transformerFor clause)

    val abstractValues = new MHashMap[Predicate, domain.Element]
    for (p <- allPreds)
      abstractValues.put(p, domain bottom p)

    val clausesTodo = new LinkedHashSet[Int]

    // start with the clauses with empty body
    for ((Clause(IAtom(p, _), Seq(), _), n) <- clauseSeq.iterator.zipWithIndex;
         if p != HornClauses.FALSE)
      clausesTodo += n
      
    while (!clausesTodo.isEmpty) {
      val nextID = clausesTodo.head
      clausesTodo -= nextID
      val Clause(head, body, _) = clauseSeq(nextID)

      val bodyValues =
        for (IAtom(p, _) <- body) yield abstractValues(p)
      val newAbstractEl =
        propagators(nextID) transform bodyValues

      if (!(domain isBottom newAbstractEl)) {
        val headPred = head.pred
        val oldAbstractEl = abstractValues(headPred)
        val jointEl = domain.join(oldAbstractEl, newAbstractEl)

        if (jointEl != oldAbstractEl) {
          abstractValues.put(headPred, jointEl)
          for ((_, n) <- clausesWithBodyPred.getOrElse(headPred, List()))
            clausesTodo += n
        }
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    val clauseBackMapping = new MHashMap[Clause, Clause]

    var changed = false

    val newClauses =
      for (clause <- clauses) yield {
        val Clause(head, body, constraint) = clause
        var newConstraint = constraint

        var clauseChanged = false

        val newBody =
          for (a <- body) yield {
            val aValue = abstractValues(a.pred)
            val (newA, constr) = domain.inline(a, aValue)
            newConstraint = newConstraint &&& constr
            if (!(newA eq a))
              clauseChanged = true
            newA
          }

        if (!(newConstraint eq constraint))
          clauseChanged = true

        val newClause =
          if (clauseChanged) {
            changed = true
            Clause(head, newBody, newConstraint)
          } else {
            clause
          }
          
        clauseBackMapping.put(newClause, clause)
        newClause
      }

    ////////////////////////////////////////////////////////////////////////////

    val translator =
      if (changed) {
        new BackTranslator {
          import IExpression._

          def translate(solution : Solution) =
            solution transform {
              case (pred, sol) =>
                domain.augmentSolution(sol, abstractValues(pred))
            }
          
          def translate(cex : CounterExample) =
            for (p <- cex) yield (p._1, clauseBackMapping(p._2))
        }
      } else {
        IDENTITY_TRANSLATOR
      }

    (newClauses, hints, translator)
  }

}
