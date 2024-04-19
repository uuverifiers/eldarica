/**
 * Copyright (c) 2018-2022 Philipp Ruemmer. All rights reserved.
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

import ap.parser.IExpression.Predicate
import ap.parser._
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.preprocessor.AbstractAnalyserMk2.AbstractTransformerMk2
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

import scala.collection.mutable.{LinkedHashSet, HashMap => MHashMap}
import scala.collection.{Map => GMap}

object AbstractAnalyserMk2 {

  /**
   * Abstract domains used during propagation
   */
  trait AbstractDomainMk2 {
    val name : String

    /** The type of abstract elements in this domain */
    type Element

    /** The local element type over clause terms */
    type LocalElement

    /** The abstract bottom element */
    def bottom(p : Predicate) : Element

    /** Compute the join (union) of two abstract elements */
    def join(a : Element, b : Element) : Element

    /** Test whether an abstract element is bottom */
    def isBottom(b : Element) : Boolean

    /** Create an abstract transformer for the given clause */
    def transformerFor(clause : Clause) : AbstractTransformerMk2[Element,
                                                                 LocalElement]
  }

  /**
   * Transformer that computes the abstract value of a clause head given
   * the abstract values for the body literals.
   */
  abstract class AbstractTransformerMk2[Element, LocalElement](clause : Clause) {

    /** Compute the meet of two local elements */
    protected def meet(a : LocalElement, b : LocalElement) : LocalElement

    /** The abstract top local element */
    protected val topLocalElement : LocalElement

    /** The abstract bottom local element */
    protected val botLocalElement : LocalElement

    /** Method to convert an element into a local element */
    protected def localElementForAtom(e : Element, a : IAtom) : LocalElement

    /** Method to convert a local element into an element for an atom */
    protected def elementForAtom(e : LocalElement, a : IAtom) : Element

    /** The return type of the optional pre-analysis */
    type PreAnalysisResult

    /** Method to perform pre-analysis with a custom return type */
    def preAnalysisFun(conjuncts : Seq[IFormula]) : PreAnalysisResult

    /**
     * Constraing propagator function. Should return `None` for early return
     * if the result is the bottom element.
     */
    protected def constraintPropagator(
      conjunct : IFormula, element : LocalElement,
      preAnalysisResult: PreAnalysisResult) : Option[LocalElement]

    @scala.annotation.tailrec
    private def fixedPointLoop(element           : LocalElement,
                               conjuncts         : Seq[IFormula],
                               preAnalysisResult : PreAnalysisResult)
    : Option[LocalElement] = {
      conjuncts.foldLeft(Option(element)){(maybeElement, conjunct) =>
        maybeElement.flatMap(
          element => constraintPropagator(conjunct, element, preAnalysisResult))
      } match {
        case Some(updatedElement) if updatedElement != element =>
          fixedPointLoop(updatedElement, conjuncts, preAnalysisResult)
        case fixedPoint =>
          fixedPoint
      }
    }

    private def propagate(initElement : LocalElement,
                          constraint  : IFormula) : Option[LocalElement] = {
      val conjuncts =
        LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)
      val preAnalysisResult = preAnalysisFun(conjuncts)
      fixedPointLoop(initElement, conjuncts, preAnalysisResult)
    }

    def transform(bodyValues    : Seq[Element],
                  bottomElement : Element) : (Element, Option[LocalElement]) = {

      /** Compute the initial local element by constraining top local element
        * with the values coming from the clause body.
       * Will return None if any element becomes botLocalElement.
        */
      val initialLocalElement : Option[LocalElement] = {
        (clause.body zip bodyValues).foldLeft(Option(topLocalElement)){
          (accOpt, bodyAtomElem) =>
            accOpt.flatMap{accElem =>
              val (bodyAtom, bodyElement) = bodyAtomElem
              meet(accElem, localElementForAtom(bodyElement, bodyAtom)) match {
                case e if e == botLocalElement => None
                case e => Some(e)
              }
            }
        }
      }

      /** Early return if initialLocalElement is bottom */
      if (initialLocalElement isEmpty) return (bottomElement, None)

      /** Run the pre-analysis first */


      /** Start the constraint propagation loop */
      propagate(initialLocalElement.get, clause.constraint) match {
        case Some(e) if clause.head.pred == HornClauses.FALSE =>
          (bottomElement, Some(e))
        case Some(e) =>
          (elementForAtom(e, clause.head), Some(e))
        case None => (bottomElement, None)
      }
    }
  }
}

class AbstractAnalyserMk2[Domain <: AbstractAnalyserMk2.AbstractDomainMk2]
                      (clauses : Clauses, val domain : Domain,
                       frozenPredicates : Set[Predicate]) {

  val (predToElement   : GMap[Predicate, domain.Element],
       clauseToElement : GMap[Clause, Option[domain.LocalElement]]) = {
    val allPreds = HornClauses allPredicates clauses

    val clauseSeq = clauses.toVector
    val clausesWithBodyPred =
      (for ((clause, n) <- clauseSeq.zipWithIndex;
            IAtom(p, _) <- clause.body)
       yield (p, n)) groupBy (_._1)

    val propagators = clauseSeq map domain.transformerFor

    val predAbstractValues = new MHashMap[Predicate, domain.Element]
    val clauseAbstractValues = new MHashMap[Clause, Option[domain.LocalElement]]

    for (p <- allPreds)
      if (frozenPredicates contains p) {
        // set the frozen predicates to the top value
        val sorts = predArgumentSorts(p)
        val args  = for (s <- sorts) yield s.newConstant("X")
        val head  = IAtom(p, args)
        val prop  = domain transformerFor Clause(head, List(), true)
        val (elementForPred, _) =
          prop transform(List(), domain.bottom(head.pred))
        predAbstractValues.put(p, elementForPred)
      } else {
        // everything else to bottom
        predAbstractValues.put(p, domain bottom p)
      }

    val clausesTodo = new LinkedHashSet[Int]

    // start with the clauses with empty body
//    for ((Clause(IAtom(p, _), body, _), n) <-
//           clauseSeq.iterator.zipWithIndex;
//         if body forall { case IAtom(q, _) => frozenPredicates contains q })
//      clausesTodo += n
    clauseSeq.indices.foreach(clausesTodo +=)
      
    while (clausesTodo nonEmpty) {
      val nextID = clausesTodo.head
      clausesTodo -= nextID
      val clause@Clause(head, body, _) = clauseSeq(nextID)

      val bodyValues =
        for (IAtom(p, _) <- body) yield predAbstractValues(p)
      val (newAbstractPredEl, newAbstractClauseEl) =
        propagators(nextID) transform(bodyValues, domain.bottom(head.pred))

      if (!(domain isBottom newAbstractPredEl)) {
        val headPred = head.pred
        val oldAbstractEl = predAbstractValues(headPred)
        val jointEl = domain.join(oldAbstractEl, newAbstractPredEl)

        if (jointEl != oldAbstractEl) {
          predAbstractValues.put(headPred, jointEl)
          for ((_, n) <- clausesWithBodyPred.getOrElse(headPred, List()))
            clausesTodo += n
        }
      }
      clauseAbstractValues put (clause, newAbstractClauseEl)
    }

    (predAbstractValues, clauseAbstractValues)
  }

}
