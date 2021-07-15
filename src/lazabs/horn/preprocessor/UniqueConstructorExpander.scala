/**
 * Copyright (c) 2020-2021 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.bottomup.HornClauses
import HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.abstractions.VerificationHints

import ap.basetypes.IdealInt
import ap.parser._
import IExpression.{Predicate, Sort, and}
import ap.theories.ADT
import ap.types.MonoSortedPredicate

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer,
                                 LinkedHashMap}
import scala.collection.{Map => GMap}

object UniqueConstructorExpander {

  import AbstractAnalyser._
  import IExpression._
  import HornPreprocessor._
  import Sort.:::

  /**
   * Abstract domain to infer the constructor type of ADT arguments.
   */
  object CtorTypeDomain extends AbstractDomain {
    val name = "constructor type"

    // For each argument, store the index of the unique constructor that
    // was identified
    type Element = Option[Seq[Option[Int]]]

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

    object InconsistencyException extends Exception

    def transformerFor(clause : Clause) = new AbstractTransformer[Element] {
      val Clause(head, body, constraint) = clause
      val headSorts = predArgumentSorts(head.pred)
      val bodySorts = for (b <- body) yield predArgumentSorts(b.pred)

      val adtConsts =
        for (c <- clause.constants;
             sort = Sort sortOf c;
             if sort.isInstanceOf[ADT.ADTProxySort])
        yield c

      // we only use equations for propagation
      val literals =
        for (f <- LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And);
             if (f match {
                   case Eq(_, _) => true
                   case _        => false
                 }))
        yield f

      val initialValueMap =
        (for (c <- adtConsts.iterator;
              adtSort = (Sort sortOf c).asInstanceOf[ADT.ADTProxySort];
              ctorIds = adtSort.adtTheory.ctorIdsPerSort(adtSort.sortNum);
              if ctorIds.size == 1)
         yield (c, ctorIds.head)).toIndexedSeq

      /**
       * The abstract values used for constraint propagation map constants
       * to a constructor index of the corresponding ADT.
       */
      private val constValueMap = new MHashMap[ConstantTerm, Int]
      private var changed = false

      def addConstValue(c : ConstantTerm, adt : ADT, ctorIndex : Int) : Unit =
        if (adtConsts contains c) {
          (Sort sortOf c) match {
            case adt.SortNum(num) if num == adt.sortOfCtor(ctorIndex) =>
              // ok
            case s =>
              return // inconsistent sorts, we ignore this constraint
          }

          (constValueMap get c) match {
            case None => {
              constValueMap.put(c, ctorIndex)
              changed = true
            }
            case Some(oldIndex) =>
              if (ctorIndex != oldIndex)
                throw InconsistencyException
          }
        }

      def transform(bodyVals : Seq[Element]) : Element =
        if (bodyVals exists (_.isEmpty)) {
          None
        } else try {
          constValueMap.clear
          constValueMap ++= initialValueMap

          for (((IAtom(pred, args), cArgs), sorts) <-
                 body.iterator zip bodyVals.iterator zip bodySorts.iterator;
               ((IConstant(c), Some(ind)), s : ADT.ADTProxySort) <-
                 args.iterator zip cArgs.get.iterator zip sorts.iterator)
            addConstValue(c, s.adtTheory, ind)

          changed = true
          while (changed) {
            changed = false

            for (lit <- literals)
              lit match {
                case Eq(IFunApp(ADT.Constructor(adt, ind), _),
                        IConstant(c)) =>
                  addConstValue(c, adt, ind)
                case Eq(IFunApp(ADT.CtorId(adt, sortInd), Seq(IConstant(c))),
                        Const(IdealInt(perSortId))) =>
                  addConstValue(c, adt, adt.ctorIdsPerSort(sortInd)(perSortId))
                case Eq(IConstant(c) ::: (cs : ADT.ADTProxySort),
                        IConstant(d) ::: (ds : ADT.ADTProxySort)) if cs == ds => {
                  for (ind <- constValueMap get c)
                    addConstValue(d, cs.adtTheory, ind)
                  for (ind <- constValueMap get d)
                    addConstValue(c, cs.adtTheory, ind)
                }
                case lit =>
//                  println("cannot handle: " + lit)
              }
          }

          val headVals =
            for ((t, s) <- head.args zip headSorts) yield t match {
              case IConstant(c) ::: cs if s == cs => constValueMap get c
              case _                              => None
            }
          Some(headVals)
        } catch {
          case InconsistencyException => None
        }
        
    }
  }
}

/**
 * Preprocessor that adds expands ADT arguments when their constructor
 * type is fixed.
 */
class UniqueConstructorExpander extends ArgumentExpander {

  import IExpression._
  import HornPreprocessor._
  import UniqueConstructorExpander._

  val name = "inlining ADT constructors"

  override def process(clauses : Clauses, hints : VerificationHints)
                    : (Clauses, VerificationHints, BackTranslator) = {
    ctorElements = (new AbstractAnalyser(clauses, CtorTypeDomain)).result
    super.process(clauses, hints)
  }

  private var ctorElements : GMap[Predicate, CtorTypeDomain.Element] = _

  def expand(pred : Predicate, argNum : Int, sort : Sort)
           : Option[(Seq[(ITerm, Sort, String)], Option[ITerm])] =
    for (value     <- ctorElements get pred;
         someValue <- value;
         ctorIndex <- someValue(argNum)) yield {
      val adt  = sort.asInstanceOf[ADT.ADTProxySort].adtTheory
      val ctor = adt constructors ctorIndex
      val sels = adt selectors ctorIndex
      (for (f <- sels) yield (f(v(0)), f.resSort, f.name),
       Some(ctor((for (n <- 0 until sels.size) yield v(n)) : _*)))
    }

  def isExpandableSort(s : Sort) : Boolean = s.isInstanceOf[ADT.ADTProxySort]

}
