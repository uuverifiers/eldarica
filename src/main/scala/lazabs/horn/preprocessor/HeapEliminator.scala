/**
 * Copyright (c) 2023 Zafer Esen. All rights reserved.
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
import IExpression._
import ap.SimpleAPI
import ap.theories.{ADT, Heap, TheoryRegistry}
import ap.theories.ADT.{ADTProxySort, ADTSort, OtherSort}
import ap.types.{MonoSortedIFunction, MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.{Clause, allPredicates}
import lazabs.horn.Util.{DagEmpty, DagNode}

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

class HeapEliminator extends HornPreprocessor {
  import HornPreprocessor._

  override val name : String = "eliminating heaps"

  /**
   * Only applicable when the input CHCs contain heap theories.
   */
  override def isApplicable(clauses          : Clauses,
                            frozenPredicates : Set[Predicate]) : Boolean = {
    clauses.flatMap(c => c.theories).toSet.exists(_.isInstanceOf[Heap])
  }

  override def process(clauses : Clauses,
                       hints : VerificationHints,
                       frozenPredicates : Set[Predicate])
  : (Clauses, VerificationHints, HornPreprocessor.BackTranslator) = {

    val predBackMapping = new MHashMap[Predicate, Predicate]

    val heapTheories = clauses.flatMap(c => c.theories)
      .filter(theory => theory.isInstanceOf[Heap])
      .map(theory => theory.asInstanceOf[Heap])
      .toSet

    /**
     * First create new preds as needed, and create a map from old preds
     */

    val oldUnintPreds = clauses.flatMap(_.predicates)

    val heapToADT : Map[Heap, ADT] = heapTheories.map{ heap =>
      val heapBuiltinAdtCtorSignatures = heap.HeapADTSortId.values.toSeq
        .sortBy(_.id).flatMap(key => heap.heapADTDefinitions.get(key))

      val newAdtCtorSignatures = (heap.adtCtorSignatures ++
        heapBuiltinAdtCtorSignatures).map {
        case (sortName, signature) =>
          val newArguments = signature.arguments.map {
            case arg@(_, ADTSort(_)) => arg
            case (ctorName, OtherSort(sort)) =>
              val newSort =
                if (sort == heap.AddressSort || sort == heap.HeapSort)
                  Sort.Nat
                else sort
              (ctorName, OtherSort(newSort))
          }
          sortName -> ADT.CtorSignature(newArguments, signature.result)
      }
      heap -> new ADT(heap.heapADTs.sorts.map(_.name), newAdtCtorSignatures)
    }.toMap

    val oldToNewSortMap : Map[Sort, Sort] = heapToADT.flatMap{
      case (heap, adt) =>
        Map(heap.HeapSort -> Sort.Nat,
            heap.AddressSort -> Sort.Nat) ++
          (heap.heapADTs.sorts zip adt.sorts)
    }

    val oldToNewFunMap : Map[IFunction, IFunction] = heapToADT.flatMap{
      case (heap, adt) =>
        heap.heapADTs.functions.map(
          oldF => oldF -> adt.functions.find(_.name == oldF.name).get).toMap
    }

    for (oldPred <- oldUnintPreds) {
      val newPred = oldPred match {
        case sortedPred : MonoSortedPredicate =>
          val newSorts : Seq[Sort] =
            for (oldSort <- sortedPred.argSorts) yield
              oldToNewSortMap get oldSort match {
                case Some(newSort) => newSort
                case None => oldSort
              }
          if (newSorts.diff(sortedPred.argSorts) nonEmpty)
            new MonoSortedPredicate(oldPred.name, newSorts)
          else oldPred
        case _ => oldPred
      }
      predBackMapping += newPred -> oldPred
    }

    val oldPredToNewPred = Map() ++ predBackMapping.map(_.swap)

    val newClauses = for (clause <- clauses) yield {
      var curConstraint = clause.constraint

      var curAtoms = List(clause.head) ++ clause.body
      for (heap <- heapTheories) {
        val eliminator = new HeapEliminatorVisitor(heap)
        curConstraint = eliminator(curConstraint)
        curAtoms = curAtoms.map(eliminator.apply)
      }

      var curClause = Clause(curAtoms.head, curAtoms.tail, curConstraint)

      val heapToAdtRewriter = new ClauseRewriter(
        oldPredToNewPred, oldToNewSortMap, oldToNewFunMap, curClause)
      curClause = heapToAdtRewriter.rewriteClause

      curClause
    }

    val backMapping = (newClauses zip clauses).toMap

    val backTranslator = new BackTranslator {
      override def translate(solution : Solution) : Solution = solution
      override def translate(cex : CounterExample) : CounterExample =
        translateCEX(cex).collapseNodes

      private def translateCEX(dag : CounterExample) : CounterExample =
        dag match {
          case DagNode(p@(a, clause), children, next) =>
            val newNext     = translateCEX(next)
            backMapping get clause match {
              case Some(oldClause) =>
                DagNode((a, oldClause), children, newNext)
              case None =>
                DagNode(p, children, newNext)
            }
          case DagEmpty => DagEmpty
        }
    }
//    val c = newClauses.filter(c => c.theories.exists(_.isInstanceOf[Heap]))
//    c.foreach(c => println(c.toPrologString))
    // The following assertion does not necessarily hold here, there might be
    // heap-conjuncts remaining that will be eliminated by constraint simplifier,
    // and there might also be the HeapTuple ADT with a heap selector.
//    assert(newClauses.flatMap(_.theories).forall(t => !t.isInstanceOf[Heap]))
    (newClauses, hints, backTranslator)
  }

  class ClauseRewriter(oldToNewPredMap : Map[Predicate, Predicate],
                       oldToNewSortMap : Map[Sort, Sort],
                       oldToNewFunMap  : Map[IFunction, IFunction],
                       clause          : Clause)
    extends CollectingVisitor[Unit, IExpression] {

    assert(clause.predicates.forall(oldToNewPredMap contains))

    private val oldNewTermMap : Map[ConstantTerm, ConstantTerm] =
      clause.constantsSorted.map{
        case c : SortedConstantTerm if oldToNewSortMap contains c.sort =>
          c -> new SortedConstantTerm(c.name, oldToNewSortMap(c.sort))
        case c => c -> c
      }.toMap

    def rewriteClause : Clause = {
      val newConstraint = visit(clause.constraint, ()).asInstanceOf[IFormula]
      val newHead = visit(clause.head, ()).asInstanceOf[IAtom]
      val newBody = clause.body.map(a => visit(a, ()).asInstanceOf[IAtom])
      Clause(newHead, newBody, newConstraint)
    }

    override def postVisit(t      : IExpression, arg : Unit,
                           subres : Seq[IExpression]) : IExpression = {
      t match {
        /** Rewrite constants using the provided map */
        case IConstant(SortedConstantTerm(c, _)) =>
          assert(oldNewTermMap contains c)
          IConstant(oldNewTermMap(c))

        case ISortedVariable(i, sort) if oldToNewSortMap contains sort =>
          ISortedVariable(i, oldToNewSortMap(sort))

        /** Rewrite predicates using the provided map */
        case IAtom(pred, _) if oldToNewPredMap contains pred =>
          IAtom(oldToNewPredMap(pred), subres.map(_.asInstanceOf[ITerm]))

        /** Rewrite functions using the provided map */
        case IFunApp(f, _) if oldToNewFunMap contains f =>
          IFunApp(oldToNewFunMap(f), subres.map(_.asInstanceOf[ITerm]))

        case _ =>
          t update subres
      }
    }
  }

  class HeapEliminatorVisitor(heap : Heap)
    extends CollectingVisitor[Unit, IExpression] {
    val termMap = new MHashMap[ITerm, ITerm]

    def apply(f : IFormula) : IFormula = visit(f, ()).asInstanceOf[IFormula]
    def apply(f : IAtom) : IAtom = visit(f, ()).asInstanceOf[IAtom]

    override def postVisit(t      : IExpression,
                           arg    : Unit,
                           subres : Seq[IExpression]) : IExpression = t match {
      /** Constant substitutions */
      case oldTerm@IConstant(SortedConstantTerm(c, sort))
        if sort == heap.HeapSort || sort == heap.AddressSort =>
        oldToNewTerm(oldTerm, c)

      /** Variable substitutions */
      case ISortedVariable(i, sort)
        if sort == heap.HeapSort || sort == heap.AddressSort =>
        ISortedVariable(i, Sort.Nat)

      /** Function substitutions */

      /** counter(h) --> h */
      case IFunApp(f, _) if f == heap.counter =>
        subres.head

      /** Formula substitutions */

      /** emptyHeap = h --> h === 0 */
      case Eq(IFunApp(f, _), _) if f == heap.emptyHeap =>
        i(true) //subres(1).asInstanceOf[ITerm] === 0

      case Eq(IFunApp(f, _), _) if f == heap.nullAddr =>
        i(true) //subres(1).asInstanceOf[ITerm] === 0

      /** read(_,_) = _ --> remove */
      case Eq(IFunApp(f, _), _) if f == heap.read =>
        i(true) //i(true)

      /** write(h1,_,_) = h2 --> h1 === h2 */
      case Eq(IFunApp(f, _), _) if f == heap.write =>
        val funApp = subres(0).asInstanceOf[IFunApp]
        val h1 = funApp.args.head
        val h2 = subres(1).asInstanceOf[ITerm]
        i(true) //h1 === h2

      /** allocHeap(h1,_) = h2 --> h1+1 === h2 */
      case Eq(IFunApp(f, _), _) if f == heap.allocHeap =>
        val funApp = subres(0).asInstanceOf[IFunApp]
        val h1 = funApp.args.head
        val h2 = subres(1).asInstanceOf[ITerm]
        i(true) //h1 + 1 === h2

      /** allocAddr(h1,_) = a2 --> h1+1 === a2 */
      case Eq(IFunApp(f, _), _) if f == heap.allocAddr =>
        val funApp = subres(0).asInstanceOf[IFunApp]
        val h1 = funApp.args.head
        val a2 = subres(1).asInstanceOf[ITerm]
        i(true) //h1 + 1 === a2

      /** valid(h,a) --> h >= a > 0 */
      case IAtom(pred, _) if pred == heap.isAlloc =>
        val h = subres(0).asInstanceOf[ITerm]
        val a = subres(1).asInstanceOf[ITerm]
        i(true) //h >= a &&& a > 0

      /** !valid(h,a) */
      case INot(IAtom(pred, _)) if pred == heap.isAlloc =>
        i(true)

      case _ =>
        t update subres
    }
    private def oldToNewTerm(oldTerm : IConstant,
                             c       : SortedConstantTerm) = {
      termMap get oldTerm match {
        case Some(newTerm) => newTerm
        case None =>
          val newTerm = IConstant(new SortedConstantTerm(c.name, Sort.Nat))
          termMap += oldTerm -> newTerm
          newTerm
      }
    }
  }
}
