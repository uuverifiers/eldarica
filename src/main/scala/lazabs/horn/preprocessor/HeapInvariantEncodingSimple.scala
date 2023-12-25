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
import ap.theories.ADT.ADTProxySort
import ap.types.{MonoSortedIFunction, MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.{Clause, allPredicates}
import lazabs.horn.bottomup.Util.{DagEmpty, DagNode}

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

object ADTExploder {
  def apply(expr : IExpression) : IExpression =
    Rewriter.rewrite(expr, explodeADTs)

  case class ADTTerm(t : ITerm, adtSort : ADTProxySort)
  object adtTermExploder extends CollectingVisitor[Object, IExpression] {
    def getADTTerm(t : IExpression) : Option[ADTTerm] = {
      t match {
        case f @ IFunApp(fun, _) if ADT.Constructor.unapply(fun).nonEmpty =>
          val sortedFun = fun.asInstanceOf[MonoSortedIFunction]
          val adtSort = sortedFun.resSort.asInstanceOf[ADT.ADTProxySort]
          Some(ADTTerm(f, adtSort))
        case c@IConstant(SortedConstantTerm(_, sort))
          if sort.isInstanceOf[ADTProxySort] =>
          Some(ADTTerm(c, sort.asInstanceOf[ADTProxySort]))
        case _ => None
      }
    }

    override def postVisit(t: IExpression, none : Object,
                           subres: Seq[IExpression]) : IExpression = {

      import IExpression._
      def explodeADTSelectors (originalEq : IEquation, ctorFun : IFunction,
                               lhsIsCtor : Boolean) : IFormula = {
        val newEq = originalEq update subres
        val (newFunApp, selectorTerms, newRootTerm) =
          if (lhsIsCtor) {
            val Eq(newFunApp@IFunApp(_, selectorTerms), newRootTerm) = newEq
            (newFunApp, selectorTerms, newRootTerm)
          } else {
            val Eq(newRootTerm, newFunApp@IFunApp(_, selectorTerms)) = newEq
            (newFunApp, selectorTerms, newRootTerm)
          }
        val adtTerm = getADTTerm(newFunApp).get
        val adt = adtTerm.adtSort.adtTheory
        val ctorIndex = adt.constructors.indexOf(ctorFun)
        val selectors = adt.selectors(ctorIndex)
        adt.hasCtor(newRootTerm, ctorIndex) &&&
          (for ((fieldTerm, selectorInd) <- selectorTerms zipWithIndex) yield
          selectors(selectorInd)(newRootTerm) === fieldTerm).reduce(_ &&& _)
      }

      t match {
        case e@Eq(funApp@IFunApp(fun, _), _) if getADTTerm(funApp).nonEmpty =>
          explodeADTSelectors(e.asInstanceOf[IEquation], fun, lhsIsCtor = true)
        case e@Eq(_, funApp@IFunApp(fun, _)) if getADTTerm(funApp).nonEmpty =>
          explodeADTSelectors(e.asInstanceOf[IEquation], fun, lhsIsCtor = false)
        case t@IFunApp(f,_) =>
          val newApp = t update subres
          (for (theory <- TheoryRegistry lookupSymbol f;
                res <- theory evalFun newApp) yield res) getOrElse newApp
        case _ =>
          t update subres
      }
    }
  }

  // converts "s = S(a, b)" to "f1(s) = a & f2(s) = b"
  private def explodeADTs(expr : IExpression) : IExpression =
    adtTermExploder.visit(expr, null)

}

class HeapInvariantEncodingSimple extends HornPreprocessor {
  import HornPreprocessor._

  override val name : String = "Heap invariants encoder (simple)"
  private val backMapping = new MHashMap[Clause, Clause]

  /**
   * HeapInvariantEncodingSimple is only applicable when the input CHCs contain
   * exactly one heap theory.
   */
  override def isApplicable(clauses          : Clauses,
                            frozenPredicates : Set[Predicate]) : Boolean = {
    clauses.flatMap(c => c.theories).toSet.nonEmpty
  }

  override def process(clauses : Clauses,
                       hints : VerificationHints,
                       frozenPredicates : Set[Predicate])
  : (Clauses, VerificationHints, HornPreprocessor.BackTranslator) = {
    val heapTheories = clauses.flatMap(c => c.theories)
                              .filter(theory => theory.isInstanceOf[Heap])
                              .map(theory => theory.asInstanceOf[Heap])
                              .toSet

//    println("Applying heap invariant encoding to the following clauses")
//    println("="*80)
//    clauses.foreach(clause => println(clause.toPrologString))
//    println("="*80)
//    println
    var currentClauses = clauses

    // Define an invariant per heap theory
    val heapInvariantPerHeap : Map[Heap, Predicate] = heapTheories.map(
      heap => heap -> new MonoSortedPredicate(
        s"Inv_${heap.HeapSort.name}", Seq(heap.AddressSort, heap.ObjectSort)))
      .toMap

    val allHeapInvariants : Set[Predicate] = heapInvariantPerHeap.values.toSet

    // Collect maps from sorts to argument indices containing those sorts
    // in every predicate.
    val predSortToArgInds = new MHashMap[Predicate, Map[Sort, List[Int]]]
    for (pred <- allPredicates(clauses)) {
      pred match {
        case sortedPred : MonoSortedPredicate =>
          val sortInds = new MHashMap[Sort, List[Int]]
          for ((sort, ind) <- sortedPred.argSorts.zipWithIndex) {
            sortInds get sort match {
              case None      => sortInds += sort -> List(ind)
              case Some(seq) => sortInds += sort -> (ind :: seq)
            }
          }
          predSortToArgInds += pred -> sortInds.toMap
        case _ =>
          predSortToArgInds +=
            pred -> Map(Sort.Integer -> (0 until  pred.arity).toList)
      }
    }

/**
 * Why normalization is needed: consider the following clause with two heap ops.
 * Each read replaces a clause with two clauses.

  head :- read1 & read2

 * The following translation is weak (num_reads*2 clauses), because each
 * path to "head" only considers one of the reads (i.e., the invariants of
 * other reads are not propagated even when those reads are valid).

  head :- read1 & read2 &  valid1 & Inv1
  head :- read1 & read2 & !valid1
  head :- read1 & read2 &  valid2 & Inv2
  head :- read1 & read2 & !valid2

 * The stronger encoding would be as follows, but grows the number of clauses
 * exponentially in the number of reads (i.e., num_reads^^2 clauses):

  head :- read1 & read2 & valid1  & Inv1 & valid2 & Inv2
  head :- read1 & read2 & valid1  & Inv1 & !valid2
  head :- read1 & read2 & !valid1        & valid2 & Inv2
  head :- read1 & read2 & !valid1        & !valid2

 * Normalization (i.e., one clause per heap operation) would in this case first
 * split the original clause into num_reads, and then transform each clause
 * with a read into two clauses, leading to num_reads*2 clauses.
*/
    // Each heap theory
    for (heap <- heapTheories) {
      val newClauses = new ArrayBuffer[HornClauses.Clause]
      val inv = heapInvariantPerHeap(heap)
      for (clause <- currentClauses) {
        val conjuncts =
          LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)

        var addedThisClause = false
        for (conjunct <- conjuncts) {
          conjunct match {
            // alloc(h0, o) == ar: push inv(allocAddr(h0, o), o)
            case Eq(IFunApp(heap.alloc, Seq(IConstant(h0), IConstant(o))),
                    IConstant(ar)) =>
              val a = heap.allocAddr(h0, o)
              val newClause = Clause(inv(a, o), clause.body, clause.constraint)
              newClauses += newClause
              backMapping += newClause -> clause
              newClauses += clause
              assert(!addedThisClause)
              addedThisClause = true

            // allocHeap(h0, o) == h1: push inv(allocAddr(h0, o), o)
            case Eq(IFunApp(heap.allocHeap, Seq(IConstant(h0), IConstant(o))),
                    IConstant(h1)) =>
              val a = heap.allocAddr(h0, o)
              val newClause = Clause(inv(a, o), clause.body, clause.constraint)
              newClauses += newClause
              backMapping += newClause -> clause
              newClauses += clause
              assert(!addedThisClause)
              addedThisClause = true

            // write(h0, a, o) == h1: push inv(a, o) if valid(h0, a)
            case Eq(IFunApp(heap.write,
                            Seq(IConstant(h0), IConstant(a), IConstant(o))),
                    IConstant(h1)) =>
              val newClause = Clause(inv(a, o), clause.body,
                                     clause.constraint &&& heap.isAlloc(h0, a))
              newClauses += newClause
              backMapping += newClause -> clause
              newClauses += clause
              assert(!addedThisClause)
              addedThisClause = true

            // read(h, a) == o: replace original clause with two clauses:
            //   1) head :- body & valid(h, a) & I(a, o)
            //   2) head :- body & !valid(h,a)
            case Eq(IFunApp(heap.read,
                            Seq(IConstant(h), IConstant(a))),
                    IConstant(o)) =>
              val newClause1 =
                Clause(clause.head, inv(a, o) :: clause.body,
                       clause.constraint &&& heap.isAlloc(h, a))
              val newClause2 =
                Clause(clause.head, clause.body,
                       clause.constraint &&& !heap.isAlloc(h, a))
              newClauses ++= Seq(newClause1, newClause2)
              backMapping ++= Map(newClause1 -> clause, newClause2 -> clause)
              assert(!addedThisClause)
              addedThisClause = true
            case _ =>
//              println(s"Ignoring conjunct $conjunct in clause ${clause.toPrologString}")

            // todo: handle unbound heap terms
          }
        }
        if (!addedThisClause)
          newClauses += clause
      }
      currentClauses = newClauses
    }

    val backTranslator = new BackTranslator {
      override def translate(solution : Solution) : Solution = {
        val newSolution                   = new MHashMap[Predicate, IFormula]
        val solutionWithoutHeapInvariants =
          solution -- heapInvariantPerHeap.values
        solutionWithoutHeapInvariants.foreach(newSolution +=)
        for (heap <- heapTheories; (pred, _) <- solutionWithoutHeapInvariants) {
          predSortToArgInds(pred) get heap.HeapSort match {
            case Some(heapInds) if heapInds.nonEmpty =>
              val invF = solution(heapInvariantPerHeap(heap))
              for (heapInd <- heapInds) {
                val adtExploded = ADTExploder(invF).asInstanceOf[IFormula]
                val simplified  = SimpleAPI.withProver(_.simplify(adtExploded))

                // Augment the solution of this predicate with:
                // forall a. valid(h, a) ==> inv(a, read(h, a))
                // Where a is quantified only over the address arguments of
                // the current predicate.
                val newConj = {
                  val h = v(heapInd, heap.HeapSort)
                  heap.AddressSort.all(
                    a => heap.isAlloc(h, a) ===> VariableSubstVisitor(
                      simplified, (List(a, heap.read(h, a)), 0)))
                }
                newSolution(pred) = newSolution(pred) &&& newConj
              }
            case _ =>
          }
        }
        newSolution.toMap
      }
      override def translate(cex : CounterExample) : CounterExample =
        translateCEX(cex).collapseNodes

      private def translateCEX(dag : CounterExample) : CounterExample =
        dag match {
          case DagNode(p@(a, clause), children, next) =>
            val newChildren = children.filterNot(
              i => allHeapInvariants.contains(dag(i)._1.pred))
            val newNext = translateCEX(next)
            backMapping get clause match {
              case Some(oldClause) =>
                DagNode((a, oldClause), newChildren, newNext)
              case None =>
                DagNode(p, newChildren, newNext)
            }
          case DagEmpty => DagEmpty
        }
    }

//    println("\nNew clauses")
//    println("=" * 80)
//    currentClauses.foreach(clause => println(clause.toPrologString))
//    println("=" * 80)
//    println

    (currentClauses, hints, backTranslator)
  }
}
