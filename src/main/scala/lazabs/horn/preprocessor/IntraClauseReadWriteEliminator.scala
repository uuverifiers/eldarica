/**
 * Copyright (c) 2024 Zafer Esen. All rights reserved.
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

import ap.parser.IExpression._
import ap.parser._
import ap.theories.ADT.{ADTSort, OtherSort}
import ap.theories.Heap.HeapFunExtractor
import ap.theories.{ADT, Heap}
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.Util.{DagEmpty, DagNode}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.preprocessor.AbstractAnalyserMk2.AbstractTransformerMk2

import scala.collection.immutable.BitSet
import scala.collection.mutable.{ArrayBuffer, Buffer => MBuffer, HashMap => MHashMap, HashSet => MHashSet}

class IntraClauseReadWriteEliminator extends HornPreprocessor {
  import HornPreprocessor._

  override val name : String = "eliminating simple heap read/write operations"

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

    case class LatticeElement(value : BitSet) {
      def join(that : LatticeElement) = LatticeElement(value union that.value)
      def meet(that : LatticeElement) = LatticeElement(value intersect that.value)
      def <=(that : LatticeElement) : Boolean = this.value subsetOf that.value
      override def toString : String = "{" + value.map{
        case 0 => "NLL"
        case 1 => "NYA"
        case 2 => "VLD"
      }.mkString(",") + "}"
    }

    val NLL = LatticeElement(BitSet(0))
    val NYA = LatticeElement(BitSet(1))
    val VLD = LatticeElement(BitSet(2))
    val TOP = LatticeElement(NLL.value ++ NYA.value ++ VLD.value)
    val BOT = LatticeElement(BitSet.empty)

    case class HeapAddressIndPair(heapInd : Int,
                                  addrInd : Int,
                                  theory  : Heap) {
      override def toString : String = s"($heapInd,$addrInd)"
    }

    case class HeapAddressPair(heap   : ConstantTerm,
                               addr   : ConstantTerm,
                               theory : Heap) {
      override def toString : String = s"($heap,$addr)"
    }

    val domain = new AbstractAnalyserMk2.AbstractDomainMk2 {
      override val name : String = "Heap validity"
      override type Element = Option[Map[HeapAddressIndPair, LatticeElement]]
      override type LocalElement = Map[HeapAddressPair, LatticeElement]
      override def bottom(p : Predicate) : Element = None
      override def isBottom(b : Element) : Boolean = b.isEmpty
      override def join(a : Element, b : Element) : Element = a match {
        case None => b
        case Some(aMap) => b match {
          case None => a
          case Some(bMap) =>
            Some(for ((key, aVal) <- aMap if bMap contains key) yield
              (key, aVal join bMap(key)))
        }
      }

      class HeapValidityTransformer(clause : Clause)
        extends AbstractTransformerMk2[Element, LocalElement](clause) {
        override def meet(a : LocalElement,
                          b : LocalElement) : LocalElement = {
          val commonKeys    = a.keySet.intersect(b.keySet)
          val commonResults = commonKeys.flatMap{key =>
            val meetResult = a(key) meet b(key)
            if (meetResult == BOT) return botLocalElement
            Some(key -> meetResult)
          }

          val uniqueA = a -- b.keySet
          val uniqueB = b -- a.keySet

          (commonResults ++ uniqueA ++ uniqueB).toMap
        }

        /**
         * Meets *all* elements that satisfy cond and `v`
         */
        def meetAllWhere(cond : HeapAddressPair => Boolean,
                         elem : LocalElement,
                         v    : LatticeElement) : Option[LocalElement] = {
          elem.keys.filter(cond).foldLeft(Option(elem)){(accOpt, key) =>
            accOpt.flatMap{accMap =>
              accMap(key) meet v match {
                case BOT => None
                case updated => Some(accMap + (key -> updated))
              }
            }
          }
        }

        override val topLocalElement : LocalElement = {
          val heaps = clause.theories.collect{case h : Heap => h}
          val elem  = new MHashMap[HeapAddressPair, LatticeElement]

          for (heap <- heaps) {
            val heapTerms = MBuffer[ConstantTerm]()
            val addrTerms = MBuffer[ConstantTerm]()

            /** Collect heap and address pairs */
            clause.constants.foreach{
              case SortedConstantTerm(c, sort) if sort == heap.HeapSort =>
                heapTerms += c
              case SortedConstantTerm(c, sort) if sort == heap.AddressSort =>
                addrTerms += c
              case _ => // nothing
            }

            /** Initialize all pairs to the TOP element */
            for (heapTerm <- heapTerms; addrTerm <- addrTerms)
              elem += (HeapAddressPair(heapTerm, addrTerm, heap) -> TOP)
          }
          elem.toMap
        }

        override val botLocalElement : LocalElement = Map()

        override def localElementForAtom(e : Element,
                                         a : IAtom) : LocalElement = {
          if (e.isEmpty) return botLocalElement
          val elem = e.get
          elem.keys.foldLeft(topLocalElement){(curElem, indPair) =>
            // Construct the actual HeapAddressPair based on indices and the
            // atom's arguments.
            val heapTerm = a.args(indPair.heapInd).asInstanceOf[IConstant].c
            val addrTerm = a.args(indPair.addrInd).asInstanceOf[IConstant].c
            val termPair =
              HeapAddressPair(heapTerm, addrTerm, indPair.theory)

            assert(curElem contains termPair,
                   s"top does not have value for $termPair")
            curElem.updated(termPair, elem(indPair) meet curElem(termPair))
          }
        }

        override def elementForAtom(e : LocalElement, a : IAtom) : Element = {
          assert(a.args.forall(_.isInstanceOf[IConstant]),
                 s"Atom must only have constant terms as arguments: $a")
          val args = a.args.map(_.asInstanceOf[IConstant].c)
          val res  = a.pred match {
            case p : MonoSortedPredicate =>
              val heaps = clause.theories.collect{case h : Heap => h}
              val keys  = heaps.flatMap{heap =>
                val heapInds = new MHashSet[Int]
                val addrInds = new MHashSet[Int]
                for ((sort, ind) <- p.argSorts zipWithIndex) sort match {
                  case heap.HeapSort => heapInds += ind
                  case heap.AddressSort => addrInds += ind
                  case _ => // nothing
                }
                for (hInd <- heapInds; aInd <- addrInds) yield
                  HeapAddressIndPair(hInd, aInd, heap)
              }
              keys.map{
                case key@HeapAddressIndPair(hInd, aInd, heap) =>
                  val localKey = HeapAddressPair(args(hInd), args(aInd), heap)
                  key -> e(localKey)
              }.toMap
            case _ => Map[HeapAddressIndPair, LatticeElement]()
          }
          Some(res)
        }

        private type OldHeapToAddrAfterAlloc = Map[ConstantTerm, ConstantTerm]
        override type PreAnalysisResult = OldHeapToAddrAfterAlloc
        override def preAnalysisFun(conjuncts : Seq[IFormula]) : PreAnalysisResult = {
          /** alloc and AllocRes selectors should have already been eliminated. */
          if (conjuncts.exists {
            case Eq(IFunApp(fun@HeapFunExtractor(heap), _), _)
              if Seq(heap.newHeap, heap.newAddr, heap.alloc).contains(fun) => true
            case _ => false
          }) throw new UnsupportedOperationException(
            s"The input clauses to preprocessor '$name' contains the " +
              s"function alloc or a selector of AllocRes. This can happen " +
              s"if ConstraintSimplifier was not applied first.")

          val oldHeapToAddrAfterAlloc = conjuncts.collect{
            case Eq(IFunApp(fun@HeapFunExtractor(heap), Seq(IConstant(h), _)),
                    IConstant(a)) if fun == heap.allocAddr =>
              (h, a)
          }.toMap
          oldHeapToAddrAfterAlloc
        }

        override protected def constraintPropagator(
          conjunct : IFormula, element  : LocalElement,
          preAnalysisResult : PreAnalysisResult)
        : Option[LocalElement] = conjunct match {

          /** nullAddress() = a */
          case Eq(IFunApp(fun@HeapFunExtractor(heap), _),
                  IConstant(a)) if fun == heap.nullAddr =>
            meetAllWhere(_.addr == a, element, NLL)

          /** emptyHeap() = h */
          case Eq(IFunApp(fun@Heap.HeapFunExtractor(heap), _), IConstant(h))
            if fun == heap.emptyHeap =>
            meetAllWhere(_.heap == h, element, NYA join NLL)

          /** valid(h,a) */
          case IAtom(pred@Heap.HeapPredExtractor(heap),
                     Seq(IConstant(h), IConstant(a))) if pred == heap.isAlloc =>
            meetAllWhere(e => e.heap == h && e.addr == a, element, VLD)

          /** !valid(h, a) */
          case INot(IAtom(pred@Heap.HeapPredExtractor(heap),
                          Seq(IConstant(h), IConstant(a)))) if pred == heap.isAlloc =>
            meetAllWhere(key => key.heap == h && key.addr == a, element, NYA join NLL)

          /** write(h1,a,_) = h2 --> forall a'; (h2,a') <= (h1, a')*/
          case Eq(IFunApp(fun@HeapFunExtractor(heap), Seq(
          IConstant(h1), IConstant(a), _)), IConstant(h2))
            if fun == heap.write =>

            val allAddresses = element.keys.map(_.addr)
            allAddresses.foldLeft(Option(element)){(curEOpt, a2) =>
              curEOpt.flatMap{
                curE =>
                  val oldPair = HeapAddressPair(h1, a2, heap)
                  val newPair = HeapAddressPair(h2, a2, heap)

                  meetAllWhere(key => key.heap == newPair.heap &&
                    key.addr == newPair.addr, curE, curE(oldPair))
              }
            }

          /**
           * allocHeap(h1,o) = h2
           * allocAddr is not handled separately.
           *
           * --> allocated addr a --> (h2,a) <= {VLD}
           * --> forall a'; (h2,a') <= (h1, a') if !({NYA} <= (h1,a'))
           * --> forall a'; (h2,a') <= (h1, a') ++ {VLD} if {NYA} <= (h1,a')
           */
          case Eq(IFunApp(fun1@HeapFunExtractor(heap),
                          Seq(IConstant(h1), _)),
                  IConstant(h2)) if fun1 == heap.allocHeap &&
            preAnalysisResult.contains(h1) =>

            // Allocated address will be allocated in the new heap
            val elem1 = meetAllWhere(
              key => key.heap == h2 && key.addr == preAnalysisResult(h1), element, VLD)

            if (elem1 isEmpty) return None
            // All other addresses
            val allAddresses = elem1.get.keys.map(_.addr)
            allAddresses.foldLeft(elem1){(curEOpt, addr) =>
              curEOpt.flatMap{
                curE =>
                  val oldPair = HeapAddressPair(h1, addr, heap)
                  val newPair = HeapAddressPair(h2, addr, heap)
                  if (!(NYA <= curE(oldPair))) {
                    // those except with value NYA, will preserve their old values
                    meetAllWhere(
                      key => key.heap == newPair.heap && key.addr == newPair.addr,
                      curE, curE(oldPair))
                  } else {
                    // those with value NYA can also be valid now
                    meetAllWhere(
                      key => key.heap == newPair.heap && key.addr == newPair.addr,
                      curE, curE(oldPair) join VLD)
                  }
              }
            }

          /** a1 === a2 (address equality) */
          case Eq(IConstant(a1@SortedConstantTerm(_, sort)),
                  IConstant(a2)) if sort.isInstanceOf[Heap.AddressSort] =>
            meetAllWhere(key => key.addr == a1 || key.addr == a2, element, TOP)

          /** h1 === h2 (heap equality) */
          case Eq(IConstant(h1@SortedConstantTerm(_, sort)),
                  IConstant(h2)) if sort.isInstanceOf[Heap.HeapSort] =>
            meetAllWhere(key => key.heap == h1 || key.heap == h2, element, TOP)

          /** a1 =/= a2 (address inequality) */
          case INot(Eq(IConstant(SortedConstantTerm(a1, sort)),
                       IConstant(a2)))
            if sort.isInstanceOf[Heap.AddressSort] =>
            val a1IsNLL = element.exists{
              case (key, value) => key.addr == a1 && value == NLL
            }
            val a2IsNLL = element.exists {
              case (key, value) => key.addr == a2 && value == NLL
            }

            (a1IsNLL, a2IsNLL) match {
              case (true, _) =>
                meetAllWhere(_.addr == a2, element, VLD join NYA)
              case (_, true) =>
                meetAllWhere(_.addr == a1, element, VLD join NYA)
              case _ => Some(element)
            }

          /** No applicable rule */
          case _ => Some(element)
        }
      }

      override def transformerFor(clause : Clause)
      : AbstractAnalyserMk2.AbstractTransformerMk2[Element, LocalElement] =
        new HeapValidityTransformer(clause)
    }

    val analyser = new AbstractAnalyserMk2(clauses, domain, frozenPredicates)

//    val heapTheories = clauses.flatMap(c => c.theories)
//      .filter(theory => theory.isInstanceOf[Heap])
//      .map(theory => theory.asInstanceOf[Heap])
//      .toSet

    val newClauses = for (clause <- clauses) yield analyser.clauseToElement(clause) match {
      case Some(element) => {
        val conjuncts =
          LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)
        /**
         * First step: try to eliminate reads.
         *      write(h1,a,o) = h2, read(h2,a) = o2,          (1) rd-after-wt
         *  --> write(h1,a,o = h2),   o = o2
         *      alloc(h1,o) = (h2,a), read(h2,a) = o2         (2) rd-after-alloc
         *  --> alloc(h1,o) = (h2,a), o = o2
         * Second step: try to merge writes with allocs.
         *      write(h2,a2,o2) = h3, alloc(h1,o1) = (h2,a2)  (3) wt-after-alloc
         * -->                        alloc(h1,o2) = (h3,a2)
         * @todo improve this / run it multiple times / eliminate writes to the same address
         * @note (1) is only applicable when valid(h2,a).
         *       (3) is only applicable when h2 is not used anywhere else except
         *       for valid predicates - this is why (1) & (2) are applied first.
         */
        case class Write(h1 : ConstantTerm, a  : ConstantTerm, o : ConstantTerm,
                         h2 : ConstantTerm, heap : Heap, conjunct : IFormula)
        case class Read (h  : ConstantTerm, a  : ConstantTerm, o : ConstantTerm,
                         heap : Heap, readApp : IFunApp, conjunct : IFormula)
        case class Alloc(h1 : ConstantTerm, o  : ConstantTerm, h2 : ConstantTerm,
                         a : ConstantTerm, heap : Heap,
                         allocAddrConjunct : IFormula, allocHeapConjunct : IFormula)

        /** For writes and allocs, the keys are (h2, a) */
        val writes = new MHashMap[HeapAddressPair, Write]
        val reads  = new MHashMap[HeapAddressPair, Read]
        val allocs = new MHashMap[HeapAddressPair, Alloc]

        val oldHeapToAddrAfterAlloc = conjuncts.collect{
          case eq@Eq(IFunApp(fun@HeapFunExtractor(heap), Seq(IConstant(h), _)),
                  IConstant(a))
            if fun == heap.allocAddr =>
            h -> (a, eq)
        }.toMap

        for (conjunct <- conjuncts) conjunct match {
          case Eq(IFunApp(fun@Heap.HeapFunExtractor(heap),
                          Seq(IConstant(h1), IConstant(a), IConstant(o))),
                  IConstant(h2))
            if fun == heap.write =>
            writes += HeapAddressPair(h2, a, heap) -> Write(h1, a, o, h2, heap, conjunct)
          case Eq(app@IFunApp(fun@Heap.HeapFunExtractor(heap),
                          Seq(IConstant(h), IConstant(a))), IConstant(o))
            if fun == heap.read =>
            reads += HeapAddressPair(h, a, heap) -> Read(h, a, o, heap, app, conjunct)
          case Eq(IFunApp(fun@Heap.HeapFunExtractor(heap),
                          Seq(IConstant(h1), IConstant(o))), IConstant(h2))
            if fun == heap.allocHeap && oldHeapToAddrAfterAlloc.contains(h1) =>
            val (a, allocAddrConjunct) = oldHeapToAddrAfterAlloc(h1)
            allocs += HeapAddressPair(h2, a, heap) ->
              Alloc(h1, o, h2, a, heap, allocAddrConjunct, conjunct)
          case _ => // nothing
        }

        val readsAfterValidWrites = reads.collect{
          case (pair, read)
            if writes.contains(pair) && (element(pair) <= VLD)=>
            read -> writes(pair)
        }

        val readsAfterAllocs = reads.collect{
          case (pair, read) if allocs contains pair =>
            read -> allocs(pair)
        }

        /** First, try to eliminate unnecessary reads */
        val newReadConjuncts = reads.map{
          case (_, read) =>
            val readObj : ITerm = readsAfterAllocs get read match {
              case Some(alloc) => IConstant(alloc.o)
              case None => readsAfterValidWrites get read match {
                case Some(write) => IConstant(write.o)
                case None => read.readApp
              }
            }
            read.conjunct -> (readObj === read.o)
        }

        val conjunctsAfterReadElimination = conjuncts.map(
          c => newReadConjuncts.getOrElse(c, c))

        val allocToWriteAfterAlloc = writes.collect{
          case (_, write@Write(h1, a, o, h2, heap, conjunct)) if
            allocs contains HeapAddressPair(h1, a, heap) =>
            allocs(HeapAddressPair(h1, a, heap)) -> write
        }

        val conjunctsWithoutIsAlloc = conjunctsAfterReadElimination.filter{
          case IAtom(f@Heap.HeapPredExtractor(heap), _)
            if f == heap.isAlloc => false
          case INot(IAtom(f@Heap.HeapPredExtractor(heap), _))
            if f == heap.isAlloc => false
          case _ => true
        }

        val conjunctToSymbols : Map[IFormula, Set[ConstantTerm]] =
          conjunctsWithoutIsAlloc.map(
            c => c -> SymbolCollector.constants(c).toSet).toMap

        val conjunctsToRemove = new MHashSet[IFormula]
        val conjunctsToAdd = new MHashSet[IFormula]

        allocs.foreach{
          case (_, alloc@Alloc(h1, o, h2, a, heap,
                               allocAddrConjunct, allocHeapConjunct))
            if allocToWriteAfterAlloc contains alloc =>
            /** Check if h2 is used anywhere except
             *  valid predicates (and this conjunct) in the current clause */
            val headAndBodyArgs =
              (clause.head.args ++ clause.body.flatMap(_.args)).toSet

            val write = allocToWriteAfterAlloc(alloc)

            val h2StillUsed = (conjunctsWithoutIsAlloc.exists{
              case c if c != allocHeapConjunct && c != write.conjunct =>
                conjunctToSymbols(c) contains h2
              case _ => false
            }) || headAndBodyArgs.contains(IConstant(h2))

            if(h2StillUsed) {
              // nothing
            } else {
              /** Replace alloc(h1,o) = (h2,a) with alloc(h1,o') = (h',a)
               *  where h' and o are h2 and o from the write. */
              conjunctsToRemove += allocAddrConjunct
              conjunctsToRemove += allocHeapConjunct
              conjunctsToRemove += write.conjunct
              conjunctsToAdd += heap.allocHeap(h1, write.o) === write.h2
              conjunctsToAdd += heap.allocAddr(h1, write.o) === a
            }
          case _ => // nothing
        }

        val finalConjuncts = conjunctsAfterReadElimination.filterNot(
          c => conjunctsToRemove contains c) ++ conjunctsToAdd

//        println("starting constraint")
//        println(and(conjuncts))
//        println
//        println("remaining constraint")
//        println(and(finalConjuncts))

        Clause(clause.head, clause.body, and(finalConjuncts))
      }
      case None => clause
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
    (newClauses, hints, backTranslator)
  }
}
