package lazabs.horn.preprocessor

import ap.parser.IExpression.{ConstantTerm, Eq, Predicate}
import ap.parser._
import ap.theories.Heap
import ap.theories.Heap.{HeapFunExtractor, HeapSort, HeapSortExtractor}
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
import com.sun.xml.internal.bind.v2.schemagen.xmlschema.LocalElement
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.preprocessor.AbstractAnalyserMk2.AbstractTransformerMk2
import lazabs.horn.preprocessor.PropagatingPreprocessorMk2.InliningAbstractDomain

import scala.collection.immutable.BitSet
import scala.collection.mutable.{Buffer => MBuffer, HashMap => MHashMap, HashSet => MHashSet}

object HeapUpdateSitesAnalysis {
  /**
   * Collects update sites for all [[ap.theories.Heap.AddressSort]] terms as a
   * set from predicate indices to ???
   * @requires at most one update per clause - as guaranteed by
   *           [[ClauseSplitterFuncsAndUnboundTerms]].
   */
  class UpdateSitesDomain(updateSiteTags : Set[Int])
    extends InliningAbstractDomain {
    private[preprocessor]
    case class HeapAddressIndPair(heapInd : Int,
                                  addrInd : Int,
                                  theory  : Heap)

    override val name : String = "analysing heap address update sites"

    private[preprocessor]
    case class LatticeElement(value : BitSet) {
      def join(that : LatticeElement) =
        LatticeElement(this.value union that.value)
      def meet(that : LatticeElement) =
        LatticeElement(this.value intersect that.value)
      override def toString : String = "{" + value.mkString(",") + "}"
      def <= (that : LatticeElement) : Boolean = this.value subsetOf that.value
    }
    object LatticeElement {
      /**
       * Lattice is the powerset of clause indices ++ three special values
       * NLL - null
       * NYA - not yet allocated
       * VLD - allocated but not coming from any updates (valid)
       * (Negative values cannot appear in [[updateSiteTags]].)
       * NLLCOMP - the complement of NLL
       */
      private val maxTag = updateSiteTags.max
      val NLL = LatticeElement(BitSet(maxTag + 1))
      val NYA = LatticeElement(BitSet(maxTag + 2))
      val VLD = LatticeElement(BitSet(maxTag + 3))
      val TOP = LatticeElement(BitSet(updateSiteTags.toSeq: _*) ++
                                 NLL.value ++ NYA.value ++ VLD.value)
      val BOT = LatticeElement(BitSet.empty)
      val NLLCOMP = LatticeElement(TOP.value -- NLL.value)
      val IDS = LatticeElement(BitSet(updateSiteTags.toSeq: _*))
    }

    /**
     * Element for the predicate. This is an [[Option]], because a contradiction
     * leads to None (e.g., if we have a = null & a = alloc(...)).
     */
    override type Element = Option[Map[HeapAddressIndPair, LatticeElement]]

    override def bottom(p : Predicate) : Element = None

    override def isBottom(b : Element) : Boolean = b.isEmpty

    /**
     * `join` is called while computing the fixed point over all clauses.
     */
    override def join(a: Element, b: Element): Element = a match {
      case None => b
      case Some(aMap) => b match {
        case None => a
        case Some(bMap) =>
          /**
           * If the pair is only present in a or b, then their join becomes
           * the top element (in this case simply missing from the computed
           * element).
           */
          // todo: initialize all pairs
          // assert same domain and nonempty
          Some(for ((key, aVal) <- aMap if bMap contains key) yield
            (key, aVal join bMap(key)))
      }
    }

    class HeapUpdateSitesTransformer(clause : Clause)
      extends AbstractTransformerMk2[Element](clause) {
      case class HeapAddressPair(heap   : ConstantTerm,
                                 addr   : ConstantTerm,
                                 theory : Heap)

      override type LocalElement = Map[HeapAddressPair, LatticeElement]

      override def meet(a : LocalElement, b : LocalElement) : LocalElement = {
        val result = new MHashMap[HeapAddressPair, LatticeElement]
        for ((key, aValue) <- a) {
          b.get(key) match {
            case Some(bValue) =>
              val meetResult = aValue meet bValue
              if (meetResult == LatticeElement.BOT) {
                return botLocalElement
              }
              result += (key -> meetResult)
            case None => // nothing needed
          }
        }
        result.toMap
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
              case LatticeElement.BOT => None
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
            case otherSort => // nothing
          }

          /** Initialize all pairs to the TOP element */
          for (heapTerm <- heapTerms; addrTerm <- addrTerms)
            elem += (HeapAddressPair(heapTerm, addrTerm, heap) ->
              LatticeElement.TOP)
        }
        elem.toMap
      }

      override val botLocalElement : LocalElement = Map()

      override def localElementForAtom(e : Element,
                                       a : IAtom) : LocalElement = {
        if (e.isEmpty) return botLocalElement
        val elem = e.get
        e.get.keys.foldLeft(topLocalElement){(curElem, indPair) =>
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
              }
              for (hInd <- heapInds; aInd <- addrInds) yield
                HeapAddressIndPair(hInd, aInd, heap)
            }
            keys.map{
              case key@HeapAddressIndPair(hInd, aInd, heap) =>
                val localKey = HeapAddressPair(args(hInd), args(aInd), heap)
                key -> e(localKey)
            }.toMap
        }
        if (res isEmpty) None else Some(res)
      }

      /**
       * Consider the function applications
       * allocHeap(h,o) = h', allocAddr(h,o) = a, and alloc(h,o) = ar
       * where any of them by itself does not provide enough information about
       * the newly allocated heap-address pair.
       * We run a pre-analysis to collect this information.
       * This analysis only runs within a single clause - it will not yield any
       * useful information if the functions are spread over multiple clauses.
       */
      private type OldHeapToAddrAfterAlloc = Map[ConstantTerm, ConstantTerm]
      private type AllocResToHeapAddrPair = Map[ConstantTerm, HeapAddressPair]
      override type PreAnalysisResult =
        (OldHeapToAddrAfterAlloc, AllocResToHeapAddrPair)
      override def preAnalysisFun(conjuncts : Seq[IFormula]) : PreAnalysisResult = {
        val oldHeapToAddrAfterAlloc = new MHashMap[ConstantTerm, ConstantTerm]
        val allocResToAddr = new MHashMap[ConstantTerm, ConstantTerm]
        val allocResToHeap = new MHashMap[ConstantTerm, ConstantTerm]
        val allocResToHeapAddrPair = new MHashMap[ConstantTerm, HeapAddressPair]
        var continue = true
        while(continue) {
          continue = false
          for(conjunct <- conjuncts) {
            conjunct match {
              /** allocAddr(h,_) = a */
              case Eq(IFunApp(fun@HeapFunExtractor(heap),
                              Seq(IConstant(h), _)), IConstant(a))
                if fun == heap.allocAddr && !(oldHeapToAddrAfterAlloc contains h) =>
                oldHeapToAddrAfterAlloc += h -> a

              /** newHeap(ar) = h */
              case Eq(IFunApp(fun@HeapFunExtractor(heap),
                              Seq(IConstant(ar))), IConstant(h))
                if fun == heap.newHeap && !(allocResToHeap contains h) =>
                allocResToHeap += ar -> h
                continue = true

              /** newAddr(ar) = a */
              case Eq(IFunApp(fun@HeapFunExtractor(heap),
                              Seq(IConstant(ar))), IConstant(a))
                if fun == heap.newAddr && !(allocResToAddr contains a) =>
                allocResToAddr += ar -> a
                continue = true

              /** alloc(h,o) = ar */
              case Eq(IFunApp(fun@HeapFunExtractor(heap),
                              Seq(IConstant(ar))), IConstant(a))
                if fun == heap.alloc &&
                  allocResToHeap.contains(ar) && allocResToAddr.contains(ar) =>
                allocResToHeapAddrPair += ar -> HeapAddressPair(
                  allocResToHeap(ar), allocResToAddr(ar), heap)

              case _ => // nothing
            }
          }
        }
        (oldHeapToAddrAfterAlloc.toMap, allocResToHeapAddrPair.toMap)
      }

      private def handleAllocate(h1      : ConstantTerm,
                                 h2      : ConstantTerm,
                                 heap    : Heap,
                                 a       : IExpression.ConstantTerm,
                                 tag     : Int,
                                 element : LocalElement) : Option[LocalElement] = {
        // Allocated address will have id i in the new heap
        val elem1 = meetAllWhere(key => key.heap == h2 && key.addr == a,
                                 element, LatticeElement(BitSet(tag)))
        elem1 match {
          case Some(e) =>
            // All other addresses, except those with value NYA, will preserve
            // their old values in the new heap.
            val allAddresses = e.keys.map(_.addr)
            allAddresses.foldLeft(Option(e)){(curEOpt, addr) =>
              curEOpt.flatMap{
                curE =>
                  val oldPair = HeapAddressPair(h1, addr, heap)
                  val newPair = HeapAddressPair(h2, addr, heap)
                  if (!(LatticeElement.NYA <= curE(oldPair))) {
                    meetAllWhere(
                      key => key.heap == newPair.heap && key.addr == newPair.addr,
                      curE, curE(oldPair))
                  } else Some(curE)
              }
            }
          case None => None
        }
      }

      override protected def constraintPropagator(conjunct : IFormula,
                                                  element  : LocalElement,
                                         preAnalysisResult : PreAnalysisResult)
      : Option[LocalElement] = conjunct match {

        /** nullAddress() = a */
        case Eq(IFunApp(fun@HeapFunExtractor(heap), _),
                IConstant(a)) if fun == heap.nullAddr =>
          println(s"case null = $a")
          meetAllWhere(_.addr == a, element, LatticeElement.NLL)

        /** emptyHeap() = h */
        case Eq(IFunApp(fun@Heap.HeapFunExtractor(heap), _), IConstant(h))
          if fun == heap.emptyHeap =>
          println("case emptyHeap")
          meetAllWhere(_.heap == h, element,
                       LatticeElement.NYA join LatticeElement.NLL)

        /** valid(h,a) & !((h,a) <= Ids)*/
        case IAtom(pred@Heap.HeapPredExtractor(heap),
                   Seq(IConstant(h), IConstant(a))) if pred == heap.isAlloc &&
          !(element(HeapAddressPair(h, a, heap)) <= LatticeElement.IDS)=>
          val key = HeapAddressPair(h, a, heap)
          println("case valid " + key)
          meetAllWhere(e => e.heap == h && e.addr == a, element, LatticeElement.VLD)

        /** !valid(h, a) */
        case INot(IAtom(pred@Heap.HeapPredExtractor(heap),
                        Seq(IConstant(h), IConstant(a)))) if pred == heap.isAlloc =>
          val key = HeapAddressPair(h, a, heap)
          println("case !valid " + key)
          meetAllWhere(key => key.heap == h && key.addr == a,
                       element, LatticeElement.NYA join LatticeElement.NLL)

        /** write(h1,a,TaggedObject(o,i)) = h2 & !({VLD} <= (h1,a))
         * @note We are assuming the inner app is TaggedObject without checking.
         */
        case Eq(IFunApp(fun@HeapFunExtractor(heap), Seq(
          IConstant(h1),IConstant(a),
          IFunApp(f, Seq(IConstant(o), IIntLit(i))))), IConstant(h2))
          if fun == heap.write &&
            !(LatticeElement.VLD <= element(HeapAddressPair(h1, a, heap))) =>
          println(s"case write($h1,$a,${f.name}($o,$i)) = $h2")
          val newVal = element(HeapAddressPair(h1, a, heap)) join
            LatticeElement(BitSet(i.intValue))
          meetAllWhere(e => e.heap == h2 && e.addr == a, element, newVal)

        /** write(h1,a,TaggedObject(o,i)) = h2 & {VLD} <= (h1,a) */
        case Eq(IFunApp(fun@HeapFunExtractor(heap), Seq(
        IConstant(h1), IConstant(a),
        IFunApp(f, Seq(IConstant(o), IIntLit(i))))), IConstant(h2))
          if fun == heap.write &&
            LatticeElement.VLD <= element(HeapAddressPair(h1, a, heap)) =>
          println(s"case write($h1,$a,${f.name}($o,$i)) = $h2")
          val newVal = LatticeElement(BitSet(i.intValue))
          meetAllWhere(e => e.heap == h2 && e.addr == a, element, newVal)
        ???

        /** alloc(h1,TaggedObject(o,i)) = ar */
        case eq@Eq(IFunApp(fun1@HeapFunExtractor(heap),
                        Seq(IConstant(h1),
                            IFunApp(f, Seq(IConstant(o), IIntLit(i))))),
                IConstant(ar)) if fun1 == heap.alloc &&
        preAnalysisResult._2.contains(ar) =>
          println("case alloc " + eq)
          val HeapAddressPair(h2, a, _) = preAnalysisResult._2(ar)
          handleAllocate(h1, h2, heap, a, i.intValue, element)

        /**
         * allocHeap(h1,TaggedObject(o,i)) = h2
         * allocAddr is not handled separately.
         */
        case eq@Eq(IFunApp(fun1@HeapFunExtractor(heap),
                           Seq(IConstant(h1),
                               IFunApp(f, Seq(IConstant(o), IIntLit(i))))),
                   IConstant(h2)) if fun1 == heap.allocHeap &&
          preAnalysisResult._1.contains(h1) =>
          println("case allocHeap " + eq)
          handleAllocate(h1, h2, heap, preAnalysisResult._1(h1), i.intValue, element)

        /** a1 === a2 (address equality) */
        case eq@Eq(IConstant(a1@SortedConstantTerm(_, sort)),
                IConstant(a2)) if sort.isInstanceOf[Heap.AddressSort] =>
          println("case addrEq1: " + eq)
          meetAllWhere(key => key.addr == a1 || key.addr == a2, element,
                       LatticeElement.TOP)

        /** h1 === h2 (heap equality) */
        case eq@Eq(IConstant(h1@SortedConstantTerm(_, sort)),
                   IConstant(h2)) if sort.isInstanceOf[Heap.HeapSort] =>
          println("case heapEq1: " + eq)
          meetAllWhere(key => key.heap == h1 || key.heap == h2, element,
                       LatticeElement.TOP)

        /** a1 =/= a2 (address inequality) */
        case eq@INot(Eq(IConstant(SortedConstantTerm(a1, sort)),
                        IConstant(a2)))
          if sort.isInstanceOf[Heap.AddressSort] =>
          println("case addrNeq1: " + eq)
          val a1IsNLL = element.exists{
            case (key, value) => key.addr == a1 && value == LatticeElement.NLL
          }
          val a2IsNLL = element.exists {
            case (key, value) => key.addr == a2 && value == LatticeElement.NLL
          }

          (a1IsNLL, a2IsNLL) match {
            case (true, _) =>
              meetAllWhere(_.addr == a2, element, LatticeElement.NLLCOMP)
            case (_, true) =>
              meetAllWhere(_.addr == a1, element, LatticeElement.NLLCOMP)
            case _ => Some(element)
          }

        /** No applicable rule */
        case _ => Some(element)
      }
    }


    override def transformerFor(clause : HornClauses.Clause) =
      new HeapUpdateSitesTransformer(clause)

    var printedLegend = false
    override def inline(a : IAtom, value : Element) : (IAtom, IFormula) = {
      if(!printedLegend) {
        printedLegend = true
        println(s"NLL -> ${LatticeElement.NLL.value}, NYA -> ${
          LatticeElement.NYA.value
        }, VLD -> ${LatticeElement.VLD.value}")
      }
      print(s"Element for atom $a: ")
      value.foreach(println)
      a -> true
      // TODO
    }
    override def augmentSolution(sol : IFormula, value : Element) : IFormula = {
      sol
      // TODO
    }
  }
}
