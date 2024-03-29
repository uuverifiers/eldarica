package lazabs.horn.preprocessor

import ap.parser.IExpression.{ConstantTerm, Eq, Predicate}
import ap.parser._
import ap.theories.Heap
import ap.theories.Heap.HeapFunExtractor
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
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
                                  theory  : Heap) {
      override def toString : String = s"($heapInd,$addrInd)"
    }

    override val name : String = "analysing heap address update sites"

    private[preprocessor]
    case class LatticeElement(value : BitSet) {
      def join(that : LatticeElement) =
        LatticeElement(this.value union that.value)
      def meet(that : LatticeElement) =
        LatticeElement(this.value intersect that.value)
      override def toString : String = this match {
        case LatticeElement.TOP => "TOP"
        case LatticeElement.BOT => "BOT"
        case _ =>
          "{" + value.map{
            case LatticeElement.idNLL => "NLL"
            case LatticeElement.idNYA => "NYA"
            case LatticeElement.idVLD => "VLD"
            case tag => tag.toString
          }.mkString(",") + "}"
      }

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
      val idNLL = maxTag + 1
      val idNYA = maxTag + 2
      val idVLD = maxTag + 3
      val NLL = LatticeElement(BitSet(idNLL))
      val NYA = LatticeElement(BitSet(idNYA))
      val VLD = LatticeElement(BitSet(idVLD))
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
                                 theory : Heap) {
        override def toString : String = s"($heap,$addr)"
      }

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

        if(oldHeapToAddrAfterAlloc.nonEmpty ) {
          println("Preanalysis for clause: (" + clause.toPrologString + ")")
          println("oldHeapToAddrAfterAlloc: " + oldHeapToAddrAfterAlloc)
          println
        }
        oldHeapToAddrAfterAlloc
      }

      def mayAlias(pair1 : HeapAddressPair,
                   pair2 : HeapAddressPair,
                   element : LocalElement) : Boolean = {
        ((element(pair1) meet element(pair2)) != LatticeElement.BOT) ||
          element(pair1) <= LatticeElement.IDS &&
            LatticeElement.VLD <= element(pair2) ||
          element(pair2) <= LatticeElement.IDS &&
            LatticeElement.VLD <= element(pair1)
      }

      override protected def constraintPropagator(conjunct : IFormula,
                                                  element  : LocalElement,
                                         preAnalysisResult : PreAnalysisResult)
      : Option[LocalElement] = conjunct match {

        /** nullAddress() = a */
        case Eq(IFunApp(fun@HeapFunExtractor(heap), _),
                IConstant(a)) if fun == heap.nullAddr =>
//          println(s"case null = $a")
          meetAllWhere(_.addr == a, element, LatticeElement.NLL)

        /** emptyHeap() = h */
        case Eq(IFunApp(fun@Heap.HeapFunExtractor(heap), _), IConstant(h))
          if fun == heap.emptyHeap =>
//          println(s"case emptyHeap = $h")
          meetAllWhere(_.heap == h, element,
                       LatticeElement.NYA join LatticeElement.NLL)

        /** valid(h,a) & !((h,a) <= Ids)*/
        case IAtom(pred@Heap.HeapPredExtractor(heap),
                   Seq(IConstant(h), IConstant(a))) if pred == heap.isAlloc &&
          !(element(HeapAddressPair(h, a, heap)) <= LatticeElement.IDS)=>
          val key = HeapAddressPair(h, a, heap)
//          println("case valid " + key)
          meetAllWhere(e => e.heap == h && e.addr == a, element, LatticeElement.VLD)

        /** !valid(h, a) */
        case INot(IAtom(pred@Heap.HeapPredExtractor(heap),
                        Seq(IConstant(h), IConstant(a)))) if pred == heap.isAlloc =>
          val key = HeapAddressPair(h, a, heap)
//          println("case !valid " + key)
          meetAllWhere(key => key.heap == h && key.addr == a,
                       element, LatticeElement.NYA join LatticeElement.NLL)

        /** write(h1,a,TaggedObject(o,i)) = h2 & !({VLD} <= (h1,a))
         * @note We are assuming the inner app is TaggedObject without checking.
         */

        /** write(h1,a,TaggedObject(o,i)) = h2 */
        case Eq(IFunApp(fun@HeapFunExtractor(heap), Seq(
        IConstant(h1), IConstant(a),
        IFunApp(f, Seq(IConstant(o), IIntLit(i))))), IConstant(h2))
          if fun == heap.write =>
//          println(s"case write($h1,$a,${f.name}($o,$i)) = $h2")
          // if !((h1,a) <= {NYA, NLL}), update the written address
          val elem1 =
            if (!(element(HeapAddressPair(h1, a, heap)) <=
              (LatticeElement.NLL join LatticeElement.NYA))) {
              meetAllWhere(e => e.heap == h2 && e.addr == a, element,
                           LatticeElement(BitSet(i.intValue)))
            } else Some(element)

          if (elem1 isEmpty) return None

          // forall a2. the cases if mayAlias(h,a,a2) and !mayAlias(h,a,a2)
          val allAddresses = elem1.get.keys.map(_.addr)
          allAddresses.foldLeft(elem1){(curEOpt, a2) =>
            curEOpt.flatMap{
              curE =>
                val pair1 = HeapAddressPair(h1, a, heap)
                val pair2 = HeapAddressPair(h1, a2, heap)
                val newValue = if(mayAlias(pair1, pair2, curE)) {
                  curE(pair2) join LatticeElement(BitSet(i.intValue))
                } else {
                  curE(pair2)
                }
                val a2InNewHeap = HeapAddressPair(h2, a2, heap)
                meetAllWhere(key => key.heap == a2InNewHeap.heap &&
                  key.addr == a2InNewHeap.addr, curE, newValue)
            }
          }

        /**
         * allocHeap(h1,TaggedObject(o,i)) = h2
         * allocAddr is not handled separately.
         */
        case eq@Eq(IFunApp(fun1@HeapFunExtractor(heap),
                           Seq(IConstant(h1),
                               IFunApp(f, Seq(IConstant(o), IIntLit(i))))),
                   IConstant(h2)) if fun1 == heap.allocHeap &&
          preAnalysisResult.contains(h1) =>
//          println("case allocHeap " + eq)

          // Allocated address will have id i in the new heap
          val elem1 = meetAllWhere(
            key => key.heap == h2 && key.addr == preAnalysisResult(h1),
            element, LatticeElement(BitSet(i.intValue)))

          if (elem1 isEmpty) return None
          // All other addresses, except those with value NYA, will preserve
          // their old values in the new heap.
          val allAddresses = elem1.get.keys.map(_.addr)
          allAddresses.foldLeft(elem1){(curEOpt, addr) =>
            curEOpt.flatMap{
              curE =>
                val oldPair = HeapAddressPair(h1, addr, heap)
                val newPair = HeapAddressPair(h2, addr, heap)
                if (!(LatticeElement.NYA <= curE(oldPair))) {
                  meetAllWhere(
                    key => key.heap == newPair.heap && key.addr == newPair
                      .addr,
                    curE, curE(oldPair))
                } else Some(curE)
            }
          }

        /** a1 === a2 (address equality) */
        case eq@Eq(IConstant(a1@SortedConstantTerm(_, sort)),
                IConstant(a2)) if sort.isInstanceOf[Heap.AddressSort] =>
//          println("case addrEq1: " + eq)
          meetAllWhere(key => key.addr == a1 || key.addr == a2, element,
                       LatticeElement.TOP)

        /** h1 === h2 (heap equality) */
        case eq@Eq(IConstant(h1@SortedConstantTerm(_, sort)),
                   IConstant(h2)) if sort.isInstanceOf[Heap.HeapSort] =>
//          println("case heapEq1: " + eq)
          meetAllWhere(key => key.heap == h1 || key.heap == h2, element,
                       LatticeElement.TOP)

        /** a1 =/= a2 (address inequality) */
        case eq@INot(Eq(IConstant(SortedConstantTerm(a1, sort)),
                        IConstant(a2)))
          if sort.isInstanceOf[Heap.AddressSort] =>
//          println("case addrNeq1: " + eq)
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
      print(s"Element for $a: ")
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
