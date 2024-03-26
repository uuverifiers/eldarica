package lazabs.horn.preprocessor

import ap.parser.IExpression.{ConstantTerm, Eq, Predicate}
import ap.parser._
import ap.theories.Heap
import ap.theories.Heap.{HeapFunExtractor, HeapSort}
import ap.types.SortedConstantTerm
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.preprocessor.AbstractAnalyser.AbstractTransformer
import lazabs.horn.preprocessor.PropagatingPreprocessor.InliningAbstractDomain

import scala.collection.immutable.BitSet
import scala.collection.mutable.{HashMap => MHashMap, Set => MSet}

object HeapAddressUpdateSitesAnalysis {
  /**
   * Collects update sites for all [[ap.theories.Heap.AddressSort]] terms as a
   * set from predicate indices to ???
   * @requires at most one update per clause - as guaranteed by
   *           [[ClauseSplitterFuncsAndUnboundTerms]].
   */
  class UpdateSitesDomain extends InliningAbstractDomain {
    private[preprocessor]
    case class HeapAddressIndPair(heapInd : Int,
                                  addrInd : Int,
                                  theory  : Heap)

    override val name : String = "analysing heap address update sites"

    // int *p;
    // p = 0;
    // p = alloc
    // p = write
    // h' = write(h, a, o), next(s) = a
    //
    // Sites can be either uninitialized ptr decls -> id = -1
    //                     null ptr                -> id = 0
    //                     an update               -> id > 0

    //

    private[preprocessor]
    trait LatticeElement {
      def join(that : LatticeElement) : LatticeElement
      def meet(that : LatticeElement) : LatticeElement
    }
    // Lattice is the powerset of clause indices ++ three special values
    // 1) allocated but not coming from any updates (valid)
    // 2) null
    // 3) not yet allocated
    private[preprocessor]
    case class LatticeValue(value : BitSet) extends LatticeElement {
      def join(that : LatticeElement) = that match {
        case LatticeTop => LatticeTop
        case LatticeValue(v) => LatticeValue(this.value union v)
      }

      def meet(that : LatticeElement) = that match {
        case LatticeTop => this
        case LatticeValue(v) => LatticeValue(this.value intersect v)
      }

      override def toString : String = "{" + value.mkString(",") + "}"
    }
    // this is not needed, top is finite
    private[preprocessor]
    case object LatticeTop extends LatticeElement {
      def join(that : LatticeElement) = this
      def meet(that : LatticeElement) = that
    }
    object LatticeElement {
      val bottom : LatticeElement = LatticeValue(BitSet.empty)
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

    case class HeapAddressPair(heap   : ConstantTerm,
                               addr   : ConstantTerm,
                               theory : Heap)

    /**
     * This is the map whose fixed point (LUB) will be the head element
     * this one is also in terms of constant terms rather than arg indices.
     */
    val localElementMap = new MHashMap[HeapAddressPair, LatticeElement]
    private val nullAddrs    : MSet[ConstantTerm] = MSet()
    private val notNullAddrs : MSet[ConstantTerm] = MSet()

    override def transformerFor(clause : HornClauses.Clause) =
      new AbstractTransformer[Element] {
        /**
         * Helper functions
         */
        def updateLocalMap(key  : HeapAddressPair,
                           elem : LatticeElement) : Boolean = {
          val meetValue = localElementMap.getOrElse(key, LatticeTop) meet elem
          localElementMap.put(key, meetValue)
          if (meetValue == LatticeElement.bottom) {
            println(
              "contradiction for " + "(" + key.heap + "," + key.addr + ")")
            false
          }
          else {
            println("(" + key.heap + "," + key.addr + ") -> " + meetValue)
            true
          }
        }

        // updates all keys containing the passed heap
        def udpateAllPairsWithHeap(h    : ConstantTerm,
                                   elem : LatticeElement) : Boolean =
          localElementMap.filter(pair => pair._1.heap == h).keys.
            forall(updateLocalMap(_, elem))

        // updates all keys containing the passed addr
        def udpateAllPairsWithAddr(a    : ConstantTerm,
                                   elem : LatticeElement) : Boolean =
          localElementMap.filter(pair => pair._1.addr == a).keys.
            forall(updateLocalMap(_, elem))

        def handleAddressEquality(term : ConstantTerm, term1 : ConstantTerm) : Boolean =
          ???
        def handleAddressInequality(term  : SortedConstantTerm,
                                    term1 : ConstantTerm) : Boolean =
          ???

        val conjuncts = LineariseVisitor(
          Transform2NNF(clause.constraint), IBinJunctor.And)

        override def transform(bodyValues : Seq[Element]) : Element = {
          if (bodyValues contains None) { // a body element has a contradiction
            println("bodyVals has None")
            return None
          }

          localElementMap.clear

          for ((bodyAtom, bodyElement) <- clause.body zip bodyValues;
               (pair, pairValue) <- bodyElement.get) {
            val IConstant(heapTerm) = bodyAtom.args(pair.heapInd)
            val IConstant(addrTerm) = bodyAtom.args(pair.addrInd)
            if (!updateLocalMap(
              HeapAddressPair(heapTerm, addrTerm, pair.theory), pairValue))
              return None
          }

          // 2nd step: collect all possible pairs from the head atom, and fill
          // in the localElementMap. This is required since we have cases
          // like nullAddr(a), where we do not know which <h,a> pair to update
          for (IConstant(addrTerm@SortedConstantTerm(_, aSort)) <- clause.head.args
               if aSort.isInstanceOf[Heap.AddressSort];
               IConstant(heapTerm@SortedConstantTerm(_, hSort)) <- clause.head.args
               if hSort.isInstanceOf[Heap.HeapSort]) {
            val theory = hSort.asInstanceOf[HeapSort].heapTheory
            if (!updateLocalMap(HeapAddressPair(heapTerm, addrTerm, theory),
                                LatticeTop))
              return None
          }

          // a map from the original heap to the newly allocated addr
          val heapAllocAddrMap = new MHashMap[ConstantTerm, ConstantTerm]
          println("/" * 80 + "\nclause: " + clause.toPrologString)

          // analyze the constraint and calculate the fixed point
          var outputChanged : Boolean = true
          while(outputChanged) {
            outputChanged = false
            val oldMap = localElementMap.clone
            for (f <- conjuncts) {
              f match {
                // nullAddr() = a
                case Eq(IFunApp(fun@HeapFunExtractor(heap), _), IConstant(a))
                  if fun == heap.nullAddr =>
                  println("case null = " + a)
                  if (!(nullAddrs contains a)) {
                    nullAddrs += a
                    outputChanged = true
                  }
                  for (key <- localElementMap.keys.filter(_.addr == a))
                    if (!updateLocalMap(key, LatticeValue(BitSet(0))))
                      return None

                // valid(h, a) // todo ignore?
//                case IAtom(pred@Heap.HeapPredExtractor(heap),
//                           Seq(IConstant(h), IConstant(a))) if pred == heap.isAlloc =>
//                  println("case valid" + HeapAddressPair(h, a, heap))
//                  if (!updateLocalMap(HeapAddressPair(h, a, heap), ValidElem))
//                    return None
//                  if (!(notNullAddrs contains a)) {
//                    if(nullAddrs contains a) return None
//                    notNullAddrs += a
//                    outputChanged = true
//                  }

                // !valid(h, a) // todo ignore?
//                case INot(IAtom(pred@Heap.HeapPredExtractor(heap),
//                                Seq(IConstant(h), IConstant(a)))) if pred == heap.isAlloc =>
//                  println("case !valid(" + h + ", " + a + ")")
//                  if(!updateLocalMap(HeapAddressPair(h, a, heap), NullOrNotAllocElem))
//                    return None

                // write(h1, _, _) = h2
                case Eq(IFunApp(fun@HeapFunExtractor(heap),
                                Seq(IConstant(h1), _, _)), IConstant(h2))
                  if fun == heap.write =>
                  println("case write(" + h1 + ",_,_) = " + h2)
//                  if (!handleHeapEquality(h1, h2)) return None
                   ???

                // allocAddr(h,_) = a
                case Eq(IFunApp(fun@HeapFunExtractor(heap),
                                Seq(IConstant(h), _)), IConstant(a))
                  if fun == heap.allocAddr =>
                  println("case allocAddr(" + h + ",_) = " + a)
                  ???
//                  if (!updateLocalMap(HeapAddressPair(h, a, heap), NotAllocElem))
//                    return None
//                  if (!udpateAllPairsWithAddr(a, ValidOrNotAllocElem))
//                    return None
//                  if (!(heapAllocAddrMap contains h)) {
//                    heapAllocAddrMap += ((h, a))
//                    outputChanged = true
//                  }
//                  if (!(notNullAddrs contains a)) {
//                    if(nullAddrs contains a) return None
//                    notNullAddrs += a
//                    outputChanged = true
//                  }

                // allocHeap(h1,_) = h2
                case Eq(IFunApp(fun@HeapFunExtractor(heap),
                                Seq(IConstant(h1), _)), IConstant(h2))
                  if fun == heap.allocHeap =>
                  println("case allocHeap(" + h1 + ",_) = " + h2)
                  ???
//                  heapAllocAddrMap get h1 match {
//                    case Some(a) =>
//                      println("  address found for " + h1 + ": " + a)
//                      // h1 and h2 are equal everywhere except a
//                      //if (!handleHeapEquality(h1, h2, List(a))) return None
//                      // todo: we cannot equate addresses by only excluding a, as there might be other addresses equal to a
//                      // todo: whose meet might go down the wrong path of the tree (e.g. from ValidOrNotAlloc to NotAlloc)
//                      // todo: instead of to Valid. Can we somehow solve this by finding the equivalence class of a? or by removing those earlier?
//                      // h2 is valid in a
//                      if (!updateLocalMap(HeapAddressPair(h2, a, heap), ValidElem))
//                        return None
//                    // h1 is not yet alloc in a (handled in allocAddr case)
//                    //updateLocalMap(HeapAddressPair(h1, a, heap), NotAllocElem)
//                    case _ => println("  alloc address not found for " + h1)
//                    // nothing
//                  }

                // alloc(h1,o) = AllocResHeap(h2, a)
                case Eq(IFunApp(fun1@HeapFunExtractor(heap),
                                Seq(IConstant(h1), IConstant(o))),
                        IFunApp(fun2, Seq(IConstant(h2), IConstant(a))))
                  if fun1 == heap.alloc && fun2 == heap.allocResCtor =>
                  println("case alloc(" + h1 + "," + o + ") = " +
                            "AllocResHeap(" + h2 + "," + a + ")")
                  ???
//                  if (!updateLocalMap(HeapAddressPair(h2, a, heap), ValidElem))
//                    return None

                // emptyHeap() = h
                case Eq(IFunApp(fun@Heap.HeapFunExtractor(heap), _),
                        IConstant(h))
                  if fun == heap.emptyHeap =>
                  println("case emptyHeap")
//                  if (!udpateAllPairsWithHeap(h, NullOrNotAllocElem)) return None // i.e., invalid
                ???

                // a1 === a2 (both are addresses)
                case Eq(IConstant(a1@SortedConstantTerm(_, sort)),
                        IConstant(a2)) if sort.isInstanceOf[Heap.AddressSort] =>
                  println("case addrEq1: " + f)
                  for (List(p1, p2) <- List(a1,a2).permutations) {
                    if ((nullAddrs contains p1) && !(nullAddrs contains p2)) {
                      nullAddrs += p2
                      outputChanged = true
                    }
                  }
                  if (!handleAddressEquality(a1, a2)) return None

                // a1 =/= a2 (both are addresses)
                case INot(Eq(IConstant(SortedConstantTerm(a1, sort)),
                             IConstant(a2)))
                  if sort.isInstanceOf[Heap.AddressSort] =>
                  println("case addrNeq1: " + f)
                  for (List(p1, p2) <- List(a1,a2).permutations) {
                    if ((nullAddrs contains p1) && !(notNullAddrs contains p2)) {
                      if (nullAddrs contains p2) return None // contradiction
                      notNullAddrs += p2
                      outputChanged = true
                    }
                  }
                  if (!handleAddressInequality(a1, a2)) return None

                // h1 === h2 (both are heaps)
                case Eq(IConstant(SortedConstantTerm(h1, sort)),
                        IConstant(h2)) if sort.isInstanceOf[Heap.HeapSort] =>
                  println("case heapEq.1")
//                  if (!handleHeapEquality(h1, h2)) return None

                // h1 === h2 (both are heaps)
                case Eq(IConstant(h1), IConstant(SortedConstantTerm(h2, sort)))
                  if sort.isInstanceOf[Heap.HeapSort] =>
                  println("case heapEq.2")
//                  if (!handleHeapEquality(h1, h2)) return None

                case f =>
                  println("undhandled case: " + f)
                // nothing
              }
            }
//            if (!(oldMap equals localDefinednessMap)) {
//              outputChanged = true
//              println("-"*80)
//              println(localDefinednessMap)
//              println("-"*80)
//            }
          }

//          // a map to convert from terms to head argument indices
//          val term2HeadArgInd = term2AtomArgInd(head)
//
//          // convert localDefinednessMap to the element for the head
//          // (for the pairs that exist in the head)
//          Some (
//            (for ((HeapAddressPair(h, a, theory), elem) <- localDefinednessMap
//                  if term2HeadArgInd.contains(h) && term2HeadArgInd.contains(a)) yield {
//              (HeapAddressIndPair(term2HeadArgInd(h), term2HeadArgInd(a), theory), elem)
//            }).toMap
//            )

          ???
        }
      }

    override def inline(a : IAtom, value : Element) : (IAtom, IFormula) = {
      ???
    }
    override def augmentSolution(sol : IFormula, value : Element) : IFormula = {
      ???
    }
  }
}