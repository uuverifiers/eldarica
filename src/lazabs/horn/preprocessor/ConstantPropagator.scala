/**
 * Copyright (c) 2018-2020 Philipp Ruemmer. All rights reserved.
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
import ap.theories.Heap.{AddressSort, HeapSort}
import ap.theories.{ADT, TheoryRegistry}
import ap.types.{MonoSortedIFunction,SortedConstantTerm}
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.Util.{IntUnionFind, UnionFind}

import scala.collection.mutable.{ArrayBuffer, LinkedHashMap, HashMap => MHashMap}

object SimplePropagators {
  import HornClauses.Clause
  import SymbolSplitter.ClausePropagator
  import IExpression.{Predicate, ConstantTerm}
  import AbstractAnalyser.{AbstractDomain, AbstractTransformer}
  import PropagatingPreprocessor.InliningAbstractDomain

  /**
   * Abstract domain for constant propagation
   */
  class ConstantPropDomain extends InliningAbstractDomain {
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
   * Abstract domain for equality propagation
   */
  class EqualityPropDomain extends InliningAbstractDomain {
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
   * Abstract domain for (heap, address) definedness propagation
   * Is address "a" valid in heap "h"?
   */
  class HeapDefinednessDomain extends InliningAbstractDomain {

    import ap.theories.Heap

    private def getElemFromVal(value : Int) : LatticeElement = {
      value match {
        case 0 => BottomElem
        case 1 => NullElem
        case 2 => ValidElem
        case 3 => NotAllocElem
        case 4 => NullOrValidElem
        case 5 => NullOrNotAllocElem
        case 6 => ValidOrNotAllocElem
        case 7 => UnknownElem
      }
    }

    private[preprocessor] class LatticeElement(val value: Char) {
      def join(that: LatticeElement): LatticeElement =
        getElemFromVal(this.value | that.value)

      def meet(that: LatticeElement): LatticeElement =
        getElemFromVal(this.value & that.value)

      override def toString: String = value.toInt.toString
    }

    private case object BottomElem          extends LatticeElement(0) // 000
    private case object NullElem            extends LatticeElement(1) // 001
    private case object ValidElem           extends LatticeElement(2) // 010
    private case object NotAllocElem        extends LatticeElement(4) // 100
    private case object NullOrValidElem     extends LatticeElement(3) // 011
    private case object NullOrNotAllocElem  extends LatticeElement(5) // 101
    private case object ValidOrNotAllocElem extends LatticeElement(6) // 110
    private case object UnknownElem         extends LatticeElement(7) // 111

    private[preprocessor] case class HeapAddressIndPair(heapInd: Int, addrInd: Int)
    type Element = Option[Map[HeapAddressIndPair, LatticeElement]]

    val name = "heap-definedness"

    def bottom(p: Predicate): Element = None

    def isBottom(b: Element): Boolean = b.isEmpty

    def join(a: Element, b: Element): Element =
      a match {
        case None => b
        case Some(aMap) => b match {
          case None => a
          case Some(bMap) =>
            // if the pair is only present in a or b, then their join becomes the
            // top element, i.e., we don't know anything about this combination
            Some(for ((key, aVal) <- aMap if bMap contains key) yield
              (key, aVal join bMap(key)))
        }
      }

    def transformerFor(clause: Clause) = new AbstractTransformer[Element] {
      import IExpression._

      //////////////////////////////////////////////////////////////////////////
      // helper objects, classes, functions etc., move out?
      object ExtendedHeapFunExtractor {
        def unapply(fun: IFunction): Option[Heap] =
          (TheoryRegistry lookupSymbol fun) match {
            case Some(t: Heap) => Some(t)
            case Some(_: ADT) if fun.isInstanceOf[MonoSortedIFunction] =>
              val sortedFun = fun.asInstanceOf[MonoSortedIFunction]
              // we are only interested in newHeap(ar : AllocRes) and newAddr(ar)
              sortedFun.resSort match {
                case s: Heap.HeapSort =>
                  if (sortedFun == s.heapTheory.newHeap)
                    Some(s.heapTheory)
                  else None
                case s: Heap.AddressSort =>
                  if (sortedFun == s.heapTheory.newAddr)
                    Some(s.heapTheory)
                  else None
                case t if sortedFun.arity == 2 => // check for AllocRes constructor
                  sortedFun.argSorts.head match {
                    case s: Heap.HeapSort =>
                      if (t == s.heapTheory.AllocResSort)
                        Some(s.heapTheory)
                      else None
                    case _ => None
                  }
                case _ => None
              }
            case _ => None
          }
      }
      // helper for handling heap equality, returns false for contradiction
      def handleHeapEquality (h1 : ConstantTerm, h2 : ConstantTerm) : Boolean = {
        val subMap =
          localDefinednessMap.filter(e => e._1.heap == h1  ||
            e._1.heap == h2)
        val handledAddresses = new ArrayBuffer[ConstantTerm]
        for ((key, elem) <- subMap
             if !(handledAddresses contains key.addr)) {
          handledAddresses += key.addr
          val otherKey =
            if (key.heap == h1)
              HeapAddressPair(h2, key.addr)
            else
              HeapAddressPair(h1, key.addr)
          val meetValue = subMap.getOrElse(otherKey, UnknownElem) meet elem
          if (meetValue == BottomElem) {
            println("contradiction!")
            return false
          } else {
            localDefinednessMap.put(key, meetValue)
            localDefinednessMap.put(otherKey, meetValue)
          }
        }
        true
      }
      case class HeapAddressPair(heap: ConstantTerm, addr: ConstantTerm)
      //////////////////////////////////////////////////////////////////////////

      val Clause(head, body, constraint) = clause

      // this is the map whose fixed point (LUB) will be the head element
      // this one is also in terms of constant terms rather than arg indices.
      private val localDefinednessMap =
        new MHashMap[HeapAddressPair, LatticeElement]

      // updates localDefinednessMap using the meet operation
      def updateLocalMap (key : HeapAddressPair, elem : LatticeElement) {
        localDefinednessMap.put(key,
          localDefinednessMap.getOrElse(key, UnknownElem) meet elem)
      }

      private val conjuncts =
        LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)

      // generate the output element using localDefinednessMap
      // map and the body elements (corresponding to body predicates)
      def transform(bodyVals: Seq[Element]): Element = {
        if (bodyVals exists (_.isEmpty)) { // a body element has a contradiction
          println("bodyVals has None")
          return None
        }
        // initialize localDefinednessMap
        // 1st step: collect and meet all information from the bodyVals
        // maps the <heap,address> term pairs to the meet of LatticeElements
        // that are extracted from the bodyVals
        for ((bodyAtom, bodyElement) <- body zip bodyVals;
             (pair, pairValue) <- bodyElement.get) {
          val IConstant(heapTerm) = bodyAtom.args(pair.heapInd)
          val IConstant(addrTerm) = bodyAtom.args(pair.addrInd)
          updateLocalMap(HeapAddressPair(heapTerm, addrTerm), pairValue)
        }
        // 2nd step: collect all possible pairs from the head atom, and fill
        // in the localDefinednessMap. This is required since we have cases
        // like nullAddr(a), where we do not know which <h,a> pair to update
        for (IConstant(SortedConstantTerm(addrTerm, aSort)) <- head.args
             if aSort.isInstanceOf[Heap.AddressSort];
             IConstant(SortedConstantTerm(heapTerm, hSort)) <- head.args
             if hSort.isInstanceOf[Heap.HeapSort])
          updateLocalMap(HeapAddressPair(heapTerm, addrTerm), UnknownElem)

        var outputChanged : Boolean = true
        // analyze the constraint and calculate the fixed point
        while(outputChanged) {
          val oldMap = localDefinednessMap.clone
          for (f <- conjuncts) {
              f match {
                // a = nullAddr()
                case Eq(IConstant(a), IFunApp(fun@ExtendedHeapFunExtractor(heap), _))
                  if fun == heap.nullAddr =>
                  println("case null.1")
                  for (key <- localDefinednessMap.keys.filter(_.addr == a))
                    localDefinednessMap.put(key,
                      localDefinednessMap(key) meet NullElem)

                // nullAddr() = a
                case Eq(IFunApp(fun@ExtendedHeapFunExtractor(heap), _), IConstant(a))
                  if fun == heap.nullAddr =>
                  println("case null.2")
                  for (key <- localDefinednessMap.keys.filter(_.addr == a))
                    localDefinednessMap.put(key,
                      localDefinednessMap(key) meet NullElem)

                // valid(h, a)
                case IAtom(pred@Heap.HeapPredExtractor(heap),
                Seq(IConstant(h), IConstant(a))) if pred == heap.isAlloc =>
                  println("case valid")
                  val key = HeapAddressPair(h, a)
                  localDefinednessMap.put(key,
                    localDefinednessMap(key) meet ValidElem)

                // !valid(h, a)
                case INot(IAtom(pred@Heap.HeapPredExtractor(heap),
                Seq(IConstant(h), IConstant(a)))) if pred == heap.isAlloc =>
                  println("case valid")
                  val key = HeapAddressPair(h, a)
                  localDefinednessMap.put(key,
                    localDefinednessMap(key) meet NullOrNotAllocElem)

                // write(h1, _, _) = h2
                case Eq(IFunApp(fun@ExtendedHeapFunExtractor(heap),
                                Seq(IConstant(h1), _, _)), IConstant(h2))
                  if fun == heap.write =>
                  println("case write.1")
                  if (!handleHeapEquality(h1, h2)) return None

                // h2 = write(h1, _, _)
                case Eq(IConstant(h2),
                        IFunApp(fun@ExtendedHeapFunExtractor(heap),
                                Seq(IConstant(h1), _, _)))
                  if fun == heap.write =>
                  println("case write.2")
                  if (!handleHeapEquality(h1, h2)) return None

                // AllocRes(h2,a) = alloc(h1,_)
                case Eq(IFunApp(fun1, Seq(IConstant(
                SortedConstantTerm(h2, h2Sort)), IConstant(a))),
                        IFunApp(fun2@ExtendedHeapFunExtractor(heap),
                                     Seq(IConstant(h1), _)))
                  if h2Sort == heap.HeapSort && fun2 == heap.alloc =>
                  // todo : this check can probably be done better
                  println("case alloc.1")
                  ???
                // alloc(h1,_) = AllocRes(h2,a)
                case Eq(IFunApp(fun2@ExtendedHeapFunExtractor(heap),
                                Seq(IConstant(h1), _)),
                        IFunApp(fun1, Seq(IConstant(SortedConstantTerm(
                                            h2, h2Sort)), IConstant(a))))
                  if h2Sort == heap.HeapSort && fun2 == heap.alloc =>
                  // todo : this check can probably be done better
                  // todo: can we extract allocResADT functions from heap theory?
                  println("case alloc.2")
                  ???

                // AllocRes(h,a) = ar / alloc(h,a) = ar
                case Eq(IFunApp(ExtendedHeapFunExtractor(heap),
                                Seq(IConstant(h), IConstant(a))),
                        IConstant(SortedConstantTerm(_, sort)))
                  if sort == heap.AllocResSort =>
                  println("case AllocRes.1")
                  ???
                // ar = AllocRes(h,a) / ar = alloc(h,a)
                case Eq(IConstant(SortedConstantTerm(_, sort)),
                IFunApp(ExtendedHeapFunExtractor(heap),
                Seq(IConstant(h), IConstant(a))))
                  if sort == heap.AllocResSort =>
                  println("case AllocRes.2")
                  ???

                // newHeap(ar) = h
                case Eq(IFunApp(fun,
                                Seq(IConstant(SortedConstantTerm(ar, arSort)))),
                        IConstant(SortedConstantTerm(h, hSort)))
                  // todo: below check would be easier if we could check for newHeap
                  if hSort.isInstanceOf[Heap.HeapSort] &&
                     arSort == hSort.asInstanceOf[Heap.HeapSort].
                       heapTheory.AllocResSort =>
                  println("case newHeap.1")
                  ???
                // h = newHeap(ar)
                case Eq(IConstant(SortedConstantTerm(h, hSort)),
                        IFunApp(fun,
                                Seq(IConstant(SortedConstantTerm(ar, arSort)))))
                  if hSort.isInstanceOf[Heap.HeapSort] &&
                    arSort == hSort.asInstanceOf[Heap.HeapSort].
                      heapTheory.AllocResSort =>
                  println("case newHeap.2")
                  ???

                // newAddr(ar) = a
                case Eq(IFunApp(fun,
                                Seq(IConstant(SortedConstantTerm(ar, arSort)))),
                        IConstant(SortedConstantTerm(a, aSort)))
                  // todo: below check would be easier if we could check for newHeap
                  if aSort.isInstanceOf[Heap.AddressSort] &&
                    arSort == aSort.asInstanceOf[Heap.AddressSort].
                      heapTheory.AllocResSort =>
                  println("case newAddr.1")
                  ???
                // a = newAddr(ar)
                case Eq(IConstant(SortedConstantTerm(a, aSort)),
                        IFunApp(fun,
                                Seq(IConstant(SortedConstantTerm(ar, arSort)))))
                  if aSort.isInstanceOf[Heap.AddressSort] &&
                    arSort == aSort.asInstanceOf[Heap.AddressSort].
                      heapTheory.AllocResSort =>
                  println("case newAddr.2")
                  ???

                // h = emptyHeap()
                case Eq(IConstant(h),
                        IFunApp(fun@ExtendedHeapFunExtractor(heap), _))
                  if fun == heap.emptyHeap =>
                  println("case emptyHeap.1")
                  ???
                // emptyHeap() = h
                case Eq(IFunApp(fun@ExtendedHeapFunExtractor(heap), _),
                        IConstant(h))
                  if fun == heap.emptyHeap =>
                  println("case emptyHeap.2")
                  ???

                // a1 == a2 (both are addresses)
                case Eq(IConstant(SortedConstantTerm(a1, sort)),
                        IConstant(a2)) if sort.isInstanceOf[Heap.AddressSort] =>
                  println("case addrEq")
                  ???

                // h1 == h2 (both are heaps)
                case Eq(IConstant(SortedConstantTerm(h1, sort)),
                        IConstant(h2)) if sort.isInstanceOf[Heap.HeapSort] =>
                  println("case heapEq")
                  ???

                // ar1 == ar2 (both are allocation results)
                //case Eq(IConstant(SortedConstantTerm(ar1, sort)),
                //        IConstant(ar2)) if ... how to get AllocResSort? =>
                //  println("case heapEq")
                //  ???

                case f =>
                  println("undhandled case: " + f)
                // nothing
              }
            }
            outputChanged = !(oldMap equals localDefinednessMap)
        }

        // a map to convert from terms to head argument indices
        val term2HeadArgInd : Map[ConstantTerm, Int] =
          (for ((IConstant(arg), ind) <- head.args zipWithIndex) yield {
            (arg, ind)
          }).toMap

        // convert localDefinednessMap to the element for the head
        Some (
          (for ((HeapAddressPair(h, a), elem) <- localDefinednessMap) yield {
            (HeapAddressIndPair(term2HeadArgInd(h), term2HeadArgInd(a)), elem)
          }).toMap
        )
      }
    }
    import IExpression._

    def inline(a: IAtom, value: Element): (IAtom, IFormula) = {
      case class PairInfo(heapTerm : IConstant, addrTerm : IConstant,
                          heapTheory : Heap)
      def extractPairInfo (pair : HeapAddressIndPair) : PairInfo = {
        val addrTerm@IConstant(SortedConstantTerm(_, sort)) = a.args(pair.addrInd)
        val heapTerm@IConstant(_) = a.args(pair.heapInd)
        val heapTheory = sort.asInstanceOf[Heap.AddressSort].heapTheory
        PairInfo(heapTerm, addrTerm, heapTheory)
      }

      var newConstraint : IFormula = IBoolLit(true)
      value match {
        case None =>
          // this clause can be deleted, it is not reachable
          return (a, false)
        case Some(map) =>
          for((pair, elem) <- map) {
            val PairInfo(addrTerm, heapTerm, theory) = extractPairInfo(pair)
            val nullAddr = theory.nullAddr
            val valid = theory.isAlloc
            elem match {
              case UnknownElem => // top, no information
              case NullOrValidElem =>
              // add constraint a === nullAddr() || valid(h,a) ?
                newConstraint = newConstraint &&&
                  ((addrTerm === nullAddr()) ||| valid(heapTerm, addrTerm))
              case NullOrNotAllocElem =>  // a.k.a. invalid
                newConstraint = newConstraint &&&
                  INot(valid(heapTerm, addrTerm))
              case ValidOrNotAllocElem =>  // a.k.a. not null
                newConstraint = newConstraint &&& addrTerm =/= nullAddr()
              case NullElem =>
                newConstraint = newConstraint &&&
                  (addrTerm === nullAddr()) &&& INot(valid(heapTerm, addrTerm))
              case ValidElem =>
                newConstraint = newConstraint &&& valid(heapTerm, addrTerm)
              case NotAllocElem =>
                newConstraint = newConstraint &&& // not sure about this case
                  INot(valid(heapTerm, addrTerm))
                ???
              case _ => // bottom
            }
          }
      }
      (a, newConstraint)
    }

    def augmentSolution(sol: IFormula, value: Element): IFormula =
      value match {
        case None => sol
        case Some(map) => ???
      }
  }
//////////////////////////////////////////////////////////////////////////////

  /**
   * Abstract analyser instantiated to perform constant propagation.
   */
  def ConstantPropagator =
    new PropagatingPreprocessor(new ConstantPropDomain)

  /**
   * Abstract analyser instantiated to perform equality propagation.
   */
  def EqualityPropagator =
    new PropagatingPreprocessor(new EqualityPropDomain)

  /**
   * Abstract analyser instantiated to perform heap definedness propagation.
   */
  def HeapDefinednessPropagator =
    new PropagatingPreprocessor(new HeapDefinednessDomain)
}
