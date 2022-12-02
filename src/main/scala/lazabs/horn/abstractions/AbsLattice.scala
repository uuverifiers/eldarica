/**
 * Copyright (c) 2011-2016 Philipp Ruemmer and Pavle Subotic.
 * All rights reserved.
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

package lazabs.horn.abstractions

import scala.math.PartialOrdering

import ap.SimpleAPI
import ap.terfor.{ConstantTerm, TermOrder, TerForConvenience, Term, OneTerm}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.ReduceWithEqs
import ap.parser.{ITerm, IExpression, IFormula, IBoolLit, IVariable, InputAbsy2Internal}
import ap.util.{LRUCache, PeekIterator}
import ap.util.Timeout

import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet,
                                 HashMap => MHashMap, BitSet => MBitSet}
import scala.collection.immutable.BitSet
import scala.util.Random

// Defines an interface to lattices
trait AbsLattice
{
  type LatticeObject

  val latticeOrder : PartialOrdering[LatticeObject]
  val top, bottom : LatticeObject
  val arity : Int

  /** Does the lattice only contain one element? */
  def isUnit : Boolean = (top == bottom)

  def pp(o : LatticeObject) : String

  def join(x: LatticeObject, y: LatticeObject): LatticeObject
  def meet(x: LatticeObject, y: LatticeObject): LatticeObject

  /** Compute the direct parents/successors of an object */
  def succ(x: LatticeObject): Iterator[LatticeObject]
  /** Compute the direct children/predecessors of an object */
  def pred(x: LatticeObject): Iterator[LatticeObject]

  /** Compute the direct children/predecessors of an object,
    * with ascending cost. */
  def predCheapestFirst(x: LatticeObject): Iterator[LatticeObject]

  /** Compute the direct children/predecessors of an object,
    * in pseudo-random order. */
  def predRandom(x: LatticeObject)
                (implicit randGen : Random): Iterator[LatticeObject]

  /** A measure for the size of an object */
  def predNum(x: LatticeObject): Int
 
  /** Compute an element in between lower and upper */
  def middle(lower : LatticeObject, upper : LatticeObject)
            (implicit randGen : Random) : LatticeObject

  /** Compute the cost of an object. Cost is monotonic, bigger objects have
      larger cost. */
  def cost(obj : LatticeObject) : Int

  /** Try to eliminate atomic parts of the object that have cost larger than
      bound. In general, <code>result <= obj</code>, and for all
      <code>x <= obj</code> such that <code>cost(x) <= bound</code>,
      we have <code>x <= result</code>. */
  def removeExpensivePreds(obj : LatticeObject, bound : Int) : LatticeObject

  /** Assuming that <code>infeasible < feasible</code>,
      return an object such that <code>feasible = join(infeasible, result)</code>,
      and such that, whenever <code>x <= elem</code>, and <code>x</code> feasible, 
      it holds that <code>x >= result</code>. */
  def getDecrement(feasible : LatticeObject,
                   infeasible : LatticeObject) : LatticeObject

  // Create the composed relation R_A[xa, x] \circ R_B[x, xb] 
  def asRelation(obj : LatticeObject,  xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula]

  // Create the relations 
  def asRelation(obj : LatticeObject,  xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], 
                 xb : Seq[Seq[ITerm]]) : List[(IFormula, IFormula)]

  // Return a canonical object (whose relations are equivalent to the relations of o)
  def canonise(o : LatticeObject) : LatticeObject = o

  // The reduced lattice corresponding to this lattice
  val reducedLattice : AbsLattice

  //////////////////////////////////////////////////////////////////////////////

  def incomparable(mf : Seq[LatticeObject]) : Iterator[LatticeObject] =
    incomparable(top, mf)
    
  def incomparable(initialTopEl : LatticeObject,
                   mf : Seq[LatticeObject]) : Iterator[LatticeObject] = {
    val incompEls = new ArrayBuffer[LatticeObject]

    def incomparableHelp(topEl : LatticeObject,
                         mf : List[LatticeObject]) : Iterator[LatticeObject] =
      if (incompEls.exists(latticeOrder.lteq(topEl, _))) {
        Iterator.empty
      } else mf match {
        case List() =>
          Iterator single topEl
        case mfHead :: mfTail =>
          for (x <- incomparableBelow(topEl, mfHead);
               o <- incomparableHelp(x, mfTail)) yield o
      }

    for (o <- incomparableHelp(initialTopEl,
                               mf.sortBy(predNum(_)).toList)) yield {
      incompEls += o
      o
    }
  }

  /**
   * Compute a set S of objects <= topEl that are
   * (i) incomparable to comp, and
   * (ii) S has the property that for every object
   * o <= topEl and !(o <= comp), there is an element u in S such that
   * o <= u.
   * The result of the method is undefined for comp == bottom.
   */
  def incomparableBelow(topEl : LatticeObject,
                        comp : LatticeObject) : Iterator[LatticeObject]

  //////////////////////////////////////////////////////////////////////////////

  private class FeasibilityCache(isFeasible: LatticeObject => Boolean) {
    private val cachedFeasible, cachedInfeasible = new ArrayBuffer[LatticeObject]

    def apply(elem : LatticeObject) : Boolean = {
      val canon = canonise(elem)

      val feasibleIt = cachedFeasible.reverseIterator
      val infeasibleIt = cachedInfeasible.reverseIterator

      while (feasibleIt.hasNext && infeasibleIt.hasNext) {
        if (latticeOrder.lteq(feasibleIt.next, canon))
          return true
        if (latticeOrder.lteq(canon, infeasibleIt.next))
          return false
      }

      if (feasibleIt.hasNext &&
          feasibleIt.exists(e => latticeOrder.lteq(e, canon)))
        return true
      if (infeasibleIt.hasNext &&
          infeasibleIt.exists(e => latticeOrder.lteq(canon, e)))
        return false

      if (isFeasible(canon)) {
        cachedFeasible += canon
        true
      } else {
        cachedInfeasible += canon
        false
      }
    }
  }

  private class Timeouter(timeout : Long) {
    private val startTime = System.currentTimeMillis
    private var printedTimeout = false

    def apply =
      if (System.currentTimeMillis > startTime + timeout) {
        if (!printedTimeout) {
          if (lazabs.GlobalParameters.get.log)
            print(" TIMEOUT")
          printedTimeout = true
        }
        true
      } else {
        false
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  def cheapSearch(isFeasible: LatticeObject => Boolean,
                  timeout : Long = Int.MaxValue) : Seq[LatticeObject] = {
    val objs = search(isFeasible, timeout)
    if(objs.isEmpty) return Seq.empty
    val objsCost = objs.map(o => (o, cost(o)))
    val minEllst = objsCost.unzip._2 : Seq[Int]
    assert(!minEllst.isEmpty)
    val minEl = minEllst.min
    objsCost.filter{ case (v, x) => x == minEl}.unzip._1
  }


  /**
   * Compute minimal feasible elements w.r.t. the given
   * feasibility predicate (which has to be monotonic).
   * Optionally, a timeout in milliseconds can be specified;
   * if a timeout occurs, only minimal feasible elements
   * found up to that point are returned.
   *
   * Beware : starts from top unlike the paper
   */
  def search(isFeasible: LatticeObject => Boolean,
             timeout : Long = Int.MaxValue) : Seq[LatticeObject] = {
    implicit val randGen = new Random (654321)

    val timeIsOut = new Timeouter(timeout)
    val cheapIsFeasible = new FeasibilityCache(isFeasible)

    def minimize(elem : LatticeObject) : LatticeObject = {
      // Get the first feasible element
      val up = pred(elem).find(p => cheapIsFeasible(p)) match {
        case None => return elem
        case Some(f) => f
      }

      assert(up != bottom)
      val m = middle(bottom, up)
      if (cheapIsFeasible(m))
        minimize(m)
      else 
        minimize(up)
    }

    // Calculate minimal feasible for inc 
    def calcMinFeasSet(inc : Iterator[LatticeObject],
                       minFeasEls : Seq[LatticeObject]) : Seq[LatticeObject] = {
      val feasibleInc =
        for (o <- inc; if ({println(o); timeIsOut.apply || cheapIsFeasible(o)})) yield o

      if (feasibleInc.hasNext && !timeIsOut.apply) {
        val feasObj = minimize(feasibleInc.next)
        val newFeasEls = minFeasEls :+ feasObj
        println("new MF object:" + pp(feasObj))
        calcMinFeasSet(incomparable(newFeasEls), newFeasEls) // recurse
      } else {
        minFeasEls
      }
    }

    //val time = System.nanoTime;
    val allFeasibleAbs = 
    if (isFeasible(bottom)) {
      println("bottom abstraction is feasible")
      Seq(bottom)
    } else if (!isFeasible(top)) Seq()
    else{
      val mfe = minimize(top) // get initial min elem from the top
      println("MF object:" + pp(mfe))
      assert(mfe != bottom)
      val inc = incomparable(Seq(mfe)) // Get top level incomparable elements

      calcMinFeasSet(inc, Seq(mfe)) // Call calc minimal feasible
    }

    assert(allFeasibleAbs.filter( x => pred(x).exists( p => isFeasible(p))).isEmpty)
    allFeasibleAbs
  }


  private object TIME_IS_OUT extends Exception

  /**
   * Compute minimal feasible elements w.r.t. the given
   * feasibility predicate (which has to be monotonic).
   * Optionally, a timeout in milliseconds can be specified;
   * if a timeout occurs, only minimal feasible elements
   * found up to that point are returned.
   *
   * Beware : starts from top unlike the paper
   */
  def lSearch(isFeasible: LatticeObject => Boolean,
              timeout : Long = Int.MaxValue) : Seq[LatticeObject] = {
    implicit val randGen = new Random (765432)

    val timeIsOut = new Timeouter(timeout)
    val cheapIsFeasible = new FeasibilityCache(isFeasible)

    def cheapIsFeasibleWithTO(elem : LatticeObject) : Boolean =
      Timeout.withChecker { () =>
        if (timeIsOut.apply)
          Timeout.raise
      } {
        Timeout.catchTimeout {
          cheapIsFeasible(elem)
        } {
          case _ => throw TIME_IS_OUT
        }
      }

    def minimize(elem : LatticeObject,
                 glBot : LatticeObject,
                 minimalCost : Int) : Either[LatticeObject, LatticeObject] = {

      // newBot
      // new elem, new glbot
//     println("minimize")
//     println(elem)

      if (timeIsOut.apply) throw TIME_IS_OUT

      var learnedBottom = glBot
      var nextFeasible : Option[LatticeObject] = None

      val preds = predCheapestFirst(elem)
                  // predRandom(elem)
      while (!nextFeasible.isDefined && preds.hasNext) {
        val nextPred = preds.next
        if (latticeOrder.lteq(learnedBottom, nextPred)) {
          if (cheapIsFeasibleWithTO(nextPred)) {
            nextFeasible = Some(nextPred)
          } else {
            learnedBottom = join(learnedBottom, getDecrement(elem, nextPred))

            if (cost(learnedBottom) > minimalCost) {
//              println("PRUNING")
              return Right(learnedBottom)
            }
          
            if (cheapIsFeasibleWithTO(learnedBottom))
              return Left(learnedBottom)
          }
        }
      }

      nextFeasible match {
        case None =>
          // elem is an mfe
          if (cost(elem) > minimalCost)
            return Right(elem)
          else
            return Left(elem)
        case Some(nEl) => {
          val m = middle(learnedBottom, nEl)
          // if m is feasible - keep going down
          if (cheapIsFeasibleWithTO(m)){
            minimize(m, learnedBottom, minimalCost)
          } else { // if not feasible go up
            minimize(nEl, learnedBottom, minimalCost)
          }
        }
      }
    }

    // Calculate minimal feasible for inc 
    def calcMinFeasSet(inc : Iterator[LatticeObject], // incomparable elements
                       minFeasEls : Seq[LatticeObject], // minimal feasible set
                       costlyElements : Seq[LatticeObject],
                       topBound : LatticeObject,
                       currentCost : Int
                      ) : Seq[LatticeObject] = {
      if (lazabs.GlobalParameters.get.log)
        print(".")
/*      println("Cheapest MF objects:" + (minFeasEls map (pp _)).mkString(", "))
      println("Costly objects:" + (costlyElements map (pp _)).mkString(", "))
      println("current cost bound: " + currentCost) */

      val feasibleInc =
        for (o <- inc; if (timeIsOut.apply ||
                           (try {
                              cheapIsFeasibleWithTO(o)
                            } catch {
                              case TIME_IS_OUT => true
                            }))) yield o

      if (feasibleInc.hasNext && !timeIsOut.apply) {
        val (newMinFeasEls, newCostlyEls, newTopBound, newCost) = try {
          minimize(feasibleInc.next, bottom, currentCost) match {
            case Left(o) => {
              val oCost = cost(o)
              // found a cheap mfe
              if (oCost < currentCost) {
                if (lazabs.GlobalParameters.get.log) {
                  println
                  println("New cost bound: " + oCost)
                  print("Interpolation abstraction: " + pp(o) + " ")
                }
                (Seq(o), List(), removeExpensivePreds(topBound, oCost), oCost)
              } else {
                assert(oCost == currentCost)
                if (lazabs.GlobalParameters.get.log) {
                  println
                  print("Interpolation abstraction: " + pp(o) + " ")
                }
                (minFeasEls :+ o, costlyElements, topBound, currentCost)
              }
            }
            case Right(o) =>
              // this search direction is too costly
              (minFeasEls, costlyElements :+ o, topBound, currentCost)
          }
        } catch {
           case TIME_IS_OUT =>
             return minFeasEls
        }

        calcMinFeasSet(incomparable(newMinFeasEls ++ newCostlyEls),
                       newMinFeasEls, newCostlyEls, newTopBound, newCost)
      } else {
        minFeasEls
      }
    }

    //val time = System.nanoTime;
    val allFeasibleAbs = 
      if (cheapIsFeasible(bottom)) {
        if (lazabs.GlobalParameters.get.log)
          print("Interpolation abstraction: " + pp(bottom))
        Seq(bottom)
      } else if (!cheapIsFeasible(top)) {
        if (lazabs.GlobalParameters.get.log)
          print("Top interpolation abstraction is not feasible")
        Seq()
      } else {
        val Left(mfe) = try {
          minimize(top, bottom, cost(top))
        } catch {
           case TIME_IS_OUT =>
             return Seq()
        }

        val minCost = cost(mfe)
        val topBound = removeExpensivePreds(top, minCost)

        if (lazabs.GlobalParameters.get.log) {
          println("Cost bound: " + minCost)
          print("Interpolation abstraction: " + pp(mfe) + " ")
        }
        //assert(mfe != bottom && newBot > mfe)
      
        val inc = incomparable(topBound, Seq(mfe))
        calcMinFeasSet(inc, Seq(mfe), Seq(), topBound, minCost)
      }

//    assert(allFeasibleAbs.filter( x => pred(x).exists( p => isFeasible(p))).isEmpty)
    if (lazabs.GlobalParameters.get.log)
      println
    allFeasibleAbs
  }


  //////////////////////////////////////////////////////////////////////////////

  /**
   * Do a complete encoding of the the composed relation
   * R_A[xa, x] \circ R_B[x, xb] with the help of Boolean flags.
   * Returned are the flags, as well as a translator from flag
   * valuations to lattice elements.
   */
  def genBooleanEncoding(xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]],
                         p : SimpleAPI)
                        : (Seq[IFormula], Seq[Boolean] => LatticeObject)

}

////////////////////////////////////////////////////////////////////////////////

// Product lattice, inductive class

object ProductLattice {
  def apply[A <: AbsLattice, B <: AbsLattice](a : A, b : B) =
    new ProductLattice(a, b, false)
  def apply[A <: AbsLattice, B <: AbsLattice](a : A, b : B,
                                              conjunction : Boolean) =
    new ProductLattice(a, b, conjunction)
}

class ProductLattice[A <: AbsLattice, B <: AbsLattice] private (val a : A, val b : B,
                                                                conjunction : Boolean)
      extends AbsLattice {
  type LatticeObject = (a.LatticeObject, b.LatticeObject)

  override def toString =
    "" + a + (if (conjunction) " & " else " * ") + b

  def pp(o : LatticeObject) =
    a.pp(o._1) + (if (conjunction) " & " else ", ") + b.pp(o._2)

  val top = (a.top, b.top)
  val bottom = (a.bottom, b.bottom)

  // normal partial order
  val latticeOrder = new PartialOrdering[LatticeObject] {
    def tryCompare(x: LatticeObject, y: LatticeObject) =
      for (c1 <- a.latticeOrder.tryCompare(x._1, y._1);
           c2 <- b.latticeOrder.tryCompare(x._2, y._2);
           if (c1 * c2 != -1))
      yield (c1, c2) match {
        case (1, _) | (_, 1) => 1
        case (-1, _) | (_, -1) => -1
        case _ => 0
      }
 
    def lteq(x: LatticeObject, 
             y: LatticeObject) =
      a.latticeOrder.lteq(x._1, y._1) && b.latticeOrder.lteq(x._2, y._2)
  }

  val arity =
    if (conjunction) {
      assert(a.arity == b.arity)
      a.arity
    } else {
      a.arity + b.arity
    }

  def meet(x: LatticeObject, y: LatticeObject): LatticeObject =
      (a.meet(x._1, y._1), b.meet(x._2, y._2))

  def join(x: LatticeObject, y: LatticeObject): LatticeObject =
      (a.join(x._1, y._1), b.join(x._2, y._2))

  def removeExpensivePreds(obj : LatticeObject, bound : Int) : LatticeObject =
    (a.removeExpensivePreds(obj._1, bound), b.removeExpensivePreds(obj._2, bound))

  def getDecrement(feasible : LatticeObject,
                   infeasible : LatticeObject) : LatticeObject =
    if (feasible._1 == infeasible._1)
      (a.bottom, b.getDecrement(feasible._2, infeasible._2))
    else if (feasible._2 == infeasible._2)
      (a.getDecrement(feasible._1, infeasible._1), b.bottom)
    else
      bottom

  // normal order
  def succ(x: LatticeObject): Iterator[LatticeObject] =
    (for (as <- a.succ(x._1)) yield (as, x._2)) ++ (
     for (bs <- b.succ(x._2)) yield (x._1, bs))

  def pred(x: LatticeObject): Iterator[LatticeObject] =
    (for (ap <- a.pred(x._1)) yield (ap, x._2)) ++ (
     for (bp <- b.pred(x._2)) yield (x._1, bp))

  private def mergeCheapestFirst(aBase : a.LatticeObject,
                                 bBase : b.LatticeObject,
                                 aIt : Iterator[a.LatticeObject],
                                 bIt : Iterator[b.LatticeObject]) =
    new Iterator[LatticeObject] {
      val aPeek = PeekIterator(aIt)
      val bPeek = PeekIterator(bIt)

      val aCost = a.cost(aBase)
      val bCost = b.cost(bBase)

      def hasNext = aPeek.hasNext || bPeek.hasNext

      def next =
        if (aPeek.hasNext) {
          if (bPeek.hasNext &&
              a.cost(aPeek.peekNext) + bCost > aCost + b.cost(bPeek.peekNext)) {
            (aBase, bPeek.next)
          } else {
            (aPeek.next, bBase)
          }
        } else {
          (aBase, bPeek.next)
        }
    }

  def predCheapestFirst(x: LatticeObject) =
    mergeCheapestFirst(x._1, x._2,
                       a.predCheapestFirst(x._1),
                       b.predCheapestFirst(x._2))

  def predRandom(x: LatticeObject)
                (implicit randGen : Random) = new Iterator[LatticeObject] {
    val aIt = a.predRandom(x._1)
    val bIt = b.predRandom(x._2)

    def hasNext = aIt.hasNext || bIt.hasNext

    def next =
      if (!aIt.hasNext)
        (x._1, bIt.next)
      else if (!bIt.hasNext)
        (aIt.next, x._2)
      else if (randGen.nextBoolean)
        (aIt.next, x._2)
      else
        (x._1, bIt.next)
  }

  def predNum(x: LatticeObject): Int = a.predNum(x._1) + b.predNum(x._2)

  def middle(lower : LatticeObject, upper : LatticeObject)
            (implicit randGen : Random) : LatticeObject = {
    val fmid = a.middle(lower._1, upper._1)
    val smid = b.middle(lower._2, upper._2)
    (fmid, smid)
  }

  def cost(obj : LatticeObject) : Int =
    a.cost(obj._1) + b.cost(obj._2)

  def incomparableBelow(topEl : LatticeObject,
                        comp : LatticeObject) : Iterator[LatticeObject] =
    if (latticeOrder.lteq(topEl, comp))
      Iterator.empty
    else if (latticeOrder.lteq(comp, topEl))
      mergeCheapestFirst(topEl._1, topEl._2,
                         a.incomparableBelow(topEl._1, comp._1),
                         b.incomparableBelow(topEl._2, comp._2))
//      (for (x <- a.incomparableBelow(topEl._1, comp._1)) yield (x, topEl._2)) ++
//      (for (x <- b.incomparableBelow(topEl._2, comp._2)) yield (topEl._1, x))
    else
      Iterator single topEl

  def asRelation(obj : LatticeObject,
                 xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula] =
    if (conjunction)
      for ((f, g) <- a.asRelation(obj._1, xa, xb) zip b.asRelation(obj._2, xa, xb))
      yield (f & g)
    else
      a.asRelation(obj._1, xa.take(a.arity), xb.take(a.arity)) ++ 
      b.asRelation(obj._2, xa.drop(a.arity), xb.drop(a.arity))

  def asRelation(obj : LatticeObject,
                 xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]])
                : List[(IFormula, IFormula)] =
    if (conjunction)
      for (((f1, f2), (g1, g2)) <-
             a.asRelation(obj._1, xa, x, xb) zip b.asRelation(obj._2, xa, x, xb))
      yield (f1 & g1, f2 & g2)
    else
      a.asRelation(obj._1, xa.take(a.arity), x.take(a.arity), xb.take(a.arity)) ++ 
      b.asRelation(obj._2, xa.drop(a.arity), x.drop(a.arity), xb.drop(a.arity))

  def genBooleanEncoding(xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]], p : SimpleAPI)
                        : (Seq[IFormula], Seq[Boolean] => LatticeObject) =
    if (conjunction) {
      val (aFlags, aFun) = a.genBooleanEncoding(xa, xb, p)
      val (bFlags, bFun) = b.genBooleanEncoding(xa, xb, p)
      (aFlags ++ bFlags,
       flags => (aFun(flags take aFlags.size), bFun(flags drop aFlags.size)))
    } else {
      val (aFlags, aFun) = a.genBooleanEncoding(xa.take(a.arity), xb.take(a.arity), p)
      val (bFlags, bFun) = b.genBooleanEncoding(xa.drop(a.arity), xb.drop(a.arity), p)
      (aFlags ++ bFlags,
       flags => (aFun(flags take aFlags.size), bFun(flags drop aFlags.size)))
    }

  override def canonise(o : LatticeObject) : LatticeObject =
    (a.canonise(o._1), b.canonise(o._2))

  // The reduced lattice corresponding to this lattice
  lazy val reducedLattice : AbsLattice =
    new ProductLattice(a.reducedLattice, b.reducedLattice, conjunction)
}

////////////////////////////////////////////////////////////////////////////////

abstract class BitSetLattice(width : Int, name : String) extends AbsLattice {

  val arity : Int

  protected def pp(bit : Int) : String

  protected def bitCost(bit : Int) : Int

  //////////////////////////////////////////////////////////////////////////////

  type LatticeObject = BitSet

  def pp(o : LatticeObject) =
    (name match { case "" => ""; case n => n + ": " }) +
    "<" + (for (i <- o) yield pp(i)).mkString(", ") + ">"

  val latticeOrder = new PartialOrdering[LatticeObject] {
    def tryCompare(x: LatticeObject, y: LatticeObject) =
      (x subsetOf y, y subsetOf x) match {
        case (true, true)  => Some(0)
        case (true, false) => Some(-1)
        case (false, true) => Some(1)
        case _ => None
      }

    def lteq(x: LatticeObject, y: LatticeObject) = x subsetOf y
  }

  val top = BitSet((0 until width): _*)
  val bottom = BitSet.empty

  def meet(x : LatticeObject , y: LatticeObject) : LatticeObject = x intersect y
  def join(x: LatticeObject, y: LatticeObject) : LatticeObject  = x union y

  def removeExpensivePreds(obj : LatticeObject, bound : Int) : LatticeObject =
    obj filter (i => bitCost(i) <= bound)

  def getDecrement(feasible : LatticeObject,
                   infeasible : LatticeObject) : LatticeObject = {
    val step = feasible -- infeasible
    if (step.size == 1) step else bottom
  }

  def middle(lower : LatticeObject, upper : LatticeObject)
            (implicit randGen : Random) : LatticeObject = {
    val nelem = for (x <- upper;
                     if ( (lower contains x) || randGen.nextInt(100) < 80)) yield x
    assert(latticeOrder.lteq(bottom, nelem))
    nelem
  }

  def cost(obj : LatticeObject) : Int =
    (for (i <- obj.iterator) yield bitCost(i)).sum

  def incomparableBelow(topEl : LatticeObject,
                        comp : LatticeObject) : Iterator[LatticeObject] =
    if (latticeOrder.lteq(topEl, comp))
      Iterator.empty
    else if (latticeOrder.lteq(comp, topEl))
      for (t <- comp.iterator) yield (topEl - t)
    else
      Iterator single topEl

  def succ (obj: LatticeObject) : Iterator[LatticeObject] =
    for (t <- top.iterator; if (!(obj contains t))) yield (obj + t)

  def pred(obj: LatticeObject) : Iterator[LatticeObject] =
    for (t <- top.iterator; if (obj contains t)) yield (obj - t)

  lazy val objseqCostlyFirst =
    (0 until width).toArray sortBy { i => -bitCost(i) }

  def predCheapestFirst(obj: LatticeObject) : Iterator[LatticeObject ] =
    for (t <- objseqCostlyFirst.iterator; if (obj contains t)) yield (obj - t)

  def predRandom(x: LatticeObject)
                (implicit randGen : Random) = new Iterator[LatticeObject] {
    private val remaining = new MBitSet
    remaining ++= x

    def hasNext = !remaining.isEmpty

    def next = {
      val selected =
        if (remaining.size > 1) {
          val it = remaining.iterator
          for (_ <- 0 until randGen.nextInt(remaining.size))
            it.next
          it.next
        } else {
          remaining.head
        }
      remaining -= selected
      x - selected
    }
  }

  def predNum(x: LatticeObject): Int = x.size

  def genBooleanEncoding(xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]], p : SimpleAPI)
                        : (Seq[IFormula], Seq[Boolean] => LatticeObject) = {
    import p._
    val flags = createBooleanVariables(width)
    for (i <- top.iterator)
      !! (flags(i) ==> asRelation(BitSet(i), xa, xb).head)
    (flags,
     flagValues => BitSet((for ((v, i) <- flagValues.iterator.zipWithIndex;
                                if (v)) yield i).toSeq : _*))
  }
}

////////////////////////////////////////////////////////////////////////////////

object TermSubsetLattice {
  def apply(termsCosts : Seq[(ITerm, Int)], name : String = "") = {
    val objseq = termsCosts.unzip._1.toIndexedSeq
    val cmap = termsCosts.toMap
    new TermSubsetLattice(objseq, cmap, name)
  }
  def apply(objseq: Seq[ITerm], cmap: Map[ITerm, Int]) = {
    new TermSubsetLattice(objseq, cmap, "")
  }
}

class TermSubsetLattice private (objseq: Seq[ITerm],
                                 costMap : Map[ITerm, Int],
                                 _name : String)
      extends BitSetLattice(objseq.size, _name) {

  assert(costMap.keySet == objseq.toSet)

  override def toString = "TermSubsetLattice: " + (objseq mkString ", ")

  val arity = 1

  protected def pp(bit : Int) : String = objseq(bit).toString

  private val bitCostMap =
    (for ((t, i) <- objseq.iterator.zipWithIndex) yield (i, costMap(t))).toMap

  protected def bitCost(bit : Int) : Int = bitCostMap(bit)

  def getTerms(obj : LatticeObject) : Iterator[ITerm] =
    for ((t, i) <- objseq.iterator.zipWithIndex; if (obj contains i)) yield t

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula] = {
    import IExpression._
//    if (xa.isEmpty) return List(new IBoolLit(true))
    List(and(for ((t, i) <- objseq.iterator.zipWithIndex; if (obj contains i)) yield {
          subst(t, xa.head.toList, 0) === subst(t, xb.head.toList, 0)
        }))
  }

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]])
                : List[(IFormula, IFormula)] =
   List((asRelation(obj, xa, x).head, asRelation(obj, x, xb).head))

  //////////////////////////////////////////////////////////////////////////////

  private val term2Internal =
    (for (t <- objseq.iterator;
          intT = try {
            LinearCombination(InputAbsy2Internal(t, TermOrder.EMPTY),
                              TermOrder.EMPTY)
          } catch {
            // the term might contain operators that cannot directly
            // be translated to internal (like ite, eps)
            case _ : scala.MatchError => null
          };
          if (intT != null))
     yield (t -> intT)).toMap

  private val trivial =
    objseq forall (_.isInstanceOf[IVariable])

  private val cache = new LRUCache[LatticeObject, LatticeObject](10000)

  override def canonise(o : LatticeObject) : LatticeObject =
    if (trivial) {
      o
    } else cache(o) {
      import TerForConvenience._
      implicit val order = TermOrder.EMPTY

      val intTerms =
        (for (t <- getTerms(o);
              intT <- (term2Internal get t).iterator)
         yield intT).toList

      val reducer = ReduceWithEqs(intTerms === 0, order)
      val res = top filter { i => (o contains i) ||
                                  ((term2Internal get objseq(i)) exists {
                                     x => reducer(x).isZero
                                   }) }
//println("extending: size is " + res.size)
//println(o)
//println(res)
      res
    }

  // The reduced lattice corresponding to this lattice
  lazy val reducedLattice : AbsLattice =
    TermExtendingLattice(this)
}

////////////////////////////////////////////////////////////////////////////////

object TermIneqLattice {
  def apply(lowerBounds : Seq[(ITerm, Int)], name : String = "") =
    new TermIneqLattice(lowerBounds.unzip._1.toIndexedSeq,
                        lowerBounds.toMap,
                        name)
}

// Base case class
class TermIneqLattice private (lowerBounds: Seq[ITerm],
                               lowerCostMap : Map[ITerm, Int],
                               _name : String)
      extends BitSetLattice(lowerBounds.size, _name) {

  assert(lowerCostMap.keySet == lowerBounds.toSet)

  override def toString =
    "TermIneqLattice: " + lowerCostMap

  val arity = 1

  protected def pp(bit : Int) : String = " <= " + lowerBounds(bit)

  private val bitCostMap =
    (for ((t, i) <- lowerBounds.iterator.zipWithIndex)
     yield (i, lowerCostMap(t))).toMap

  protected def bitCost(bit : Int) : Int = bitCostMap(bit)

  def getTerms(obj : LatticeObject) : Iterator[ITerm] =
    for ((t, i) <- lowerBounds.iterator.zipWithIndex;
         if (obj contains i)) yield t

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula] = {
    import IExpression._
//    if (xa.isEmpty) return List(new IBoolLit(true))
    List(and(for (t <- getTerms(obj)) yield {
            subst(t, xa.head.toList, 0) <= subst(t, xb.head.toList, 0)
        }))
  }

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]])
                : List[(IFormula, IFormula)] =
   List((asRelation(obj, xa, x).head, asRelation(obj, x, xb).head))

  // The reduced lattice corresponding to this lattice
  val reducedLattice : AbsLattice = this
}

////////////////////////////////////////////////////////////////////////////////

object PredicateLattice {
  def apply(predicateCosts : Seq[(IFormula, Int)], name : String = "") =
    new PredicateLattice(predicateCosts.unzip._1.toIndexedSeq,
                         predicateCosts.toMap,
                         name)
}

// Base case class
class PredicateLattice private (predicates: Seq[IFormula],
                                costMap : Map[IFormula, Int],
                                _name : String)
      extends BitSetLattice(predicates.size, _name) {

  assert(costMap.keySet == predicates.toSet)

  override def toString =
    "PredicateLattice: " + costMap

  val arity = 1

  protected def pp(bit : Int) : String = predicates(bit).toString

  private val bitCostMap =
    (for ((t, i) <- predicates.iterator.zipWithIndex) yield (i, costMap(t))).toMap

  protected def bitCost(bit : Int) : Int = bitCostMap(bit)

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula] = {
    import IExpression._
//    if (xa.isEmpty) return List(new IBoolLit(true))
    List(and(for ((t, i) <- predicates.iterator.zipWithIndex; if (obj contains i)) yield {
          subst(t, xa.head.toList, 0) ==> subst(t, xb.head.toList, 0)
        }))
  }

  def asRelation(obj: LatticeObject,
                 xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]])
                : List[(IFormula, IFormula)] =
   List((asRelation(obj, xa, x).head, asRelation(obj, x, xb).head))

  // The reduced lattice corresponding to this lattice
  val reducedLattice : AbsLattice = this
}

////////////////////////////////////////////////////////////////////////////////

abstract class ExtendingLattice[BaseLattice <: AbsLattice](val baseLattice : BaseLattice)
                               extends AbsLattice {

  type LatticeObject = baseLattice.LatticeObject

  def pp(o : LatticeObject) = baseLattice.pp(o)

  /**
   * Has to be defined as a monotonic, extending, idempotent function
   * on the base lattice
   */
  def extendObject(o : LatticeObject) : LatticeObject

  val latticeOrder = baseLattice.latticeOrder
  val top = baseLattice.top
  val bottom = baseLattice.bottom
  val arity = baseLattice.arity

  def join(x: LatticeObject, y: LatticeObject) =
    extendObject(baseLattice.join(x, y))
  def meet(x: LatticeObject, y: LatticeObject) =
    baseLattice.meet(x, y)

  def removeExpensivePreds(obj : LatticeObject, bound : Int) : LatticeObject = obj

  def getDecrement(feasible : LatticeObject,
                   infeasible : LatticeObject) : LatticeObject = { assert(false); bottom }

  def succ(x: LatticeObject): Iterator[LatticeObject] = {
    val returned = new MHashSet[LatticeObject]
    for (o <- baseLattice.succ(x);
         extendedO = extendObject(o);
         if (returned add extendedO)) yield extendedO
  }

  protected def maximiseBelow(x : LatticeObject,
                              bound : LatticeObject) : LatticeObject = {
    val it = baseLattice.succ(x)
    while (it.hasNext) {
      val y = it.next
      if (latticeOrder.lt(y, bound)) {
        val extendedY = extendObject(y)
        if (latticeOrder.lt(extendedY, bound))
          return maximiseBelow(extendedY, bound)
      }
    }
    x
  }

  def pred(start: LatticeObject): Iterator[LatticeObject] = {
    val returned, explored = new MHashSet[LatticeObject]

//    def checkCorrectness(a : LatticeObject) =
//      assert(baseLattice.succ(a) forall {x => !latticeOrder.lteq(x, start) || extendObject(x) == start})

    def predHelp(x : LatticeObject) : Iterator[LatticeObject] = {
      for (y <- baseLattice.pred(x);
           if (explored add y);
           extendedY = extendObject(y);
           z <- {// println("x = " + x + "; y = " + y + "; extendedY = " + extendedY)
                 if (extendedY == start) {
                   predHelp(y)
                 } else if (extendedY == y) {
                   returned += y
                   Iterator single y
                 } else {
                   val maxiY = maximiseBelow(extendedY, start)
                   if (returned add maxiY)
                     Iterator single maxiY
                   else
                     Iterator.empty
                 }}) yield z
}

/*    println("computing pred for " + start)
    val res = predHelp(start).toList
    println(res)
    assert(
      (baseLattice.pred(start) forall { x => res exists { y => latticeOrder.lteq(y, x) } })
    )
    res.iterator */

    predHelp(start)
  }

  def predCheapestFirst(start: LatticeObject): Iterator[LatticeObject] =
    throw new UnsupportedOperationException

  def predRandom(x: LatticeObject)
                (implicit randGen : Random) : Iterator[LatticeObject] =
    throw new UnsupportedOperationException

/*  def incomparableBelow(topEl : LatticeObject,
                        comp : LatticeObject) : Iterator[LatticeObject] = {
    val returned = new MHashSet[LatticeObject]
    for (x <- baseLattice.incomparableBelow(topEl, comp);
         extendedX = {println(x); extendObject(x)};
         if ((returned add extendedX) &&
             latticeOrder.tryCompare(extendedX, comp) == None)) yield extendedX
  } */

  def predNum(x: LatticeObject): Int = baseLattice.predNum(x)
  def middle(lower : LatticeObject, upper : LatticeObject)
            (implicit randGen : Random) =
    extendObject(baseLattice.middle(lower, upper))
  def cost(obj : LatticeObject) : Int = baseLattice.cost(obj)

  def asRelation(obj : LatticeObject,
                 xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]]) : List[IFormula] =
    baseLattice.asRelation(obj, xa, xb)

  def asRelation(obj : LatticeObject,  xa : Seq[Seq[ITerm]], x : Seq[Seq[ITerm]], 
                 xb : Seq[Seq[ITerm]]) : List[(IFormula, IFormula)] =
    baseLattice.asRelation(obj, xa, x, xb)

  def genBooleanEncoding(xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]], p : SimpleAPI)
                        : (Seq[IFormula], Seq[Boolean] => LatticeObject) =
    throw new UnsupportedOperationException

  // The reduced lattice corresponding to this lattice
  val reducedLattice : AbsLattice = this
}

////////////////////////////////////////////////////////////////////////////////

case class TermExtendingLattice(_baseLattice : TermSubsetLattice)
                               extends ExtendingLattice(_baseLattice) {

  def extendObject(o : LatticeObject) : LatticeObject = baseLattice.canonise(o)

  def incomparableBelow(topEl : LatticeObject,
                        comp : LatticeObject) : Iterator[LatticeObject] = {
    val returned, explored = new MHashSet[LatticeObject]

//    def checkCorrectness(a : LatticeObject) =
//      assert(baseLattice.succ(a) forall {x => !latticeOrder.lteq(x, start) || extendObject(x) == start})

    def handlePred(y : LatticeObject) : Iterator[LatticeObject] = {
      val extendedY = extendObject(y)
      if (extendedY == topEl) {
        predHelp(y)
      } else if (extendedY == y) {
        returned += y
        Iterator single y
      } else {
        val maxiY = maximiseBelow(extendedY, topEl)
        if (returned add maxiY)
          Iterator single maxiY
        else
          Iterator.empty
      }
    }

    def predHelp(x : LatticeObject) : Iterator[LatticeObject] =
      for (y <- baseLattice.pred(x);
           if (explored add y);
           z <- handlePred(y)) yield z

/*    println("computing pred for " + start)
    val res = predHelp(start).toList
    println(res)
    assert(
      (baseLattice.pred(start) forall { x => res exists { y => latticeOrder.lteq(y, x) } })
    )
    res.iterator */

    for (t <- baseLattice.objseqCostlyFirst.iterator;
         if (comp contains t);
         y = topEl - t;
         if (explored add y);
         z <- handlePred(y);
         if (latticeOrder.tryCompare(z, comp) == None)) yield z
  }

}
