/**
 * Copyright (c) 2011-2018 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.bottomup

import lazabs.prover.Tree

import scala.collection.mutable.{HashMap => MHashMap}

object Util {

  def toStream[A](f : Int => A) : Stream[A] =
    toStreamHelp(0, f)
  
  private def toStreamHelp[A](n : Int, f : Int => A) : Stream[A] =
    f(n) #:: toStreamHelp(n + 1, f)
  
  //////////////////////////////////////////////////////////////////////////////

  abstract sealed class Dag[+D] {
    def isEmpty : Boolean
    val size : Int

    def map[E](f : D => E) : Dag[E]
    def foreach[U](f : D => U) : Unit

    def toTree[B >: D] : Tree[B]
    def drop(n : Int) : Dag[D]
    def apply(n : Int) : D

    def zipWithIndex : Dag[(D, Int)] = zipWithIndexHelp(0)

    protected[Util]
      def zipWithIndexHelp(depth : Int) : Dag[(D, Int)]

    def zip[B](that : Dag[B]) : Dag[(D, B)]

    def updated[B >: D](updates : Map[Int, (B, List[Int])]) : Dag[B] =
      updatedHelp(0, updates)
    protected[Util]
      def updatedHelp[B >: D](depth : Int,
                              updates : Map[Int, (B, List[Int])]) : Dag[B]

    /**
     * Substitute nodes at given indexes with sub-dags. Each sub-dag
     * of size <code>n</code> can reference nodes <code>n+1, n+2, ...</code>,
     * which are then connected to the children of the original node.
     */
    def substitute[B >: D](insertedDags : Map[Int, Dag[B]]) : Dag[B] =
      substituteHelp(0, insertedDags)._1
    protected[Util]
      def substituteHelp[B >: D](depth : Int,
                                 insertedDags : Map[Int, Dag[B]])
                                : (Dag[B], List[Int])

    def head = apply(0)
    def tail = drop(1)

    def subdagIterator = new Iterator[DagNode[D]] {
      private var rem = Dag.this
      def hasNext = DagEmpty != rem
      def next = {
        val res = rem.asInstanceOf[DagNode[D]]
        rem = res.next
        res
      }
    }

    def iterator : Iterator[D] =
      for (DagNode(d, _, _) <- subdagIterator) yield d

    def incoming(n : Int) : Seq[(Int, Int)] = incomingIterator(n).toList
    def incomingIterator(n : Int) : Iterator[(Int, Int)] =
      for ((DagNode(_, children, _), i) <- subdagIterator.zipWithIndex;
           (c, ci) <- children.iterator.zipWithIndex;
           if (i + c == n)) yield (i, ci)

    def pathFromRoot(n : Int) : Seq[(Int, Int)] = {
      var res = List[(Int, Int)]()
      var k = n
      while (k > 0) {
        val p@(nextk, _) = incomingIterator(k).next
        res = p :: res
        k = nextk
      }
      res
    }

    def elimUnconnectedNodes : Dag[D] = elimUnconnectedNodesHelp(0, Set(0))._1

    protected[Util]
      def elimUnconnectedNodesHelp(depth : Int, refs : Set[Int])
                                  : (Dag[D], List[Boolean])

    def prettyPrint : Unit =
      for ((DagNode(d, children, _), i) <- subdagIterator.zipWithIndex)
        println("" + i + ": " + d +
                (if (children.isEmpty)
                   ""
                 else
                   (" -> " + (for (ind <- children) yield (i + ind)).mkString(", "))))

    def dotPrint(reverse : Boolean) : Unit = {
      println("digraph dag {")
      for ((DagNode(d, children, _), i) <- subdagIterator.zipWithIndex) {
        println("" + i + "[label=\"" + d + "\"];")
        for (c <- children)
          if (reverse)
            println("" + (i + c) + "->" + i + ";")
          else
            println("" + i + "->" + (i + c) + ";")
      }
      println("}")
    }
  }

  case class DagNode[+D](d : D, children : List[Int],
                         next : Dag[D]) extends Dag[D] {
    def isEmpty = false
    val size : Int = next.size + 1
    def map[E](f : D => E) : Dag[E] = {
      val newD = f(d)
      DagNode(newD, children, next map f)
    }
    def foreach[U](f : D => U) : Unit = {
      f(d)
      next foreach f
    }

    protected[Util]
      def zipWithIndexHelp(depth : Int) : Dag[(D, Int)] =
        DagNode((d, depth), children, next.zipWithIndexHelp(depth + 1))

    def drop(n : Int) : Dag[D] =
      if (n == 0) this else (next drop (n-1))

    def zip[B](that : Dag[B]) : Dag[(D, B)] =
      DagNode((d, that.asInstanceOf[DagNode[B]].d),
              children,
              next zip that.asInstanceOf[DagNode[B]].next)

    protected[Util]
       def elimUnconnectedNodesHelp(depth : Int, refs : Set[Int])
                                   : (Dag[D], List[Boolean]) =
      if (refs contains depth) {
        // this node has to be kept
        val (newNext, shifts) =
          next.elimUnconnectedNodesHelp(depth + 1,
                                        refs ++ (for (c <- children.iterator)
                                                 yield (depth + c)))
        (DagNode(d,
                 for (c <- children)
                 yield (1 + shifts.iterator.take(c-1).count(x => !x)),
                 newNext),
         false :: shifts)
      } else {
        // drop this node
        val (newNext, shifts) = next.elimUnconnectedNodesHelp(depth + 1, refs)
        (newNext, true :: shifts)
      }

    def apply(n : Int) : D =
      if (n == 0) d else next(n-1)
    def toTree[B >: D] : Tree[B] =
      Tree(d, for (i <- children) yield drop(i).toTree[B])

    protected[Util]
      def updatedHelp[B >: D](
                 depth : Int,
                 updates : Map[Int, (B, List[Int])]) : Dag[B] = {
      val newNext = next.updatedHelp(depth + 1, updates)
      (updates get depth) match {
        case None =>
          if (newNext eq next) this else DagNode(d, children, newNext)
        case Some((newD, newChildren)) =>
          DagNode(newD, newChildren, newNext)
      }
    }

    protected[Util]
      def substituteHelp[B >: D](depth : Int,
                                 insertedDags : Map[Int, Dag[B]])
                                : (Dag[B], List[Int]) = {
      val (newNext, gaps) = next.substituteHelp(depth + 1, insertedDags)
      val newChildren = for (c <- children) yield (c + firstNSum(gaps, c-1))

      (insertedDags get depth) match {
        case None =>
          (DagNode(d, newChildren, newNext), 0 :: gaps)

        case Some(subDag) => {
          def substChildren(dag : Dag[B]) : (Dag[B], Int) = dag match {
            case DagNode(dagD, dagChildren, dagNext) => {
              val (newDagNext, size) = substChildren(dagNext)
              val newDagChildren =
                for (c <- dagChildren)
                yield (if (c > size) (newChildren(c - size - 1) + size) else c)
              (DagNode(dagD, newDagChildren, newDagNext), size + 1)
            }
            case DagEmpty =>
              (newNext, 0)
          }
          
          (substChildren(subDag)._1, (subDag.size - 1) :: gaps)
        }
      }
    }
  }

  case object DagEmpty extends Dag[Nothing] {
    def isEmpty = true
    val size : Int = 0
    def map[E](f : Nothing => E) : Dag[E] = this
    def foreach[U](f : Nothing => U) : Unit = {}

    protected[Util]
      def zipWithIndexHelp(depth : Int) : Dag[(Nothing, Int)] = DagEmpty

    def drop(n : Int) : Dag[Nothing] = {
      if (n != 0)
        throw new IllegalArgumentException
      this
    }

    def zip[B](that : Dag[B]) : Dag[(Nothing, B)] = DagEmpty

    protected[Util]
      def elimUnconnectedNodesHelp(depth : Int, refs : Set[Int])
                                  : (Dag[Nothing], List[Boolean]) = (this, List())
    def apply(n : Int) : Nothing =
      throw new UnsupportedOperationException
    def toTree[B >: Nothing] : Tree[B] =
      throw new UnsupportedOperationException

    protected[Util]
      def updatedHelp[B >: Nothing](
               depth : Int,
               updates : Map[Int, (B, List[Int])]) : Dag[B] = this
    protected[Util]
      def substituteHelp[B >: Nothing](depth : Int,
                                       insertedDags : Map[Int, Dag[B]])
                                      : (Dag[B], List[Int]) = (this, List())
  }

  //////////////////////////////////////////////////////////////////////////////

  private def firstNSum(l : List[Int], n : Int) : Int = {
    var res = 0
    var i = 0
    var rem = l
    while (i < n && !rem.isEmpty) {
      res = res + rem.head
      rem = rem.tail
      i = i + 1
    }
    res
  }

  //////////////////////////////////////////////////////////////////////////////

  def show[D](d : Dag[D], name : String) : Unit = {
    if (!lazabs.GlobalParameters.get.pngNo) {
      val runTime = Runtime.getRuntime   
      val filename = if (lazabs.GlobalParameters.get.dotSpec)
                       lazabs.GlobalParameters.get.dotFile
                     else
                       "dag-graph-" + name + ".dot"
      val dotOutput = new java.io.FileOutputStream(filename)
      Console.withOut(dotOutput) {
        d.dotPrint(true)
      }
      dotOutput.close

      if (lazabs.GlobalParameters.get.eogCEX) {
        var proc = runTime.exec( "dot -Tpng " + filename + " -o " + filename + ".png" )
        proc.waitFor    
        proc = runTime.exec( "eog " + filename + ".png")
//    proc.waitFor
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  class UnionFind[D] extends Cloneable {
    private val parent = new MHashMap[D, D]
    private val rank   = new MHashMap[D, Int]

    def apply(d : D) : D = {
      val p = parent(d)
      if (p == d) {
        p
      } else {
        val res = apply(p)
        parent.put(d, res)
        res
      }
    }

    def makeSet(d : D) : Unit = {
      parent.put(d, d)
      rank.put(d, 0)
    }

    def union(d : D, e : D) : Unit = {
      val dp = apply(d)
      val ep = apply(e)
      
      if (dp != ep) {
        val dr = rank(dp)
        val er = rank(ep)
        if (dr < er) {
          parent.put(dp, ep)
        } else if (dr > er) {
          parent.put(ep, dp)
        } else {
          parent.put(ep, dp)
          rank.put(dp, dr + 1)
        }
      }
    }

    override def clone : UnionFind[D] = {
      val res = new UnionFind[D]
      res.parent ++= this.parent
      res.rank ++= this.rank
      res
    }

    override def toString : String = parent.toString
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Union-find specialised for integers ranging over <code>[0, card)</code>
   */
  class IntUnionFind(card : Int) extends Cloneable {
    private val parent : Array[Int] = (0 until card).toArray
    private val rank   : Array[Int] = new Array[Int] (card)

    def apply(d : Int) : Int = {
      val p = parent(d)
      if (p == d) {
        p
      } else {
        val res = apply(p)
        parent(d) = res
        res
      }
    }

    def union(d : Int, e : Int) : Unit = {
      val dp = apply(d)
      val ep = apply(e)
      
      if (dp != ep) {
        val dr = rank(dp)
        val er = rank(ep)
        if (dr < er) {
          parent(dp) = ep
        } else if (dr > er) {
          parent(ep) = dp
        } else {
          parent(ep) = dp
          rank(dp) = dr + 1
        }
      }
    }

    override def clone : IntUnionFind = {
      val res = new IntUnionFind(card)
      Array.copy(this.parent, 0, res.parent, 0, card)
      Array.copy(this.rank,   0, res.rank,   0, card)
      res
    }

    override def toString : String = "[" + (parent mkString ", ") + "]"
  }

}
