/**
 * Copyright (c) 2011-2014 Filip Konecny. All rights reserved.
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

abstract class AbsGraph { thisGraph =>
  type Node <: BaseNode
  type Edge <: BaseEdge
  
  def nodes : Iterable[Node]
  def edges : Iterable[Edge]
  
  def outgoing(n : Node) = edges.filter(e => e.from == n)
  def incoming(n : Node) = edges.filter(e => e.to == n)
  def selfloops(n : Node) = edges.filter(e => e.from == n && e.to == n)
  
  class BaseNode
  
  class BaseEdge(from : Node, to : Node) {
    def from() : Node = from
    def to() : Node = to
  }
    
  
  /////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////
  ///////// Tarjan SCC algorithm
  
  private class TData {
    val n2inx = new scala.collection.mutable.HashMap[Node,Int]
    val n2link = new scala.collection.mutable.HashMap[Node,Int]
    
    for (n <- nodes) yield {
      n2inx.update(n,-1)
      n2link.update(n,-1)
    }
    
    def inx(n : Node, v : Int) : Unit = n2inx.update(n,v)
    def inx(n : Node) : Int = n2inx(n)
    def link(n : Node, v : Int) : Unit = n2link.update(n,v)
    def link(n : Node) : Int = n2link(n)
    
    def processed(n : Node) = n2inx(n) >= 0
  }
  object Tarjan {
    def apply() = {
      val t = new Tarjan
      t.sccs
    }
    def nontrivial = {
      apply().filter(scc => scc.size > 1 || thisGraph.selfloops(scc(0)).size > 0)
    }
    def trivial = {
      apply().filter(scc => scc.size == 1 && thisGraph.selfloops(scc(0)).size == 0)
    }
    
  }
  private class Tarjan {
    
    val d = new TData
    val S = new scala.collection.mutable.Stack[Node]
    var index = 0
    
    val sccs = new scala.collection.mutable.ListBuffer[scala.collection.mutable.ListBuffer[Node]]
    
    for (n <- nodes) yield {
      if (!d.processed(n)) strongConnect(n)
    }
    
    def strongConnect(v : Node) : Unit = {
      d.inx(v,index)
      d.link(v,index)
      index += 1
      S.push(v)
      
      for (e <- thisGraph.outgoing(v)) {
        val w = e.to
        if (!d.processed(w)) {
          strongConnect(w)
          d.link(v, d.link(v) min d.link(w))
        } else if (S.contains(w)) {
          d.link(v, d.link(v) min d.inx(w))
        }
      }
      
      if (d.link(v) == d.inx(v)) {
        val scc = new scala.collection.mutable.ListBuffer[Node]
        sccs += scc
        var b = true 
        while (b) {
          val w = S.pop
          scc += w
          b = w != v
        }
      }
    }    
  }
  
  
  def filterPrefix(pref : Seq[Edge]) : Boolean = false
  
  // finds a path 'from' --> 'to' that traverses only nodes in 'via'
  // TODO: filter infeasible paths
  def anyPath(from : Node, to : Node, via : Iterable[Node]) : Option[Seq[Edge]] = {
    val s = via.toSet + from + to
    val b = new scala.collection.mutable.ListBuffer[Node]
    val seen = new scala.collection.mutable.HashSet[Node]
    val m = new scala.collection.mutable.HashMap[Node,Edge]
    
    def construct(from : Node, last : Edge) : Seq[Edge] = {
      var ret = last :: Nil
      var e = last
      while (e.from != from) {
        e = m(e.from)
        ret = e :: ret
      }
      ret
    }
    def filter(from : Node, last : Edge) : Boolean = {
      if (from == last.from) {
        false
      } else {
        filterPrefix(construct(from,last))
      }
    }
    
    b += from
    var found = false
    while (!found && b.nonEmpty) {
      val n = b.remove(0)
      for (e <- this.outgoing(n).filter(e => s.contains(e.to))) {
        if (!seen.contains(e.to) && !filter(from,e)) {
          seen.add(e.to)
          b += e.to
          m.update(e.to, e)
          if (e.to == to)
            found = true
        }
      }
    }
    if (found) {
      Some(construct(from,m(to)))
    } else {
      None
    }
  }

  
}
