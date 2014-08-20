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

import ap.parser._
import IExpression._


object DepGraph {
  def apply(orig : Seq[HornClauses.Clause]) = new DepGraph(orig)
} 
class DepGraph(orig : Seq[HornClauses.Clause]) extends AbsGraph {
  override type Node = DepNode
  override type Edge = DepEdge
  
  val (preds,clauses,n,e) = {
    
    val s = new scala.collection.mutable.HashSet[Predicate]
    val p2n = new scala.collection.mutable.HashMap[Predicate,DepNode]
    val triple2e = new scala.collection.mutable.HashMap[Tuple3[Predicate,Predicate,HornClauses.Clause],DepEdge]
    
    def newNode(p : Predicate) = {
      val aux = new DepNode(p)
      p2n.update(p, aux)
      s += p
      aux
    }
    def node(p : Predicate) = {
      val aux = p2n.get(p)
      aux.getOrElse(newNode(p))
    }
    def newEdge(p : Predicate, p_head : Predicate, c : HornClauses.Clause) = {
      val n = node(p)
      val n_head = node(p_head)
      val aux = new DepEdge(n,n_head,c)
      triple2e.update((p,p_head,c), aux)
      aux
    }
    def edge(p : Predicate, p_head : Predicate, c : HornClauses.Clause) = {
      val aux = triple2e.get((p,p_head,c))
      aux.getOrElse(newEdge(p,p_head,c))
    }
    
    
    for (c@HornClauses.Clause(IAtom(p_head,_),body,_) <- orig)
      for (IAtom(p,_) <- body) edge(p,p_head,c)
    
    (s,orig,p2n,triple2e)
  } 
  
  override def nodes() : Iterable[Node] = n.values
  override def edges() : Iterable[Edge] = e.values
  
  override def filterPrefix(pref : Seq[Edge]) : Boolean = {
    val c = HornManipulate.inlineSequence(pref.map(_.c))
    !PrincessFlataWrappers.isSat(c.constraint)
  }
  
  class DepNode(p : Predicate) extends BaseNode {
    override def toString() = p.name
  }
  
  class DepEdge(from : DepNode, to : DepNode, c : HornClauses.Clause) extends BaseEdge(from, to) {
    def c() : HornClauses.Clause = c
    override def toString() = {
      "("+from+","+to+","+c+")"
    }
  }
  
}

object HornManipulate {
  
  // inline a sequence of Horn clauses
  def inlineSequence(cycle : Seq[HornClauses.Clause]) : HornClauses.Clause = {
    val i = cycle.reverseIterator
    var selfLoop = i.next
    
    // iteratively inline
    while (i.hasNext) {
      val c = i.next
      val toSubst : IAtom = selfLoop.body.find(a => a.pred == c.head.pred).get
      val (atoms,constr) = c.inline(toSubst.args)
      selfLoop = HornClauses.Clause(
          selfLoop.head, 
          (selfLoop.body ++ atoms).filterNot(_ == toSubst), 
          selfLoop.constraint &&& constr)
    }
    selfLoop
  }
  
}

object HornAccelerate {
  
  def accelerate(orig : Seq[HornClauses.Clause]) : Seq[HornClauses.Clause] = {
    
    (new HornAccelerate(orig)).accelerate
    
  }
}

class HornAccelerate(orig : Seq[HornClauses.Clause]) {

  // split the clauses into lower-bound, upper-bound, and dependent clauses
  val (lb,ub,dep) = {
    val (a1,aux) = orig.partition( c => c.body.size == 0 )
    val (a2,a3) = aux.partition( c => c.head match {
      case IAtom(HornClauses.FALSE, Nil) => true
      case _ => false
    } )
    (a1,a2,a3)
  }
  
  // predicate-dependency graph
  val dg = DepGraph(orig)
  
  // create unique signature (list of variables) for each predicate
  val p2signature : Map[Predicate,IAtom] = (for (p <- dg.preds) yield (
    p -> 
    ( IAtom( p, for (x <- 1 to p.arity) yield i(new ConstantTerm(p.name+"_"+x)).asInstanceOf[IConstant]) )
    )).toMap

  // under-approximation of the least solution
  // a solution for a predicate is represented as a horn clause with no predicate in the body
  var p2sol = new scala.collection.mutable.HashMap[Predicate,HornClauses.Clause]
  var solQueue : Set[Predicate] = Set()
  for (p <- dg.preds) {
    p2sol.update(p, createSol(p, IBoolLit(false)))
  }
  lbImpliedSolution

  private def createSol(p : Predicate, f : IFormula) : HornClauses.Clause = {
    HornClauses.Clause(p2signature(p),List(), f)
  }
  private def updateSol(p : Predicate, f : IFormula) {
    val h = p2sol(p)
    val newSol = h.constraint ||| f
    p2sol.update(p, createSol(p, newSol))
  }
  
  // under-approximation implied by lower-bound clauses
  private def lbImpliedSolution = { 
    var aux : List[Predicate] = List()
    for (c <- lb) {
      val p = c.head.pred
      aux = p :: aux
      val (_,f) = c.inline(p2signature(p).args)
      updateSol(p,f)
    }
    solQueue = aux.toSet
  }
  private def updateSolutionWith(c : HornClauses.Clause) = {
    var constr = c.constraint
    for (a <- c.body) {
      val (_,aux) = p2sol(a.pred).inline(a.args)
      constr = constr &&& aux
    }
    constr = constr &&& (c.head.args === p2signature(c.head.pred).args)
    updateSol(c.head.pred,constr)
  }
  
  // compute a non-empty under-approximation of the least solution of the system for given predicates 
  def solutionsFor(ps : Iterable[Predicate]) = {
    def clausesWithBody = {
      dg.clauses.filter( c => c.body.exists( a => solQueue.contains(a.pred) ) )
    }
    def isFalse(f : IFormula) = {
      f match {
        case IBoolLit(false) => true
        case _ => false
      }
    }
    def someEmpty = {
      ps.exists(p => isFalse(p2sol(p).constraint))
    }
    
    while (someEmpty) {
      var aux : List[Predicate] = List()
      for (c <- clausesWithBody) {
        aux = c.head.pred :: aux
        updateSolutionWith(c)
      }
      solQueue = aux.toSet
    }
  }
  
  // input: p1(t1) /\ ... /\ pn(tn) /\ phi => p1(t)
  // output: p1(Z) /\ psi => p1(Zp)
  def selfDep2accelerated(c : HornClauses.Clause) : Option[HornClauses.Clause] = {
    val aux = (n : Int, pref : String, suf : String ) => {
      for (x <- 1 to n) yield  i(new ConstantTerm(pref+x+suf)).asInstanceOf[IConstant]
    }
    val a_head = c.head
    val p_head = c.head.pred
    val a_new_head = IAtom(p_head,aux(p_head.arity,"Z","'"))
    val a_new_body = IAtom(p_head,aux(p_head.arity,"Z",""))
    
    // substitute predicates p2,...,pn with under-approximations of solutions
    // to obtain p1(x1) /\ psi => p1(y1)
    val needSol = (for (a <- c.body) yield a.pred).toSet - c.head.pred
    solutionsFor(needSol)
    var constr = c.constraint
    // deal with the head
    constr = constr &&& (a_head.args === a_new_head.args) 
    // deal with the body
    var found = false
    for (a <- c.body) {
      if (!found && a.pred == c.head.pred) {
        found = true
        constr = constr &&& (a.args === a_new_body.args)
      } else {
        val (_,aux) = p2sol(a.pred).inline(a.args)
        constr = constr &&& aux
      }
      
    }
    assert(found)
    
    // normalize constraint (eliminate variables, DNF)
    val var_bnd = SymbolCollector constants (a_new_head & a_new_body)
    def normalize = {
      val var_all = var_bnd ++ (SymbolCollector constants constr)
      val var_elim = var_all -- var_bnd
      PrincessFlataWrappers.transformFormula(constr, var_elim, var_bnd)
    }
    val cNorm = HornClauses.Clause(a_new_head,List(a_new_body),normalize)
    
    // next, try to accelerate
    val res_acc = PrincessFlataWrappers.accelerate(cNorm.constraint, var_bnd)
    
    val ret : Option[HornClauses.Clause] = res_acc match {
      case None => None
      case Some(acc) => {
        val cAcc = HornClauses.Clause(a_new_head,List(a_new_body),acc)
        Some(cAcc)
      }
    }
    ret
  }
  
  def accelerate() : Seq[HornClauses.Clause] = {
    
    val sccs = dg.Tarjan.nontrivial
    
    var hc : List[HornClauses.Clause] = Nil
    
    // for each nontrivial scc  
    for (scc <- sccs) {
      // find arbitrary cycle
//      val n = scc(0)
//      val cycle : Seq[this.dg.DepEdge] = dg.anyPath(n, n, scc).get
      val cycles = for (n <- scc.iterator;
                        c <- dg.anyPath(n, n, scc).iterator) yield c
      if (cycles.hasNext) {
        val cycle = cycles.next
        val hcycle = for (e <- cycle) yield e.c
        // inline it and obtain a horn clause of the form P /\ ... => P
        val hSelfLoop = HornManipulate.inlineSequence(hcycle)
        // try to infer a clause of the form P(Z) /\ phi(Z,Zp) => P(Zp)
        // where phi is octagon and accelerate it
        val hAcc = selfDep2accelerated(hSelfLoop)
      
        if (hAcc.isDefined) 
          hc = hAcc.get :: hc
      }
    }
    
    hc ::: dg.clauses.toList
  }
    
}

object PrincessFlataWrappers {
  
  import lazabs.prover.PrincessAPI_v1
  private val api = new PrincessAPI_v1
  import api._
  type MHashMap[A,B] = scala.collection.mutable.HashMap[A,B]
  
  def transformFormula(f : IFormula, elim : scala.collection.Set[ConstantTerm], keep : scala.collection.Set[ConstantTerm]) : IFormula = {
    
    val replacement = new MHashMap[ConstantTerm, ITerm]
    // identity for "free" variable
    for (c <- keep) { 
      replacement.put(c, i(c)) 
    }
    // arbitrary bijective mapping from the set of n "bound" variables to de Bruijn indices {0..n-1}
    var x = 0
    for (c <- elim) { 
      replacement.put(c, v(x))
      x += 1
    }
    // construct a formula with explicit quantifiers
    var fExist =  ConstantSubstVisitor(f, replacement.toMap)
    for (_ <- 0 to x-1) {
      fExist = IQuantified(Quantifier.EX,fExist)
    }
    // eliminate quantifiers
    val fExistElim = elimQuans(fExist, keep.toSeq)
    // transform to DNF
    val fDnf = dnfSimplify(fExistElim, keep.toSeq)
    fDnf
  }
  
  def isSat(f : IFormula) : Boolean = {
    api.isSat(f, (SymbolCollector constants f).toSeq)
  }
  
  import lazabs.ast.ASTree._
  import lazabs.nts._
  import lazabs.prover._
  import scala.collection.mutable.LinkedHashMap
  def accelerate(f : IFormula, var_all : scala.collection.Set[ConstantTerm]) : Option[IFormula] = {
    
    val symbolMap_p2e = (for (v <- var_all) yield (v, "sc_"+v.name)).toMap
    
    val e = PrincessWrapper.formula2Eldarica(f,symbolMap_p2e,false)
    
    val accEld = FlataWrapper.accelerate(List(List(e)),AccelerationStrategy.PRECISE) match {
      case Some(e: Expression) => e
      case None => return None
    }
    
    // retrieve Eldarica representation and a symbol map
    val (List(acc),symbolMap_e2p) = PrincessWrapper.formula2Princess(List(accEld))
    
    val accElim = elimQuans(acc.asInstanceOf[IFormula], symbolMap_e2p.values.toSeq)
    
    // ensure consistency with original symbols by renaming
    val replacement = new MHashMap[ConstantTerm, ITerm]
    for (v <- var_all) {
      if (symbolMap_e2p.contains("sc_"+v.name))
        replacement.put(symbolMap_e2p("sc_"+v.name), v)
    }
    var accElimRen = ConstantSubstVisitor(accElim, replacement.toMap)
    
    Some(accElimRen.asInstanceOf[IFormula])
  }
}
