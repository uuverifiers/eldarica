/**
 * Copyright (c) 2011-2014 Hossein Hojjat. All rights reserved.
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

package lazabs.refine

import lazabs.ast.ASTree._
import lazabs.cfg._
import lazabs.art._
import lazabs.nts.AccelerationStrategy._
import lazabs.art.RTreeMethods._
import lazabs.utils.Manip._
import lazabs.prover.PrincessWrapper._

object RefineAccelerate {
  
  /**
   * gets the index of a loop in a path
   */
  def getLoopIndex(path: List[(RNode,Label)]): Int = path.indexWhere(_._2 match {
    case TransitiveClosure(_,_) =>
      true
    case _ => false
  })

  /**
   * It looks for repeated subpaths and labels the repeated subpaths with TransitiveClosure
   */
  def findRepetitivePaths(path: List[(RNode,Label)]): List[(RNode,Label)] = {
    var suffixes = new Array[List[(RNode,Label)]](path.size)
    for (i <- 0 until path.size)
      suffixes(i) = path.takeRight(path.size - i)
    var i, j = 0
    var startLoopIndex,finishLoopIndex = 0
    var found = false
    while((i < suffixes.size) && !found) {
      j = i + 1
      while((j < (i + 1 + suffixes(i).size / 2)) && !found) {
        if(suffixes(i).take(j - i).map(x => (x._1.getCfgId,x._2)) == suffixes(j).take(j - i).map(x => (x._1.getCfgId,x._2))) {
          found = true
          startLoopIndex = i
          finishLoopIndex = j
        }
        j = j + 1
      }
      i = i + 1
    }
    if(found) {
      println("dynamic acceleration")
      val loop = path.slice(startLoopIndex,finishLoopIndex)
      val label = TransitiveClosure(loop.map(_._2),loop.tail.map(x => CFGVertex(x._1.getCfgId)))
      (path.take(startLoopIndex) ::: List((path(startLoopIndex)._1,label)) ::: path.slice(2*finishLoopIndex-startLoopIndex,path.size))
    }
    else path
  }
  
  /**
   * get formulas of a path leading to error
   */
  def getPathToErrorFormula(path: List[(RNode,Label)]): List[Expression] = {
    (path.zip(path.tail).map(el => getFormula(el._1._1,el._2._1,el._1._2)) :+ getFormula(path.last._1,errorNode,path.last._2)).map(shortCircuit)    
  }
  
  /**
   * get formulas of a path
   */
  def getPathFormula(path: List[(RNode,Label)], end: RNode): List[Expression] = {
    (path.zip(path.tail).map(el => getFormula(el._1._1,el._2._1,el._1._2)) :+ getFormula(path.last._1,end,path.last._2)).map(shortCircuit)    
  }
  
  var getFormula : ((RNode,RNode,Label) => Expression) = ((_,_,_) => BoolConst(false))
  var errorNode: RNode = RNode(-1, -1, Set())
  var log: Boolean = false
    /**
   * Replace transitive closure by approximation
   * @return 1) the list of formulas containing approximation, 2) the formula for acceleration, 3) preciseness of the result 
   */
  def approximatePath(path: List[(RNode,Label)],method: AccelerationStrategy): (List[Expression],Expression,Boolean) = {
    val loopIndex = getLoopIndex(path)
    if(loopIndex < 0) return (getPathToErrorFormula(path),BoolConst(false),true)
    var precise = false
    var acceleratedExpr: Expression = BoolConst(false)
    val prefix = if(loopIndex == 0) List(BoolConst(true)) else path.slice(0,loopIndex).zip(path).map(el => getFormula(el._1._1,el._2._1,el._1._2))
    ((path.zip(path.tail).map (el => el._1._2 match {
      case TransitiveClosure(t,_) =>
        val (v: Expression, p: Boolean) = lazabs.nts.FlataWrapper.accelerate(lazabs.cfg.AccelerationRule.label2lists(t.reduceLeft(Sequence(_,_))),method,prefix)
        precise = p
        acceleratedExpr = lazabs.prover.PrincessWrapper.elimQuantifiers(v)
        acceleratedExpr
      case _ => getFormula(el._1._1,el._2._1,el._1._2)
    }) :+ getFormula(path.last._1,errorNode,path.last._2)).map(shortCircuit),acceleratedExpr,precise) 
  }

  /**
   * Gets the spurious path and returns an inductive interpolant if accelerable
   */
  def apply(wholePath: List[(RNode,Label)], infeasibleSuffixIndex: Int, getFormula: (RNode,RNode,Label) => Expression,errorNode: RNode, underApproximate: Boolean, log: Boolean): 
      (List[RNode],collection.mutable.Map[CFGVertex,List[(Expression,List[Int])]]) = {
    this.getFormula = getFormula
    this.errorNode = errorNode
    this.log = log
    val infeasibleSuffix = wholePath.drop(infeasibleSuffixIndex)
    var removalPath = infeasibleSuffix
    var newPredicatesMap = collection.mutable.Map[CFGVertex,List[(Expression,List[Int])]]().empty
    val pathRest = wholePath.slice(0,infeasibleSuffixIndex)
    val repetitivePath = findRepetitivePaths(infeasibleSuffix)
    //if(repetitivePath.head._1.getId == -1)  // there are global variables inside Scala input
    //  rTree.transitions += (repetitivePath.head._1 -> (rTree.transitions.getOrElse(repetitivePath.head._1, Set.empty) + RAdjacent(repetitivePath.head._2,repetitivePath.tail.head._1)))    
    if(getLoopIndex(repetitivePath) >= 0) {
      val loopId = if(getLoopIndex(repetitivePath) >= 0) repetitivePath(getLoopIndex(repetitivePath))._1.getId
      val (formulas,e:Expression, precise: Boolean) = approximatePath(repetitivePath,OVER_APPROX)
      if(precise)
        exactAcc
      val sPath = pathRest ::: (repetitivePath.map(_._1).zip(formulas.map(Transfer(_))))
      val parent: Map[RNode,(RNode,Label)] = (((pathRest ::: repetitivePath).tail.map(_._1) :+ errorNode).zip(sPath)).toMap
      def localGetFormula(r1: RNode,r2: RNode,l: Label): Expression = {  // the function returns the approximation function in the place of the loop
        val rr = ((if(pathRest.size == 0) List() else pathRest.map(_._1).zip(getPathFormula(pathRest,repetitivePath.head._1))) ::: repetitivePath.map(_._1).zip(formulas)) :+ (errorNode,BoolConst(false))
        rr.zip(rr.tail).find {
          case (a,b) => 
            (a._1 == r1) && (b._1 == r2)
        } match {
          case Some(ss) => ss._1._2
          case None =>
            BoolConst(false)
        }
      }
      val (newSpur,newPath) = isSpurious(errorNode,parent,localGetFormula,List())
      newPredicatesMap = (newSpur,precise) match {
        case (false,true) =>
          stopTimer
          println("The program has a bug")
          report
          sys.exit(0)
        case (false,false) =>
          println("Retreating from over-approximation")
          unsuccessfulOverAcc
          if(underApproximate) {
            println("under-approximation")
            val (uFormulas,uAccExpr,_) = approximatePath(repetitivePath,UNDER_APPROX)
            refinement(repetitivePath.map(_._1).zip(uFormulas),repetitivePath(getLoopIndex(repetitivePath))._1.getId,repetitivePath(getLoopIndex(repetitivePath))._2)
          } else {
            refinement(infeasibleSuffix.map(_._1).zip(getPathToErrorFormula(infeasibleSuffix)))
          }
          //reconstructTree(path.map(_._1))
        case _ =>
          if(!precise)
            successfulOverAcc
          removalPath = if(wholePath.indexWhere(_ == newPath.head) >= 0)
            wholePath.slice(wholePath.indexWhere(_ == newPath.head),wholePath.size) else infeasibleSuffix
          val newLoopIndex = newPath.indexWhere(_._1.getId == loopId)
          refinement(newPath.map{
            case (rn,Transfer(t)) => (rn,t)
            case (rn,la@_) => (rn,transFormula(la, Set())._1)
          },repetitivePath(getLoopIndex(repetitivePath))._1.getId,repetitivePath(getLoopIndex(repetitivePath))._2)
      }
    }
    else
      newPredicatesMap = refinement(infeasibleSuffix.map(_._1).zip(getPathToErrorFormula(infeasibleSuffix)))
    (removalPath.map(_._1),newPredicatesMap)
  }
  /**
   * finds the interpolants for a spurious path and returns the predicate map with new predicates
   */
  def refinement(oPath: List[(RNode,Expression)], loopNodeId: Int = -1, loopLabel: Label = Assume(BoolConst(true))): collection.mutable.Map[CFGVertex,List[(Expression,List[Int])]] = {
    //println("I am sending " + forwardSSA(oPath.map(_._2)).map(shortCircuit).size + " formulas to princess")
    val oInterpolants = pathInterpols(forwardSSA(oPath.map(_._2)).map(shortCircuit))
    var result = collection.mutable.Map[CFGVertex,List[(Expression,List[Int])]]().empty
    if(oInterpolants.size == 0) {
      println("Fatal Error: No interpolants found")
      sys.exit(0)
    }
    if(log) println("Interpolants: " + oInterpolants.map(lazabs.viewer.ScalaPrinter(_)).mkString(" , "))
    val path = oPath.drop(oInterpolants.indexWhere(_ != BoolConst(true)))     // getting the shortest suffix, if any
    var interpolants = oInterpolants.dropWhile(_ == BoolConst(true))          // getting the shortest suffix, if any
    //lazabs.viewer.DrawGraph(rTree,false)
    //Console.readLine
    val loopIndex = path.zip(path.tail).indexWhere{
      case (a,b) => 
        (a._1.getId == loopNodeId)
    }
    if(loopIndex >= 0) {
      val accelerationImage = sp((if(loopIndex == 0) BoolConst(true) else interpolants(loopIndex - 1)),Transfer(path(loopIndex)._2))
      val interpolantFreeVars1 = (if(loopIndex == 0) Set() else freeVars(interpolants(loopIndex - 1)))
      val interpolantFreeVars2 = freeVars(interpolants(loopIndex))
      val imageFreeVars = freeVars(accelerationImage)
      val inductiveInterpolant = elimQuantifiers(deBruijnIndex((imageFreeVars -- (interpolantFreeVars1 ++ interpolantFreeVars2)).foldLeft[Expression](accelerationImage)((a,b) => Existential(BinderVariable(b.name).stype(b.stype),a))))
      interpolants = interpolants.updated(loopIndex,inductiveInterpolant)
      if(loopIndex != 0) interpolants = interpolants.updated(loopIndex - 1,BoolConst(false))
      loopLabel match {
        case TransitiveClosure(labels,states) if (labels.size > 1) =>
          val localPath = (List(CFGVertex(path(loopIndex)._1.getCfgId)) ::: states ::: List(CFGVertex(path(loopIndex)._1.getCfgId))).zip(labels :+ Assume(BoolConst(true)))
          val localPathFormulas: List[Expression] = List(prime(inductiveInterpolant)) ::: ((localPath).zip(localPath.tail)).map(el => MakeRTreeInterpol.cfg.getFormula(el._1._1,el._2._1,el._1._2)) ::: List(Not(inductiveInterpolant))
          val interInterpols = pathInterpols(forwardSSA(localPathFormulas).map(shortCircuit))
          (states.zip(interInterpols.slice(1,interInterpols.size - 1))).foreach(sti => {
            result.update(sti._1,(result.getOrElse(sti._1,List((BoolConst(false),List()))) ::: List((sti._2,List()))).distinct)
          })
        case _ =>
      }
    }
    path.tail.zip(interpolants).filterNot(_._2 == BoolConst(false)).foreach(p => {
      val vertex = CFGVertex(p._1._1.getCfgId)
      result.update(vertex,(result.getOrElse(vertex,List((BoolConst(false),List()))) ::: List((p._2,List()))).distinct)
    })
    result
  }
}