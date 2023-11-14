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
import lazabs.utils.Manip._
import lazabs.prover.PrincessWrapper._

object RefineNormal {
  /**
   * finds the interpolants for a spurious path and returns the predicate map with new predicates
   */
  def apply(oPath: List[(RNode,Expression)], log: Boolean): collection.mutable.Map[CFGVertex,List[(Expression,List[Int])]] = {
    //println("I am sending " + forwardSSA(oPath.map(_._2)).map(shortCircuit).map(lazabs.viewer.ScalaPrinter(_)) + " formulas to princess")
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
    path.tail.zip(interpolants).filterNot(_._2 == BoolConst(false)).foreach(p => {
      val vertex = CFGVertex(p._1._1.getCfgId)
      result.update(vertex,(result.getOrElse(vertex,List((BoolConst(false),List()))) ::: List((p._2,List()))).distinct)
    })
    result
  }
}
