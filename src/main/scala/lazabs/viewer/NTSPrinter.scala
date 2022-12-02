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

package lazabs.viewer

import lazabs.ast.ASTree._
import lazabs.nts._
import lazabs.types._
import lazabs.cfg._
import lazabs.utils.Manip._


object NTSPrinter {

  /**
   * converts the given control flow graph to NTS subsystem
   * @param cfg input cfg
   * @param name name of the output subsystem 
   */
  def toNtsSub(cfg: CFG, name: String): NtsSubsystem = {
    NtsSubsystem(
      name,                                                                    // name
      cfg.transitions.toList.map{ x => x._2.map{ y =>                          // transitions
        NtsTransition(
          x._1.getId,
          y.to.getId,
          cfg.formulas.getOrElse((x._1,y.to),BoolConst(false)))
      }}.flatten,
      List(),                                                                  // inputVars
      List(),                                                                  // outputVars
      (cfg.variables.values.foldLeft(Set[Variable]())(_++_) ++                 // vars
         cfg.freshVars.values.foldLeft(Set[Variable]())(_++_)).toList,
      List(cfg.start.getId),                                                   // initStates
      List(),                                                                  // finalStates
      List(-1)                                                                 // errorStates
    )
  }

  def apply(cfg: CFG): String = {
    val freshStartId = FreshCFGStateId.apply
    val (name,init) = cfg.sobject match {
      case Some(o) => (o.name,MakeCFG.initialValues(o))
      case None => ("Eldarica_Output",List[(Variable,Expression)]())
    }
    val subsys = toNtsSub(cfg,"main")
    "nts " + name + ";\n\n" + subsys.copy(
        transitions = (if (init.size != 0)
        List(NtsTransition(
          freshStartId, 
          cfg.start.getId,
          init.map(x => Assignment(prime(x._1), x._2)).reduceLeft(Conjunction(_,_))
        ))
          else List()) ++ subsys.transitions,
        initStates = (if (init.size != 0) List(freshStartId) else subsys.initStates)
    )
  }
}