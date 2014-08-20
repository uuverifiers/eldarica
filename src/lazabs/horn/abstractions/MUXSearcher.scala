/**
 * Copyright (c) 2011-2014 Philipp Ruemmer. All rights reserved.
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
import SimpleAPI.ProverStatus
import ap.parser._
import ap.proof.theoryPlugins.Plugin
import ap.terfor.conjunctions.Conjunction
import ap.proof.goal.Goal

import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet,
                                 HashMap => MHashMap}


class MUXSearcher(lattice : AbsLattice,
                  xa : Seq[Seq[ITerm]], xb : Seq[Seq[ITerm]],
                  p : SimpleAPI) {
  import p._
  import IExpression._

  scope {
    val (flags, toLatticeObj) = lattice.genBooleanEncoding(xa, xb, p)

    val flagPreds = (for (IAtom(p, _) <- flags.iterator) yield p).toSet
    assert(flagPreds.size == flags.size)

    var allBlockingClauses : IFormula = true

    var maxNegFlags = 1
    while (??? == ProverStatus.Sat) scope {
      println(maxNegFlags)

      setupTheoryPlugin(new Plugin {
        def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] = {

/*          val posFlags =
            (for (atom <- goal.facts.predConj.positiveLits.iterator;
                  if (flagPreds contains atom.pred))
               yield atom.pred).toSet */
          val negFlags =
            (for (atom <- goal.facts.predConj.negativeLits.iterator;
                  if (flagPreds contains atom.pred))
               yield atom.pred).toSet

          if (negFlags.size > maxNegFlags)
            // case not allowed, backtrack
            Some((Conjunction.FALSE, Conjunction.TRUE))
          else if (negFlags.size == maxNegFlags) {
//       println("propagating: " + negFlags)
            // all other flags can be set to true
            Some(Conjunction.conj(
                   for (f@IAtom(p, _) <- flags.iterator;
                        if (!(negFlags contains p)))
                   yield asConjunction(f), goal.order),
                 Conjunction.TRUE)
          }
/*          else if (negFlags.size == maxNegFlags - 1 &&
                   flags.size >= posFlags.size + negFlags.size + 2)
            Some(Conjunction.disj(
                   (for (f@IAtom(p, _) <- flags.iterator;
                        if (!(negFlags contains p) && !(posFlags contains p)))
                    yield asConjunction(f)) take 2, goal.order),
                 Conjunction.TRUE) */
          else
            None
        }
      })

      !! (allBlockingClauses)

      while (??? == ProverStatus.Sat) {
        val posFlags =
          (for (f <- flags.iterator;
                if (evalPartial(f) != Some(false))) yield f).toSeq

        println("MSS: " + (posFlags mkString ", "))
        val clause = !and(posFlags)
        allBlockingClauses = allBlockingClauses &&& clause

        !! (clause)
      }

      maxNegFlags = maxNegFlags + 1
    }
  }
}