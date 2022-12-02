/**
 * Copyright (c) 2011-2019 Philipp Ruemmer and Pavle Subotic.
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

import ap.terfor.preds.Predicate

import scala.collection.mutable.{HashMap => MHashMap}

  object AbstractionRecord {
    def apply(pair : (Iterable[Predicate], AbsLattice)) =
      new AbstractionRecord {
        val loopBody = pair._1.toSet
        val lattice = pair._2
        val loopIterationAbstractionThreshold = 3
      }

    def mergeMaps(a : AbstractionMap, b : AbstractionMap) : AbstractionMap = {
      val res = new MHashMap[Predicate, AbstractionRecord]
      res ++= a
      for ((pred, record) <- b) (res get pred) match {
        case Some(oldRecord) => res.put(pred, oldRecord merge record)
        case None => res.put(pred, record)
      }
      res.toMap
    }

    type AbstractionMap = Map[Predicate, AbstractionRecord]
  }

  abstract class AbstractionRecord {
    val loopBody : Set[Predicate]
    val lattice : AbsLattice
    // how often does a predicate have to occur in a counterexample before
    // interpolation abstraction is applied
    val loopIterationAbstractionThreshold : Int

    def merge(that : AbstractionRecord) : AbstractionRecord =
      if (this.lattice.isUnit) {
        that
      } else if (that.lattice.isUnit) {
        this
      } else {
        val x = this
        new AbstractionRecord {
          val loopBody = that.loopBody
          val lattice = ProductLattice(x.lattice, that.lattice, true)
          val loopIterationAbstractionThreshold =
            x.loopIterationAbstractionThreshold min
            that.loopIterationAbstractionThreshold
        }
      }
  }


