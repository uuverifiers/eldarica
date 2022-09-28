/**
 * Copyright (c) 2022 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
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

package lazabs.horn.extendedquantifiers

import ap.parser.{IFormula, ITerm}

// An instrumentation consists of a new constraint and a map from head argument
// indices (for the ghost variables) to ghost terms used in the constraint
case class Instrumentation (constraint : IFormula,
                            headTerms  : Map[Int, ITerm]) {
  // Two instrumentations are composed by conjoining the constraints,
  // and taking the union of the head terms. (head term map should be disjoint.)
  def + (that : Instrumentation): Instrumentation = {
    assert((headTerms.keys.toSet intersect that.headTerms.keys.toSet).isEmpty) // todo: use eldarica assertions

    Instrumentation(constraint &&& that.constraint, headTerms ++ that.headTerms)
  }
}

object Instrumentation {
  // the product of two sequences of instrumentations
  def product(instrs1 : Seq[Instrumentation],
              instrs2 : Seq[Instrumentation]) : Seq[Instrumentation] =
    for(instr1 <- instrs1; instr2 <- instrs2) yield instr1 + instr2
}