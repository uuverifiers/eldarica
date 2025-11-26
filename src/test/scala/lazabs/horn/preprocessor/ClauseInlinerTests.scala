/**
 * Copyright (c) 2025 Zafer Esen. All rights reserved.
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

package lazabs.horn.preprocessor

import ap.SimpleAPI
import ap.parser.IExpression
import lazabs.GlobalParameters
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.preprocessor.HornPreprocessor.Solution
import org.scalatest.freespec.AnyFreeSpec

class ClauseInlinerTests extends AnyFreeSpec {

  import HornClauses._
  import IExpression._

  val reconstructionModes = Seq(
    ("cegar", GlobalParameters.SolutionReconstruction.CEGAR),
    ("wp", GlobalParameters.SolutionReconstruction.WP)
    )

  for ((modeName, modeValue) <- reconstructionModes) {
    s"solutionReconstruction:$modeName tests" - {
      "Empty solution" in {
        SimpleAPI.withProver(enableAssert = true){p =>
          import p._

          GlobalParameters.get.solutionReconstruction = modeValue

          val r = createRelation("r", List())
          val clauses : Seq[Clause] = List(
            r() :- true
          )

          val inliner = new ClauseInliner
          val (_, _, backTranslator) =
            inliner.process(clauses, EmptyVerificationHints)
          val emptySol : Solution = Map()
          val sol = backTranslator.translate(emptySol)
          assert(sol.size == 1 &&
                 sol.head._2 == i(true))
        }
      }
    }
  }
}