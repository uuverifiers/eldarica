/**
 * Copyright (c) 2015-2016 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.preprocessor.{DefaultPreprocessor, HornPreprocessor}

import ap.parser._
import ap.terfor.preds.Predicate
import Util._

/**
 * Simple wrapper around the classes that can be used to
 * call the solver from Java
 */
object SimpleWrapper {

  import HornPreprocessor.InitPredicateVerificationHints

  def solve(clauses : Iterable[HornClauses.Clause],
            initialPredicates : Map[Predicate, Seq[IFormula]],
            useTemplates : Boolean,
            debuggingOutput : Boolean)
          : Either[Map[Predicate, IFormula],
                   Dag[(IAtom, HornClauses.Clause)]] = {
    val errOutput =
      if (debuggingOutput) Console.err else HornWrapper.NullStream
      
    Console.withErr(errOutput) { Console.withOut(Console.err) {
      var (newClauses, newInitialPredicates, backTranslator) = {
        val preprocessor = new DefaultPreprocessor
        val hints = new InitPredicateVerificationHints(initialPredicates)
        val (newClauses, newHints, backTranslator) =
          preprocessor.process(clauses.toSeq, hints)
        (newClauses, newHints.toInitialPredicates, backTranslator)
      }
  
      val interpolator = if (useTemplates) {
        val abstractionMap =
          (new lazabs.horn.abstractions.StaticAbstractionBuilder(
            newClauses,
            lazabs.GlobalParameters.get.templateBasedInterpolationType)
               .abstractions) mapValues (
                 lazabs.horn.bottomup.TemplateInterpolator.AbstractionRecord(_))
        lazabs.horn.bottomup.TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
          abstractionMap,
          lazabs.GlobalParameters.get.templateBasedInterpolationTimeout)
      } else {
        DagInterpolator.interpolatingPredicateGenCEXAndOr _
      }
      
      val predAbs =
        new HornPredAbs(newClauses, initialPredicates, interpolator)
  
      backTranslator translate predAbs.result
    }}
  }

  def clause(head : IAtom, body : List[IAtom], constraint : IFormula)
            : HornClauses.Clause =
    HornClauses.Clause(head, body, constraint)

  val FALSEAtom = IAtom(HornClauses.FALSE, List())

}