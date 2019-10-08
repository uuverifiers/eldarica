/**
 * Copyright (c) 2015-2019 Philipp Ruemmer. All rights reserved.
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

import lazabs.{GlobalParameters, ParallelComputation}
import lazabs.horn.preprocessor.DefaultPreprocessor
import lazabs.horn.abstractions.{StaticAbstractionBuilder, AbstractionRecord,
                                 InitPredicateVerificationHints}

import ap.parser._
import ap.terfor.preds.Predicate
import Util._

/**
 * Simple wrapper around the classes that can be used to
 * call Eldarica from Java or Scala applications.
 *
 * 
 */
object SimpleWrapper {

  /**
   * Solve the given set of clauses, but construct a full solution or a
   * counterexample only lazily when needed.
   */
  def solveLazily(clauses : Iterable[HornClauses.Clause],
                  initialPredicates : Map[Predicate, Seq[IFormula]],
                  useTemplates : Boolean,
                  debuggingOutput : Boolean,
                  useAbstractPO : Boolean)
                : Either[() => Map[Predicate, IFormula],
                         () => Dag[(IAtom, HornClauses.Clause)]] = {
    val errOutput =
      if (debuggingOutput) Console.err else HornWrapper.NullStream

    GlobalParameters.get.templateBasedInterpolation = useTemplates
    GlobalParameters.get.templateBasedInterpolationPortfolio = useAbstractPO

    Console.withErr(errOutput) { Console.withOut(Console.err) {
      var (newClauses, newInitialPredicates, backTranslator) = {
        val preprocessor = new DefaultPreprocessor
        val hints = new InitPredicateVerificationHints(initialPredicates)
        val (newClauses, newHints, backTranslator) =
          preprocessor.process(clauses.toSeq, hints)
        (newClauses, newHints.toInitialPredicates, backTranslator)
      }
  
      val params =
        if (GlobalParameters.get.templateBasedInterpolationPortfolio)
          GlobalParameters.get.withAndWOTemplates
        else
          List()

      ParallelComputation(params) {
        val interpolator =
          if (GlobalParameters.get.templateBasedInterpolation) {
            val abstractionBuilder =
              new StaticAbstractionBuilder(
                newClauses,
                GlobalParameters.get.templateBasedInterpolationType)
            val abstractionMap =
              abstractionBuilder.abstractionRecords
            TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
              abstractionMap,
              GlobalParameters.get.templateBasedInterpolationTimeout)
          } else {
            DagInterpolator.interpolatingPredicateGenCEXAndOr _
          }
      
        val predAbs =
          new HornPredAbs(newClauses, initialPredicates, interpolator)

        predAbs.result match {
          case Left(x) => Left(() => backTranslator translate x)
          case Right(x) => Right(() => backTranslator translate x)
        }
      }}}
  }

  /**
   * Solve the given set of clauses. It is optionally possible to provide
   * an initial set of predicates used for predicate abstraction
   * (<code>initialPredicates</code>),
   * to switch on interpolation abstraction (<code>useTemplates</code>),
   * to use normal interpolation and interpolation abstraction in a
   * portfolio (<code>useAbstractPO</code>), 
   * to enable debugging output on stderr (<code>debuggingOutput</code>),
   * or to show counterexamples graphically using dot and eog
   * (<code>showDot</code>).
   */
  def solve(clauses : Iterable[HornClauses.Clause],
            initialPredicates : Map[Predicate, Seq[IFormula]] = Map(),
            useTemplates : Boolean = false,
            debuggingOutput : Boolean = false,
            showDot : Boolean = false,
            useAbstractPO : Boolean = false)
          : Either[Map[Predicate, IFormula],
                   Dag[(IAtom, HornClauses.Clause)]] =
    solveLazily(clauses, initialPredicates, useTemplates,
                debuggingOutput, useAbstractPO) match {
      case Left(x) => Left(x())
      case Right(x) => {
        val cex = x()
        if (showDot) {
          val oldConf = GlobalParameters.get.pngNo
          GlobalParameters.get.pngNo = false
          Util.show(cex map (_._1), "SimpleWrapper")
          GlobalParameters.get.pngNo = oldConf
        }
        Right(cex)
      }
    }

  /**
   * Check whether the given clauses are satisfiable.
   */
  def isSat(clauses : Iterable[HornClauses.Clause],
            initialPredicates : Map[Predicate, Seq[IFormula]] = Map(),
            useTemplates : Boolean = false,
            debuggingOutput : Boolean = false,
            useAbstractPO : Boolean = false) : Boolean =
    solveLazily(clauses, initialPredicates, useTemplates,
                debuggingOutput, useAbstractPO).isLeft
  
  /**
   * Construct a clause from the given components.
   */
  def clause(head : IAtom, body : List[IAtom], constraint : IFormula)
            : HornClauses.Clause =
    HornClauses.Clause(head, body, constraint)

  /**
   * To be used as head of clauses without head.
   */
  val FALSEAtom = IAtom(HornClauses.FALSE, List())

}
