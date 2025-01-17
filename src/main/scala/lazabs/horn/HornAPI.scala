/**
 * Copyright (c) 2024 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn

import ap.parser.{IFormula, IAtom}
import ap.terfor.preds.Predicate

import lazabs.GlobalParameters
import lazabs.horn.Util._
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.bottomup.{HornClauses, SimpleWrapper}
import lazabs.horn.preprocessor.DefaultPreprocessor
import lazabs.horn.symex._

/**
 * Simplified API for calling the different Horn clause back-ends.
 */
object HornAPI {

  /**
   * Solution of a set of Horn clauses.
   */
  type Solution = Map[Predicate, IFormula]

  /**
   * Counterexample for a set of Horn clauses.
   */
  type Counterexample = Dag[(IAtom, HornClauses.Clause)]

  /**
   * Options for the Horn engine. Options can be modified by overriding.
   */
  abstract class Options {
    val debuggingOutput  : Boolean      = false
    val enableAssertions : Boolean      = false
    val timeoutMS        : Option[Long] = None
  }

  /**
   * Options for the CEGAR engine. Passing an object of this class
   * to the methods of the <code>HornAPI</code> class will select
   * the CEGAR backend.
   */
  class CEGAROptions extends Options {
    val initialPredicates : Map[Predicate, Seq[IFormula]] = Map()
    val useTemplates      : Boolean                       = false
    val useAbstractPO     : Boolean                       = false
  }

  sealed trait SymexStrategy
  object SymexStrategy {
    case object BreadthFirstForward extends SymexStrategy
    case object DepthFirstForward   extends SymexStrategy
  }

  /**
   * Options for the symbolic execution engine.
   * If `maxDepth` is not `None`, execution will stop after the number of unit
   * clauses for any predicate exceeds `depth`.
   * Currently only `BreadthFirstForward` allows specifying `maxDepth`.
   */
  class SymexOptions extends Options {
    val strategy : SymexStrategy = SymexStrategy.BreadthFirstForward
    val maxDepth : Option[Int]   = None
  }

  /**
   * Exception indicating that a Horn backend has run into a timeout.
   */
  class TimeoutException extends Exception
}

/**
 * Simplified API for calling the different Horn clause back-ends.
 */
class HornAPI(options : HornAPI.Options = new HornAPI.CEGAROptions) {
  import HornAPI._

  private def newTimeoutChecker : () => Unit = {
    val startTime = System.currentTimeMillis
    options.timeoutMS match {
      case Some(to) => () => {
        if (System.currentTimeMillis - startTime > to.toLong)
          throw new TimeoutException
      }
      case None => () => {}
    }
  }

  /**
   * Solve the given set of clauses, but construct a full solution or a
   * counterexample only lazily when needed.
   */
  def solveLazily(clauses : Iterable[HornClauses.Clause])
                : Either[() => Solution, () => Counterexample] =
    GlobalParameters.withValue(GlobalParameters.get.clone) {

      GlobalParameters.get.assertions     = options.enableAssertions
      GlobalParameters.get.timeoutChecker = newTimeoutChecker
      GlobalParameters.get.setLogLevel(2)

      options match {
        case options : CEGAROptions =>
          SimpleWrapper.solveLazily(
            clauses           = clauses,
            initialPredicates = options.initialPredicates,
            useTemplates      = options.useTemplates,
            debuggingOutput   = options.debuggingOutput,
            useAbstractPO     = options.useAbstractPO)
        case options : SymexOptions =>
          val errOutput = if (options.debuggingOutput) Console.err else NullStream
          Console.withErr(errOutput) { Console.withOut(Console.err) {
            val (newClauses, _, backTranslator) = {
              val preprocessor = new DefaultPreprocessor
              preprocessor.process(clauses.toSeq, EmptyVerificationHints)
            }

            val symex = options.strategy match {
              case SymexStrategy.BreadthFirstForward =>
                new BreadthFirstForwardSymex[HornClauses.Clause](newClauses, options.maxDepth)
              case SymexStrategy.DepthFirstForward   =>
                new DepthFirstForwardSymex[HornClauses.Clause](newClauses)
            }
            symex.printInfo = options.debuggingOutput

            val result = symex.solve()
            symex.shutdown

            result match {
              case Left(x) => Left(() => backTranslator translate x)
              case Right(x) => Right(() => backTranslator translate x)
            }
          }
          }
      }
    }

  /**
   * Solve the given set of clauses.
   */
  def solve(clauses : Iterable[HornClauses.Clause])
          : Either[Solution, Counterexample] =
    solveLazily(clauses) match {
      case Left(x) => Left(x())
      case Right(x) => Right(x())
    }

  /**
   * Check whether the given clauses are satisfiable.
   */
  def isSat(clauses : Iterable[HornClauses.Clause]) : Boolean =
    solveLazily(clauses).isLeft

}
