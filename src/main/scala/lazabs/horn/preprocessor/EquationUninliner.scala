/**
 * Copyright (c) 2023 Zafer Esen. All rights reserved.
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

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap,
  HashSet => MHashSet}
import ap.parser._
import ap.parser.IExpression.{Predicate, and}
import ap.types.{Sort, SortedConstantTerm}
import lazabs.horn.preprocessor.HornPreprocessor._
import lazabs.horn.bottomup.HornClauses._

/**
 * A very simple preprocessor that ensures the following.
 *
 * 1) Constant terms on the RHS of every function application are distinct, e.g.,
 *   f(a) = c, g(b) = c
 * is rewritten as
 *   f(a) = c, g(b) = c1, c = c1.
 *
 * 2) If there are 0-ary function applications, the first is duplicated, e.g.,
 *   f() = c, g(b) = c
 * is rewritten as
 *   f() = c, f() = c1, g(b) = c2, c1 = c2
 *
 * This is done by duplicating the first appearing 0-ary function application,
 * and not adding an explicit equality formula.
 *   f() = c, g(a) = c
 * is rewritten as
 *   f() = c, f() = c1, g(a) = c1
 * after which (1) is applied to get
 *   f() = c, f() = c1, g(a) = c2, c1 = c2
 *
 * For the motivation of (2), consider the following:
 *   f() = c, g(b) = c, h(c) = b
 * This is seemingly a loop in terms of dependencies; however, since 'c' is
 * really a constant, it is not a dependency produced by g(b). By (2), this
 * would get rewritten as:.
 *   f() = c, f() = c1, g(b) = c2, c1 = c2, h(c) = b
 * which breaks the loop. So (2) is only applied when c appears as argument in
 * some other function application.
 *
 * This translator can be useful for obtaining a normal form. For instance when
 * creating a clause graph, it ensures each such constant can have one
 * incoming edge at most.
 *
 * Requires: function applications in the form f(x_bar) = b with b : IConstant.
 * Ensures: distinct IConstant RHS for all function applications in a clause..
 */
class EquationUninliner extends HornPreprocessor {
  override val name : String = "uninlining equations"
  override def process(clauses          : Clauses,
                       hints            : VerificationHints,
                       frozenPredicates : Set[Predicate]) : (Clauses,
    VerificationHints, HornPreprocessor.BackTranslator) = {

    val clauseBackMapping = new MHashMap[Clause, Clause]

    for (clause <- clauses) {
      val conjuncts =
        LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)

      val newConjuncts = new ArrayBuffer[IFormula]
      val constantCountAsRhs = new MHashMap[IConstant, Int]
      clause.constants.foreach(
        constant => constantCountAsRhs += IConstant(constant) -> 0)

      // Use the latest constant in equalities, needed for duplication of 0-ary
      // function applications.
      val constToLatestConst = new MHashMap[IConstant, IConstant]
      clause.constants.foreach(
        c => constToLatestConst += IConstant(c) -> IConstant(c))

      val duplicatedFuns = new MHashSet[IFunction]
      val constantsAppearingAsFunArgs = new MHashSet[IConstant]

      // Duplicate each 0-ary function application first.
      // Collect function applications some constant appears as equal to,
      // if there are more than one such occurrence.
      val constantsToFunApps : Map[IConstant, Seq[IFunApp]] =
        conjuncts.collect{
          case IEquation(app@IFunApp(_, args), c@IConstant(_)) =>
            // Collect constants appearing as fun args while we are at it.
            args.foreach{
              case constant : IConstant => constantsAppearingAsFunArgs +=
                constant
              case _ =>
            }
            app -> c
        }.groupBy(_._2).map(pair => pair._1 -> pair._2.map(_._1))
          .filter(_._2.length > 1)
      // For each such constant, duplicate the conjunct
      for ((c, apps) <- constantsToFunApps) {
        apps.find(app => app.args.isEmpty) match {
          case Some(app) if constantsAppearingAsFunArgs contains c =>
            newConjuncts += app === c
            // also make sure that the rest continues from some new constant
            val newConstant = IConstant(new SortedConstantTerm(
              s"${c.c.name}_0", Sort.sortOf(c)))
            constantCountAsRhs(c) = 1
            constToLatestConst += c -> newConstant
            duplicatedFuns += app.fun
          case _ => // nothing needed
        }
      }

      for (conjunct <- conjuncts) conjunct match {
        case eq@IEquation(IFunApp(fun, _), c@IConstant(_)) =>
          if (constantCountAsRhs(c) > 0) {
            if(duplicatedFuns contains fun) {
              // Use the constant created during the pre-pass above.
              newConjuncts += eq.left === constToLatestConst(c)
            } else {
              // Need a new constant.
              val newConstant = IConstant(new SortedConstantTerm(
                s"${c.c.name}_${constantCountAsRhs(c)}", Sort.sortOf(c)))
              newConjuncts += eq.left === newConstant &&&
                constToLatestConst(c) === newConstant
              constToLatestConst += c -> newConstant
              constantCountAsRhs(c) += 1
            }
          } else {
            constantCountAsRhs(c) += 1
            // Mo need to introduce a new constant, keep old conjunct.
            newConjuncts += eq
          }
        case _ =>
          newConjuncts += conjunct
      }

      val newClause = Clause(clause.head, clause.body,and(newConjuncts))
      clauseBackMapping += newClause -> clause
    }

    val backTranslator = new BackTranslator {
      override def translate(solution : Solution) : Solution = solution
      override def translate(cex : CounterExample) : CounterExample =
        for (p <- cex) yield {
          val (a, clause) = p
          (a, clauseBackMapping(clause))
        }
    }

    (clauseBackMapping.keys.toSeq, hints, backTranslator)
  }
}
