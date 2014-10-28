/**
 * Copyright (c) 2014 Philipp Ruemmer. All rights reserved.
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

import ap.parser._
import ap.parameters.ParserSettings
import ap.parser.Parser2InputAbsy.CRRemover2
import TplSpec._
import TplSpec.Absyn._

import scala.collection.mutable.ArrayBuffer

class AbsReader(input : java.io.Reader) {

  private val printer = new PrettyPrinterNonStatic

  /** Implicit conversion so that we can get a Scala-like iterator from a
   * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  //////////////////////////////////////////////////////////////////////////////

  val (initialPredicates, templates) = {
    Console.err.println("Loading CEGAR hints ...")

    val l = new Yylex(new CRRemover2 (input))
    val p = new parser(l)
    val specC = p.pSpecC

    val smtParser = SMTParser2InputAbsy(ParserSettings.DEFAULT)
    val env = smtParser.env

    def translatePredRef(predrefC : PredRefC) : (String, Int) = {
      val predref = predrefC.asInstanceOf[PredRef]
      val predName = printer print predref.symbolref_

      for (variableC <- predref.listsortedvariablec_.reverseIterator) {
        val variable = variableC.asInstanceOf[SortedVariable]
        val t = SMTParser2InputAbsy.BoundVariable(
                  (printer print variable.sort_) == "Bool")
        env.pushVar(printer print variable.symbol_, t)
      }

      (predName, predref.listsortedvariablec_.size)
    }

    ////////////////////////////////////////////////////////////////////////////

    val initialPredicates =
    (for (predspec <-
            specC.asInstanceOf[Spec].listpredspec_.iterator;
          if (predspec.isInstanceOf[InitialPredicates]);
          initPreds = predspec.asInstanceOf[InitialPredicates]) yield {
       val (predName, varNum) = translatePredRef(initPreds.predrefc_)

       val preds = (for (term <- initPreds.listterm_.iterator) yield {
         smtParser.parseExpression(printer print term).asInstanceOf[IFormula]
       }).toList

       for (_ <- 0 until varNum)
         env.popVar

       (predName -> preds)
    }).toList

    ////////////////////////////////////////////////////////////////////////////

    val templates =
    (for (predspec <-
            specC.asInstanceOf[Spec].listpredspec_.iterator;
          if (predspec.isInstanceOf[Templates]);
          templates = predspec.asInstanceOf[Templates]) yield {
       val (predName, varNum) = translatePredRef(templates.predrefc_)
 
       val preds = new ArrayBuffer[(IFormula, Int)]
       val terms = new ArrayBuffer[(ITerm, Int)]
       val ineqs = new ArrayBuffer[(ITerm, Int)]
       var iterationThreshold : Option[Int] = None

       for (templatec <- templates.listtemplatec_)
         templatec match {
           case template : TermTemplate => {
             val expr = smtParser.parseExpression(printer print template.term_)
             val cost = template.numeral_.toInt
 
             (template.templatetype_, expr) match {
               case (_ : PredicateType,            f : IFormula) =>
                 preds += ((~f, cost))
               case (_ : PredicatePosNegType,      f : IFormula) => {
                 preds += ((f, cost))
                 preds += ((~f, cost))
               }
               case (_ : TermType,                 t : ITerm) =>
                 terms += ((t, cost))
               case (_ : InequalityTermType,       t : ITerm) =>
                 ineqs += ((t, cost))
               case (_ : InequalityTermPosNegType, t : ITerm) => {
                 ineqs += ((t, cost))
                 ineqs += ((-t, cost))
               }
             }
           }
           case threshold : IterationThreshold =>
             iterationThreshold = Some(threshold.numeral_.toInt)
         }
 
       for (_ <- 0 until varNum)
         env.popVar
 
       val lattices : List[AbsLattice] =
         (if (preds.isEmpty) List() else List(PredicateLattice(preds))) ++
         (if (terms.isEmpty) List() else List(TermSubsetLattice(terms))) ++
         (if (ineqs.isEmpty) List() else List(TermIneqLattice(ineqs)))

       (predName ->
        ((lattices reduceLeft (ProductLattice(_, _, true)),
         iterationThreshold)))
    }).toList

    ////////////////////////////////////////////////////////////////////////////

    (initialPredicates, templates)
  }

}