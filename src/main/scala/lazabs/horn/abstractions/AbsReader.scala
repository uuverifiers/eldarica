/**
 * Copyright (c) 2014-2023 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts

import ap.parser._
import ap.parameters.ParserSettings
import ap.parser.Parser2InputAbsy.CRRemover2
import ap.SimpleAPI

import TplSpec._
import TplSpec.Absyn._

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

object AbsReader {

  /**
   * Output a set of verification hints in the template parser format.
   */
  def printHints(hints : VerificationHints) : Unit = {
    for ((pred, hints) <- hints.predicateHints.toSeq sortBy (_._1.name)) {
      val sorts =
        predArgumentSorts(pred)
      val argConsts =
        for ((s, n) <- sorts.zipWithIndex) yield (s newConstant ("x" + n))
      val subst =
        ((for (c <- argConsts.iterator) yield IConstant(c)).toList, 0)

      val (initPreds, otherHints) =
        hints partition (_.isInstanceOf[VerificationHints.VerifHintInitPred])

      if (!initPreds.isEmpty) {
        print("(initial-predicates ")
        print(SMTLineariser.quoteIdentifier(pred.name))
        print(" ")
        SMTLineariser.printArguments(sorts, argConsts)
        println

        for (VerificationHints.VerifHintInitPred(p) <- initPreds) {
          print("  ")
          printIExpr(p, subst)
          println
        }

        println(")")
      }

      if (!otherHints.isEmpty) {
        print("(templates ")
        print(SMTLineariser.quoteIdentifier(pred.name))
        print(" ")
        SMTLineariser.printArguments(sorts, argConsts)
        println

        for (el <- otherHints)
          printHintElement(el, subst)

        println(")")
      }
    }
  }

  private def printHintElement(hint : VerificationHints.VerifHintElement,
                               subst : (List[ITerm], Int)) : Unit = {
    import VerificationHints._
    print("  (")
    hint match {
      case VerifHintTplPred(f, cost) => {
        print("predicate ")
        printIExpr(f, subst)
        print(" " + cost)
      }
      case VerifHintTplPredPosNeg(f, cost) => {
        print("predicate-2 ")
        printIExpr(f, subst)
        print(" " + cost)
      }
      case VerifHintTplEqTerm(t, cost) => {
        print("term ")
        printIExpr(t, subst)
        print(" " + cost)
      }
      case VerifHintTplInEqTerm(t, cost) => {
        print("inequality-term ")
        printIExpr(t, subst)
        print(" " + cost)
      }
      case VerifHintTplInEqTermPosNeg(t, cost) => {
        print("inequality-term-2 ")
        printIExpr(t, subst)
        print(" " + cost)
      }
      case VerifHintTplIterationThreshold(threshold) => {
        print("iterationThreshold " + threshold)
      }
      case el =>
        throw new Exception("Unsupported hint element: " + el)
    }
    println(")")
  }

  private def printIExpr(t : IExpression, subst : (List[ITerm], Int)) =
    SMTLineariser(VariableSubstVisitor(t, subst))
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class to read initial predicates and interpolation templates from a file.
 */
class AbsReader(input : java.io.Reader) {

  import SMTTypes.{SMTType, SMTInteger, SMTBool, SMTArray, SMTBitVec}

  private val printer = new PrettyPrinterNonStatic

  /** Implicit conversion so that we can get a Scala-like iterator from a
   * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  /**
   * Translation of sorts to the SMT parser types.
   * 
   * TODO: add support for ADT sorts and heap.
   */
  private def translateSort(s : Sort) : SMTType = try {
    s match {
      case s : IdentSort => s.identifier_ match {
        case id : SymbolIdent => (printer print id) match {
          case "Int"  => SMTInteger
          case "Bool" => SMTBool
        }
        case id : IndexIdent => (printer print id.symbol_) match {
          case "BitVec" if id.listindexc_.size == 1 =>
            SMTBitVec((printer print id.listindexc_.get(0)).toInt)
        }
      }
      case s : CompositeSort => s.identifier_ match {
        case id : SymbolIdent => (printer print id) match {
          case "Array" => {
            val args = s.listsort_.toList map translateSort
            if (args.size < 2)
              throw new Exception(
                "Expected at least two sort arguments in Array sort")
            SMTArray(args.init, args.last)
          }
        }
      }
    }
  } catch {
    case _ : MatchError =>
      throw new Exception("unsupported type in hints: " + (printer print s))
  }

  //////////////////////////////////////////////////////////////////////////////

  val (initialPredicates, allHints, predArities) =
    SimpleAPI.withProver(enableAssert =
                         lazabs.GlobalParameters.get.assertions) { prover =>
    println(
        "---------------------------- Loading CEGAR hints -------------------------------")

    val l = new Yylex(new CRRemover2 (input))
    val p = new parser(l)
    val specC = p.pSpecC

    val smtParser = SMTParser2InputAbsy(ParserSettings.DEFAULT)
    val env = smtParser.env

    val predArities = new MHashMap[String, Int]

    def translateSymbolRef(symref : SymbolRef) : String =
      symref.asInstanceOf[IdentifierRef]
            .identifier_
            .asInstanceOf[SymbolIdent]
            .symbol_ match {
        case s : NormalSymbol =>
          s.normalsymbolt_
        case s : QuotedSymbol => {
          val str = s.quotedsymbolt_
          str.substring(1, str.size - 1)
       }
     }


    def translatePredRef(predrefC : PredRefC) : (String, Int) = {
      val predref = predrefC.asInstanceOf[PredRef]
      val predName = translateSymbolRef(predref.symbolref_)

      for (variableC <- predref.listsortedvariablec_.reverseIterator) {
        val variable = variableC.asInstanceOf[SortedVariable]
        val t = SMTParser2InputAbsy.BoundVariable(translateSort(variable.sort_))
        env.pushVar(printer print variable.symbol_, t)
      }

      val arity = predref.listsortedvariablec_.size
      predArities.put(predName, arity)

      (predName, arity)
    }

    def parseExpr(str : String) : IExpression =
      (smtParser parseExpression str) match {
        case f : IFormula =>
          // check whether the formula contains quantifiers, which
          // we would have to eliminate
          if (QuantifierCountVisitor(f) > 0) prover.scope {
            prover simplify f
          } else {
            f
          }
        case t : ITerm =>
          t
      }

    ////////////////////////////////////////////////////////////////////////////

    val initialPredicates : List[(String, Seq[IFormula])] =
    (for (predspec <-
            specC.asInstanceOf[Spec].listpredspec_.iterator;
          if (predspec.isInstanceOf[InitialPredicates]);
          initPreds = predspec.asInstanceOf[InitialPredicates]) yield {
       val (predName, varNum) = translatePredRef(initPreds.predrefc_)

       val preds = (for (term <- initPreds.listterm_.iterator) yield {
         parseExpr(printer print term).asInstanceOf[IFormula]
       }).toList

       for (_ <- 0 until varNum)
         env.popVar

       (predName -> preds)
    }).toList

    ////////////////////////////////////////////////////////////////////////////

    import VerificationHints._
    import IExpression._

    val templateHints : List[(String, Seq[VerifHintElement])] =
    (for (predspec <-
            specC.asInstanceOf[Spec].listpredspec_.iterator;
          if (predspec.isInstanceOf[Templates]);
          templates = predspec.asInstanceOf[Templates]) yield {
       val (predName, varNum) = translatePredRef(templates.predrefc_)

       val hints = new ArrayBuffer[VerifHintElement]

       for (templatec <- templates.listtemplatec_)
         templatec match {
           case template : TermTemplate => {
             val expr = parseExpr(printer print template.term_)
             val cost = template.numeral_.toInt

             (template.templatetype_, expr) match {
               case (_ : PredicateType,            f : IFormula) =>
                 hints += VerifHintTplPred(f, cost)
               case (_ : PredicatePosNegType,      f : IFormula) =>
                 hints += VerifHintTplPredPosNeg(f, cost)
               case (_ : TermType,                 t : ITerm) =>
                 hints += VerifHintTplEqTerm(t, cost)
               case (_ : TermType,                 EqZ(t)) =>
                 hints += VerifHintTplEqTerm(t, cost)
               case (_ : InequalityTermType,       t : ITerm) =>
                 hints += VerifHintTplInEqTerm(t, cost)
               case (_ : InequalityTermPosNegType, t : ITerm) =>
                 hints += VerifHintTplInEqTermPosNeg(t, cost)
               case (_ : TermType |
                       _ : InequalityTermType |
                       _ : InequalityTermPosNegType,
                     f : IFormula) =>
                 throw new Exception("template " +
                                       (printer print template.term_) +
                                       " is a predicate, not a term")
             }
           }
           case threshold : IterationThreshold =>
             hints += VerifHintTplIterationThreshold(threshold.numeral_.toInt)
         }

       for (_ <- 0 until varNum)
         env.popVar

       (predName, hints.toSeq)
     }).toList

    ////////////////////////////////////////////////////////////////////////////

    val allHints : Map[String, Seq[VerifHintElement]] = {
      val res = new MHashMap[String, Seq[VerifHintElement]]

      for ((predName, preds) <- initialPredicates)
        res.put(predName, preds map (VerifHintInitPred(_)))
      for ((predName, hints) <- templateHints)
        res.put(predName, res.getOrElse(predName, List()) ++ hints)
      
      res.toMap
    }

    ////////////////////////////////////////////////////////////////////////////

    (initialPredicates, allHints, predArities.toMap)
  }

}
