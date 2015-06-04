/**
 * Copyright (c) 2015 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.concurrency


import ap.parser._
import concurrentC._
import concurrentC.Absyn._

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer}

object CCReader {
  class ParseException(msg : String) extends Exception(msg)
  class TranslationException(msg : String) extends Exception(msg)
}

class CCReader {

  import CCReader._

  def apply(input : java.io.Reader) : ParametricEncoder.System = {
    def entry(parser : concurrentC.parser) = parser.pProgram
    val prog = parseWithEntry(input, entry _)
    println(printer print prog)
    translateProgram(prog)
    null
  }

  /**
   * Parse starting at an arbitrarily specified entry point
   */
  private def parseWithEntry[T](input : java.io.Reader,
                                entry : (parser) => T) : T = {
    val l = new Yylex(new ap.parser.Parser2InputAbsy.CRRemover2 (input))
    val p = new parser(l)
    
    try { entry(p) } catch {
      case e : Exception =>
        throw new ParseException(
             "At line " + String.valueOf(l.line_num()) +
             ", near \"" + l.buff() + "\" :" +
             "     " + e.getMessage())
    }
  }

  private val printer = new PrettyPrinterNonStatic

  //////////////////////////////////////////////////////////////////////////////

  import IExpression._

  private val globalVars = new ArrayBuffer[ConstantTerm]

  private val globalVarsInit = new ArrayBuffer[ITerm]

  private def globalVarIndex(name : String) : Option[Int] =
    (globalVars indexWhere (_.name == name)) match {
      case -1 => None
      case i  => Some(i)
    }

  private def lookupVar(name : String) : Int =
    (globalVars indexWhere (_.name == name)) match {
      case -1 => throw new TranslationException(
                   "Symbol " + name + " is not declared")
      case i  => i
    }

  //////////////////////////////////////////////////////////////////////////////

  private val channels = new MHashMap[String, ParametricEncoder.CommChannel]

  //////////////////////////////////////////////////////////////////////////////

  /** Implicit conversion so that we can get a Scala-like iterator from a
    * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  private def translateProgram(prog : Program) : Unit = {
    // first collect all declarations

    val globalVarSymex = new Symex(new ArrayBuffer)

    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_) decl match {
      case decl : Global =>
        collectVarDecls(decl.dec_, true, globalVarSymex)

      case decl : Chan =>
        for (name <- decl.chan_def_.asInstanceOf[AChan].listident_) {
          if (channels contains name)
            throw new TranslationException(
              "Channel " + name + " is already declared")
          channels.put(name, new ParametricEncoder.CommChannel(name))
        }

      case _ =>
        // nothing
    }

    globalVarsInit ++= globalVarSymex.getValues
    println(globalVarsInit.toList)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def collectVarDecls(dec : Dec,
                              global : Boolean,
                              values : Symex) : Unit = dec match {
    case decl : Declarators => {
      // just assume that the type is int for the time being

      for (initDecl <- decl.listinit_declarator_) initDecl match {
        case initDecl : OnlyDecl => {
          val c = new ConstantTerm(getName(initDecl.declarator_))
          if (global)
            globalVars += c
          values addValue c
        }
        case initDecl : InitDecl => {
          val c = new ConstantTerm(getName(initDecl.declarator_))
          val initValue = initDecl.initializer_ match {
            case init : InitExpr => values eval init.exp_
          }
          if (global)
            globalVars += c
          values addValue initValue
        }
      }
    }
    case _ : NoDeclarator =>
      // nothing
  }

  private def getName(decl : Declarator) : String = decl match {
    case decl : NoPointer => getName(decl.direct_declarator_)
  }

  private def getName(decl : Direct_declarator) : String = decl match {
    case decl : Name => decl.ident_
    case decl : ParenDecl => getName(decl.declarator_)
  }

  //////////////////////////////////////////////////////////////////////////////

  private class Symex(values : ArrayBuffer[ITerm]) {
    def addValue(t : ITerm) =
      values += t

    def getValue(name : String) =
      values(lookupVar(name))
    def setValue(name : String, t : ITerm) =
      values(lookupVar(name)) = t

    def getValues : Seq[ITerm] = values

    def eval(exp : Exp) : ITerm = exp match {
      case exp : Ecomma => {
        eval(exp.exp_1)
        eval(exp.exp_2)
      }
//      case exp : Eassign.     Exp2  ::= Exp15 Assignment_op Exp2;
//      case exp : Econdition.  Exp3  ::= Exp4 "?" Exp ":" Exp3;
//      case exp : Elor.        Exp4  ::= Exp4 "||" Exp5;
//      case exp : Eland.       Exp5  ::= Exp5 "&&" Exp6;
//      case exp : Ebitor.      Exp6  ::= Exp6 "|" Exp7;
//      case exp : Ebitexor.    Exp7  ::= Exp7 "^" Exp8;
//      case exp : Ebitand.     Exp8  ::= Exp8 "&" Exp9;
//      case exp : Eeq.         Exp9  ::= Exp9 "==" Exp10;
//      case exp : Eneq.        Exp9  ::= Exp9 "!=" Exp10;
//      case exp : Elthen.      Exp10 ::= Exp10 "<" Exp11;
//      case exp : Egrthen.     Exp10 ::= Exp10 ">" Exp11;
//      case exp : Ele.         Exp10 ::= Exp10 "<=" Exp11;
//      case exp : Ege.         Exp10 ::= Exp10 ">=" Exp11;
//      case exp : Eleft.       Exp11 ::= Exp11 "<<" Exp12;
//      case exp : Eright.      Exp11 ::= Exp11 ">>" Exp12;
      case exp : Eplus =>
        eval(exp.exp_1) + eval(exp.exp_2)
      case exp : Eminus =>
        eval(exp.exp_1) - eval(exp.exp_2)
      case exp : Etimes =>
        eval(exp.exp_1) * eval(exp.exp_2)
//      case exp : Ediv.        Exp13 ::= Exp13 "/" Exp14;
//      case exp : Emod.        Exp13 ::= Exp13 "%" Exp14;
//      case exp : Etypeconv.   Exp14 ::= "(" Type_name ")" Exp14;
//      case exp : Epreinc.     Exp15 ::= "++" Exp15;
//      case exp : Epredec.     Exp15 ::= "--" Exp15;
//      case exp : Epreop.      Exp15 ::= Unary_operator Exp14;
//      case exp : Ebytesexpr.  Exp15 ::= "sizeof" Exp15;
//      case exp : Ebytestype.  Exp15 ::= "sizeof" "(" Type_name ")";
//      case exp : Earray.      Exp16 ::= Exp16 "[" Exp "]" ;
//      case exp : Efunk.       Exp16 ::= Exp16 "(" ")";
//      case exp : Efunkpar.    Exp16 ::= Exp16 "(" [Exp2] ")";
//      case exp : Eselect.     Exp16 ::= Exp16 "." Ident;
//      case exp : Epoint.      Exp16 ::= Exp16 "->" Ident;
//      case exp : Epostinc.    Exp16 ::= Exp16 "++";
//      case exp : Epostdec.    Exp16 ::= Exp16 "--";
      case exp : Evar =>
        getValue(exp.ident_)
      case exp : Econst =>
        eval(exp.constant_)
//      case exp : Estring.     Exp17 ::= String;
    }

    def eval(constant : Constant) : ITerm = constant match {
//      case constant : Efloat.        Constant ::= Double;
//      case constant : Echar.         Constant ::= Char;
//      case constant : Eunsigned.     Constant ::= Unsigned;
//      case constant : Elong.         Constant ::= Long;
//      case constant : Eunsignlong.   Constant ::= UnsignedLong;
//      case constant : Ehexadec.      Constant ::= Hexadecimal;
//      case constant : Ehexaunsign.   Constant ::= HexUnsigned;
//      case constant : Ehexalong.     Constant ::= HexLong;
//      case constant : Ehexaunslong.  Constant ::= HexUnsLong;
//      case constant : Eoctal.        Constant ::= Octal;
//      case constant : Eoctalunsign.  Constant ::= OctalUnsigned;
//      case constant : Eoctallong.    Constant ::= OctalLong;
//      case constant : Eoctalunslong. Constant ::= OctalUnsLong;
//      case constant : Ecdouble.      Constant ::= CDouble;
//      case constant : Ecfloat.       Constant ::= CFloat;
//      case constant : Eclongdouble.  Constant ::= CLongDouble;
      case constant : Eint =>
        i(constant.integer_)
    }
  }

}