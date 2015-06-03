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

  private def globalVarIndex(name : String) : Option[Int] =
    (globalVars indexWhere (_.name == name)) match {
      case -1 => None
      case i  => Some(i)
    }

  private val channels = new MHashMap[String, ParametricEncoder.CommChannel]

  /** Implicit conversion so that we can get a Scala-like iterator from a
    * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  private def translateProgram(prog : Program) : Unit = {
    // first collect all declarations
    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_) decl match {
      case decl : Global =>
        println(collectVarDecls(decl.dec_, true))

      case decl : Chan   =>
        for (name <- decl.chan_def_.asInstanceOf[AChan].listident_) {
          if (channels contains name)
            throw new TranslationException(
              "Channel " + name + " is already declared")
          channels.put(name, new ParametricEncoder.CommChannel(name))
        }

      case thread : Athread =>
        // nothing
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def collectVarDecls(dec : Dec,
                              global : Boolean) : Seq[ITerm] = dec match {
    case decl : Declarators => {
      // just assume that the type is int for the time being

      val res = new ArrayBuffer[ITerm]

      for (initDecl <- decl.listinit_declarator_) initDecl match {
        case initDecl : OnlyDecl => {
          val c = new ConstantTerm(getName(initDecl.declarator_))
          if (global)
            globalVars += c
          res += c
        }
        case initDecl : InitDecl => {
          val c = new ConstantTerm(getName(initDecl.declarator_))
          if (global)
            globalVars += c
          initDecl.initializer_ match {
            case init : InitExpr =>
              res += 0
          }
        }
      }

      res
    }
    case _ : NoDeclarator =>
      List()
  }

  private def getName(decl : Declarator) : String = decl match {
    case decl : NoPointer => getName(decl.direct_declarator_)
  }

  private def getName(decl : Direct_declarator) : String = decl match {
    case decl : Name => decl.ident_
    case decl : ParenDecl => getName(decl.declarator_)
  }

}