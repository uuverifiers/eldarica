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


import concurrentC._
import concurrentC.Absyn._

import scala.collection.mutable.{HashMap => MHashMap}

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

  private val channels = new MHashMap[String, ParametricEncoder.CommChannel]

  /** Implicit conversion so that we can get a Scala-like iterator from a
    * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  private def translateProgram(prog : Program) : Unit = {
    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_) decl match {
      case decl : Global =>

      case decl : Chan   =>
        for (name <- decl.chan_def_.asInstanceOf[AChan].listident_) {
          if (channels contains name)
            throw new TranslationException(
              "Channel " + name + " is already declared")
          channels.put(name, new ParametricEncoder.CommChannel(name))
        }

      case thread : Athread =>
    }
  }

}