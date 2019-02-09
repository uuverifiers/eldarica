/**
 * Copyright (c) 2019 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.concurrency.concurrentC.{Yylex, sym}
import java_cup.runtime.{Scanner, Symbol}

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap, ArrayStack}

object TypedefReplacingLexer {

  // Can we get those symbol codes somehow from the JLex file,
  //   cc-parser/lazabs/horn/concurrency/concurrentC/Yylex
  // ?

  val Typedef_num   = sym._SYMB_76;
  val Struct_num    = sym._SYMB_73;
  val Enum_num      = sym._SYMB_60;
  val Union_num     = sym._SYMB_77;
  val Semicolon_num = sym._SYMB_2;
  val LBrace_num    = sym._SYMB_7;
  val RBrace_num    = sym._SYMB_8;
  val CIdent_num    = sym.CIdent;

}

/**
 * Lexer adapter that replaces typedefs with the actual type.
 */
class TypedefReplacingLexer(underlying : Yylex) extends Scanner {

  import TypedefReplacingLexer._

  private var recording = false
  private val recordedSyms = new ArrayBuffer[Symbol]

  private val typedefs = new MHashMap[String, Seq[Symbol]]

  private val replacementStack = new ArrayStack[Symbol]

  def next_token : Symbol =
    if (replacementStack.isEmpty) {

      val s = underlying.next_token

      if (s == null)
        return null

/*
    println(s)
    println(s.value)
    println("line " + underlying.line_num)
 */

      s.sym match {
        case Typedef_num => {
          recording = true
          s
        }
        case Semicolon_num if recording => {
          typedefs.put(recordedSyms.last.value.toString,
                       recordedSyms.init.reverse.toList)
//          println(typedefs)
          recording = false
          recordedSyms.clear
          s
        }
        case CIdent_num if (typedefs contains s.value.asInstanceOf[String]) => {
          // suppress this token, replace it with its definition
          for (t <- typedefs(s.value.asInstanceOf[String]))
            replacementStack push (new Symbol(t.sym, t.value))
          next_token
        }
        case _ => {
          if (recording)
            recordedSyms += s
          s
        }
      }

    } else {

      val s = replacementStack.pop

      if (recording)
        recordedSyms += s

      s

    }

}
