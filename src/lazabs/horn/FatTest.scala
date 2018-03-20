/**
 * Copyright (c) 2011-2016 Hossein Hojjat and Philipp Ruemmer.
 * All rights reserved.
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

import lazabs.ast.ASTree._
import global._
import bottomup._
import java.io.File

object FatTest {
  
  def recursiveListFiles(f: File): Array[File] = {
    val these = f.listFiles
    these ++ these.filter(_.isDirectory).flatMap(recursiveListFiles)
  }
  
  def apply(directory: String) = {
    val files = recursiveListFiles(new File(directory)).filter(file => file.getName.endsWith("smt2"))
    val allClauses : List[(Seq[HornClause],String)] = files.map{ file =>
      (lazabs.horn.parser.HornReader.fromSMT(file.getPath()),file.getName())
    }.toList
    if(allClauses.size != 0) {
      // -----  Just to wake up Java -----
      new HornWrapper(allClauses.head._1.take(10), None, true, false)
      new HornWrapper(allClauses.head._1.take(10), None, true, false)
      new HornWrapper(allClauses.head._1.take(10), None, true, false)
      // ---------------------------------
      allClauses.foreach{ clauseSet =>
        var timeStart = System.currentTimeMillis

        /*HornWrapper(constraints: Seq[HornClause],
         * absMap: Option[Map[String, AbsLattice]],
         * lbe: Boolean,
         * log : Boolean,
         * disjunctive : Boolean,
         * interpolatorType : (Boolean, Boolean))
         */

        new HornWrapper(clauseSet._1, None, false, false)
        println("time for " + clauseSet._2 + " in TI : " + (System.currentTimeMillis - timeStart) + " milli-seconds")
        timeStart = System.currentTimeMillis
        new HornWrapper(clauseSet._1, None, false, false)
        println("time for " + clauseSet._2 + " in DI : " + (System.currentTimeMillis - timeStart) + " milli-seconds")
      }
    }
  }
}
