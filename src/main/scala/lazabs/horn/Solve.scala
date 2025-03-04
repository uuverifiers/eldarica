/**
 * Copyright (c) 2011-2023 Hossein Hojjat and Philipp Ruemmer.
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
import bottomup.RelationSymbol
import abstractions.AbsLattice
import Util.Dag

import ap.parser._

object Solve {
  def apply(clauseSet: Seq[HornClause], 
            uppaalAbsMap: Option[Map[String, AbsLattice]], 
            global: Boolean, 
            disjunctive : Boolean, 
            drawRTree: Boolean, 
            lbe: Boolean) = {

    val log = lazabs.GlobalParameters.get.log

/*    if(clauseSet.size == 0) {
      println("No Horn clause")
      sys.exit(0)
    }       */

    val arities = clauseSet.map(cl => Horn.getRelVarArities(cl)).reduceLeft(_++_)
    val timeStart = System.currentTimeMillis

    def printTime =
      if (lazabs.GlobalParameters.get.logStat)
        Console.err.println(
          "Total elapsed time (ms): " + (System.currentTimeMillis - timeStart))

      if(global) {
        val cegar = new HornCegar(clauseSet,log)
        val arg = cegar.apply

        printTime

        if(log && cegar.status == Status.SAFE) {
          for((i,sol) <- arg.reportSolution) {
            val cl = HornClause(
              RelVar(i,(0 until arities(i)).map(p => Parameter("_" + p,lazabs.types.IntegerType())).toList),
              List(Interp(sol))
            )
            println(lazabs.viewer.HornPrinter.print(cl))
          }
        }
        if(drawRTree) lazabs.viewer.DrawGraph(arg)
      } else {

        val result = try {
          (new HornWrapper(clauseSet, uppaalAbsMap, lbe, disjunctive)).result
        } catch {
          case t@(lazabs.Main.TimeoutException |
                  lazabs.Main.StoppedException) => {
            println("unknown")
            printTime
            throw t
          }
        }

        printTime

        result match {

          case Right(_cex) => {
            if (lazabs.GlobalParameters.get.didIncompleteTransformation)
              println("unknown")
            else
              lazabs.GlobalParameters.get.format match {
                case lazabs.GlobalParameters.InputFormat.SMTHorn =>
                  println("unsat")
                case _ =>
                  println("NOT SOLVABLE")
              }

            lazy val cex = _cex()

            if (lazabs.GlobalParameters.get.assertions) {
              // make sure that the full counterexample is computed
              cex
            }

            if (lazabs.GlobalParameters.get.plainCEX) {
              println
              dagPrettyPrint(cex)
            }

            if (!lazabs.GlobalParameters.get.pngNo)
              Util.show(cex, "horn-cex")
          }

          case Left(_solution) => {
            lazabs.GlobalParameters.get.format match {
              case lazabs.GlobalParameters.InputFormat.SMTHorn =>
                println("sat")
              case _ =>
                println("SOLVABLE")
            }

            lazy val solution = _solution()

            if (lazabs.GlobalParameters.get.assertions) {
              // make sure that the full solution is computed
              solution
            }

            if (lazabs.GlobalParameters.get.displaySolutionProlog) {
                val sortedSol = solution.toArray.sortWith(_._1.name < _._1.name)
                for((pred,sol) <- sortedSol) {
                  val cl = HornClause(RelVar(pred.name,
                             (0 until pred.arity).map(p =>
                                      Parameter("_" + p,lazabs.types.IntegerType())).toList),
                      List(Interp(lazabs.prover.PrincessWrapper.formula2Eldarica(sol,
                                   Map[ap.terfor.ConstantTerm,String]().empty,false))))
                  println(lazabs.viewer.HornPrinter.print(cl))
                }
            } else if (lazabs.GlobalParameters.get.displaySolutionSMT) {
              // TODO: this should probably just use the function for printing
              // models in SMTLineariser. But will change the syntax a bit
              // and require tests to be updated

                val sortedSol = solution.toArray.sortWith(_._1.name < _._1.name)
                val builder = new StringBuilder
                for((pred,sol) <- sortedSol) yield {
                  val cl = HornClause(RelVar(pred.name,
                  (0 until pred.arity).zip(HornPredAbs.predArgumentSorts(pred).map(
                      lazabs.prover.PrincessWrapper.sort2Type(_))).map(p =>
                        Parameter("_" + p._1,p._2)
                  ).toList),
                      List(Interp(lazabs.prover.PrincessWrapper.formula2Eldarica(sol,
                                   Map[ap.terfor.ConstantTerm,String]().empty,false))))
                  builder.append("\n    ")
                  builder.append(lazabs.viewer.HornSMTPrinter.printFull(cl, true))
                }
                println(s"(${builder.toString}\n)")
            }
          }
        }
      }    
  }

  def dagPrettyPrint(cex : Dag[IFormula]) =
    if (lazabs.GlobalParameters.get.cexInSMT) {
      val smtCEX = cex map {
        f => f match {
          case IAtom(HornClauses.FALSE, _) => "false"
          case f => SMTLineariser asString f
        }
      }
      smtCEX.prettyPrint
    } else {
      cex.prettyPrint
    }
}
