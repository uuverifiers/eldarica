/**
 * Copyright (c) 2011-2026 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.theories
import lazabs.horn.bottomup._
import ap.parser._
import ap.theories._
import ap.types.MonoSortedPredicate
import lazabs.horn.HornWrapper

import lazabs.horn.CHCResultMatchers
import org.scalatest.freespec.AnyFreeSpec

class ArrayTests
    extends AnyFreeSpec
    with CHCResultMatchers {

  import HornClauses._
  import IExpression._
  
  def solve(clauses : Seq[Clause]) = hideOutput {
    val predAbs = new HornPredAbs(clauses)

    predAbs.result match {
      case Right(cex) => {
        HornWrapper.verifyCEX(cex, clauses)
        Right(cex)
      }
      case Left(sol) => {
        HornWrapper.verifySolution(sol, clauses)
        Left(sol)
      }
    }
  }

  "Solving clauses over theory SimpleArray" - {
    ap.util.Debug enableAllAssertions true
    lazabs.GlobalParameters.get.assertions = true

    val ar = SimpleArray(1)
    import ar._

    "SimpleArray 1" - {
      val cnt = new ConstantTerm("cnt")
      val c = new ConstantTerm("c")
      val a = new ConstantTerm("a")
      val k = new ConstantTerm("k")
      val len = 5

      val p = for (i <- 0 until 4) yield (new Predicate("p" + i, 3))

      val clauses = List(

        p(0)(1, cnt, a)              :- true,
        p(1)(0, 0, a)                :- p(0)(1, cnt, a),
        p(2)(c, cnt, a)              :- (p(1)(c, cnt, a), cnt < len - 1),
        p(0)(c, cnt, a)              :- (p(1)(c, cnt, a), cnt >= len - 1),
        p(1)(c, cnt+1, a)            :- (p(2)(c, cnt, a), select(a, cnt) <= select(a, cnt+1)),
        p(1)(1, cnt+1,
           store(store(a, cnt,   select(a, cnt+1)),
                          cnt+1, select(a, cnt)))   :- (p(2)(c, cnt, a), select(a, cnt) > select(a, cnt+1)),

        p(3)(0, cnt, a)              :- p(0)(0, cnt, a),
        false                        :- (p(3)(c, cnt, a), k === 3,
                                         select(a, k) > select(a, k+1))

      )

      solve(clauses) should beSat
    }

    "SimpleArray 2" - {
      val x = new ConstantTerm("x")
      val y = new ConstantTerm("y")
      val z = new ConstantTerm("z")
      val a = new ConstantTerm("a")
    
      val p = for (i <- 0 until 4) yield (new Predicate("p" + i, 2))

      val clauses = List(

        p(0)(x, a)              :- true,
        p(1)(0, a)              :- p(0)(x, a),
        p(2)(x, store(a, x, x)) :- (p(1)(x, a), x < 3),
        p(1)(x+1, a)            :- p(2)(x, a),
        p(3)(x, a)              :- (p(1)(x, a), x >= 3),
        (select(a, 0) === 0)    :- p(3)(x, a)

      )

      solve(clauses) should beSat
    }
  }

  "Solving clauses over theory ExtArray" - {
    ap.util.Debug enableAllAssertions true
    lazabs.GlobalParameters.get.assertions = true

    val ar = ExtArray(List(Sort.Integer), Sort.Integer)
    import ar.{select, store, sort => IntArray}

    "ExtArray 1" - {
      val cnt = new ConstantTerm("cnt")
      val c = new ConstantTerm("c")
      val a = IntArray.newConstant("a")
      val k = new ConstantTerm("k")
      val len = 5

      val p = for (i <- 0 until 4)
              yield MonoSortedPredicate("p" + i, List(Sort.Integer, Sort.Integer, IntArray))

      val clauses = List(

        p(0)(1, cnt, a)              :- true,
        p(1)(0, 0, a)                :- p(0)(1, cnt, a),
        p(2)(c, cnt, a)              :- (p(1)(c, cnt, a), cnt < len - 1),
        p(0)(c, cnt, a)              :- (p(1)(c, cnt, a), cnt >= len - 1),
        p(1)(c, cnt+1, a)            :- (p(2)(c, cnt, a), select(a, cnt) <= select(a, cnt+1)),
        p(1)(1, cnt+1,
           store(store(a, cnt,   select(a, cnt+1)),
                          cnt+1, select(a, cnt)))   :- (p(2)(c, cnt, a), select(a, cnt) > select(a, cnt+1)),

        p(3)(0, cnt, a)              :- p(0)(0, cnt, a),
        false                        :- (p(3)(c, cnt, a), k === 3,
                                         select(a, k) > select(a, k+1))

      )

      solve(clauses) should beSat
    }

    "ExtArray 2" - {
      val x = new ConstantTerm("x")
      val y = new ConstantTerm("y")
      val z = new ConstantTerm("z")
      val a = IntArray.newConstant("a")
    
      val p = for (i <- 0 until 4)
              yield MonoSortedPredicate("p" + i, List(Sort.Integer, IntArray))

      val clauses = List(

        p(0)(x, a)              :- true,
        p(1)(0, a)              :- p(0)(x, a),
        p(2)(x, store(a, x, x)) :- (p(1)(x, a), x < 3),
        p(1)(x+1, a)            :- p(2)(x, a),
        p(3)(x, a)              :- (p(1)(x, a), x >= 3),
        (select(a, 0) === 0)    :- p(3)(x, a)

      )

      solve(clauses) should beSat
    }
  }

}
