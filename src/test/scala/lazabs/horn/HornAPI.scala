/**
 * Copyright (c) 2024 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

import ap.SimpleAPI
import ap.parser._

import lazabs.horn.bottomup.HornClauses

import org.scalatest.freespec.AnyFreeSpec

class HornAPITests extends AnyFreeSpec {

  import HornClauses._
  import IExpression._

  val CEGAROpt = new HornAPI.CEGAROptions {
    override val enableAssertions = true
  }
  val SymExOpt = new HornAPI.SymexOptions {
    override val enableAssertions = true
  }

  val allOptions = List(CEGAROpt, SymExOpt)

  "Bounded tests" - {

    "Safe" - {
      SimpleAPI.withProver(enableAssert = true) { p =>
        import p._
      
        val p0 = createRelation("p0", List(Sort.Integer))
        val p1 = createRelation("p1", List(Sort.Integer))
        val p2 = createRelation("p2", List(Sort.Integer))
        val x  = createConstant("x")

        val clauses: Seq[Clause] = List(
          p0(x) :- (x > 2),
          p1(x) :- (p0(x), x > 0),
          p0(x - 1) :- p1(x),
          p2(x) :- (p0(x), x <= 0),
          (x >= 0) :- p2(x)
        )

        for (options <- allOptions) {
          val api = new HornAPI(options)
          val res = api.solveLazily(clauses)
          assert(res.isLeft)
          val res2 = api.solve(clauses)
          assert(res2.isLeft)
          val res3 = api.isSat(clauses)
          assert(res3)
        }
      }
    }

    "Unsafe" - {
      SimpleAPI.withProver(enableAssert = true) { p =>
        import p._

        val p0 = createRelation("p0", List(Sort.Integer, Sort.Integer))
        val p1 = createRelation("p1", List(Sort.Integer, Sort.Integer))
        val x  = createConstant("x")
        val i  = createConstant("i")

        /*
         int x = 10, i = 0;
         while(i < 5) {
         if(i == 3) assert(x != 4);
         x -= 2;
         i++;
         }
         */

        val clauses: Seq[Clause] = List(
          p0(x, i) :- (x === 10, i === 0),
          p0(x - 2, i + 1) :- (p0(x, i), i =/= 3 & 5 - i >= 1),
          p1(x, i) :- (p0(x, i), i === 3 & 5 - i >= 1),
          p0(x - 2, i + 1) :- p1(x, i),
          false :- (p1(x, i), x === 4)
        )

        for (options <- allOptions) {
          val api = new HornAPI(options)
          val res = api.solveLazily(clauses)
          assert(res.isRight)
          val res2 = api.solve(clauses)
          assert(res2.isRight)
          val res3 = api.isSat(clauses)
          assert(!res3)
        }
      }
    }
  }

}
