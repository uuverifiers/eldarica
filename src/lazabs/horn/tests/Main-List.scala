/**
 * Copyright (c) 2017-2020 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.tests

import lazabs.horn.bottomup._
import ap.parser._
import ap.theories._
import ap.types.MonoSortedPredicate

object MainList extends App {

  import HornClauses._
  import IExpression._
  
  ap.util.Debug enableAllAssertions true
  lazabs.GlobalParameters.get.setLogLevel(1)
  lazabs.GlobalParameters.get.assertions = true

  val listADT =
    new ADT(List("colour", "clist"),
            List(("red",   ADT.CtorSignature(List(), ADT.ADTSort(0))),
                 ("green", ADT.CtorSignature(List(), ADT.ADTSort(0))),
                 ("blue",  ADT.CtorSignature(List(), ADT.ADTSort(0))),
                 ("nil",   ADT.CtorSignature(List(), ADT.ADTSort(1))),
                 ("cons",  ADT.CtorSignature(List(("head", ADT.ADTSort(0)),
                                                  ("tail", ADT.ADTSort(1))),
                                             ADT.ADTSort(1)))),
           ADT.TermMeasure.Size)

  println("ADT: " + listADT)

  val Seq(colour, clist) = listADT.sorts
  val Seq(red, green, blue, nil, cons) = listADT.constructors
  val Seq(_, _, _, _, Seq(head, tail)) = listADT.selectors
  val Seq(_, listSize) = listADT.termSize

  val C = MonoSortedPredicate("C", List(clist, clist, clist))
  val S = MonoSortedPredicate("S", List(clist, Sort.Integer))

  val c = colour newConstant "c"
  val n = Sort.Integer newConstant "n"
  val n2 = Sort.Integer newConstant "n2"
  val n3 = Sort.Integer newConstant "n3"
  val x = clist newConstant "x"
  val y = clist newConstant "y"
  val r = clist newConstant "r"

  def list_len(t : ITerm) = BitShiftMultiplication.eDiv(listSize(t) - 1, 2)

  val axiomClauses = List(
    C(nil(), y, y)                     :- true,
    C(cons(c, x), y, cons(c, r))       :- C(x, y, r),
    S(nil(), 0)                        :- true,
    S(cons(c, x), n+1)                 :- S(x, n)
  )

  val prop1 = List(
    (n >= 0)                           :- S(x, n)
  )

  // cannot currently be verification automatically, interpolation
  // is not clever enough
  val prop2 = List(
    (n3 === n + n2)                    :- (C(x, y, r), S(x, n), S(y, n2), S(r, n3))
  )

  val prop3 = List(
    (listSize(r) - 1 === listSize(x) - 1 + listSize(y) - 1) :- C(x, y, r)
  )
  val prop3b = List(
    (list_len(r) === list_len(x) + list_len(y)) :- C(x, y, r)
  )

  val prop4 = List(
    (n * 2 + 1 === listSize(x))        :- S(x, n)
  )

  val prop5 = List(
    ((head(x) === head(r)) | (head(y) === head(r))) :- (C(x, y, r), r =/= nil())
  )

  val clauses = axiomClauses ++ prop1 ++ prop3 ++ prop3b ++ prop4 ++ prop5

  println
  println(clauses mkString "\n")

  println
  println("Solving ...")

  println(SimpleWrapper.solve(clauses, debuggingOutput = true))

}
