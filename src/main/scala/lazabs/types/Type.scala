/**
 * Copyright (c) 2011-2018 Hossein Hojjat, Philipp Ruemmer. All rights reserved.
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

package lazabs.types

import ap.theories.{ADT, Heap}
import ap.types._

sealed abstract class Type
case class UnitType() extends Type
case class IntegerType() extends Type
case class RangeType(val lower: Int, val upper: Int) extends Type
case class BooleanType() extends Type
case class StringType() extends Type
case class AnyType() extends Type
case class ArrayType(index : Type, obj : Type) extends Type
case class HeapType(s: Sort) extends Type
case class HeapAddressType(h: Heap) extends Type
case class SetType(t: Type) extends Type
case class AdtType(s: Sort) extends Type
case class BVType(bits: Int) extends Type
case object ActorType extends Type
case class ClassType(id: String) extends Type

object ArrayType {
  def apply(obj : Type) : ArrayType = ArrayType(IntegerType(), obj)
}

trait ScalaType {
	self =>      // this-aliasing
	private var _stype: Type = UnitType()
	// Getter
	def stype  = _stype
	// Setter
	def stype( value: Type): self.type = {
		_stype = value
		self
	}
}
