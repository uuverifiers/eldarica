/**
 * Copyright (c) 2011-2014 Hossein Hojjat. All rights reserved.
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

package lazabs.bip

import lazabs.ast.ASTree._
import lazabs.horn.global._
import lazabs.types._


object BipAst {
  // BIP module
  case class BModule(
    val connectorTypes:              Seq[BConnectorType],
    val compoundType:                BCompoundType
  )

  // compound type
  case class BCompoundType(
    val connectors:                  Seq[BConnector],
    val compToNum:                   Map[String,Int],                  // map from component name to integer
    val components:                  Seq[BComponent]
  )
  
  // component object
  case class BComponent(
    val cName:                       String,
    val cType:                       BAtomicType
  )

  // parameter with type
  case class BParameter(
    val pName:                       String, 
    val pType:                       String
  )

  // connector type
  case class BConnectorType(
    val name:                        String,
    val portParams:                  Seq[BParameter]
  )

  case class BPortReference(
    val ref:                         String, 
    val field:                       String
  )

  // connector object
  case class BConnector(
    val name:                        String,
    val typeName:                    String,
    val referedPorts:                Seq[BPortReference]
  )

  // atomic type for components
  case class BAtomicType(
    val ports:                       Seq[BParameter],                  // ports defined in the atomic type
    val placeToNum:                  Map[String,Int],                  // map from place to integer
    val initial:                     String,
    val transitions:                 Seq[BTransition]
  )

  // transition
  case class BTransition(
    val origin:                      String,
    val trigger:                     BParameter,
    val guard:                       Option[Expression],
    val action:                      Option[Expression],
    val dest:                        String
  )
}