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

package lazabs.horn.global

import lazabs.ast.ASTree._
import lazabs.types._ 
import scala.collection.mutable.HashMap

object HornLBE {
  /**
   * extracts the unique linear non-recursive clauses from a set of clauses that does not make a cycle 
   */
  def UniqueLinearNonRec(clauses: Seq[HornClause]): Seq[HornClause] = {
    val headToClauses = clauses.filter {
      case HornClause(Interp(_),_) => false
      case _ => true
    }.groupBy {
      case HornClause(RelVar(varName, _), body) => varName
      case _ => ""
    }
    var uniqLinears = List[HornClause]()
    var alreadyAdded = Set[String]()   // prevent cyclic clauses
    for( (headName,cls) <- headToClauses; if (cls.size == 1)) {
      val bodyVarNames = (for (RelVar(varName,_) <- cls.head.body) yield varName)
      bodyVarNames.size match {
        case 0 => uniqLinears ::= cls.head
        case 1 =>
          if(!alreadyAdded.contains(headName)) {
            alreadyAdded += bodyVarNames.head
            uniqLinears ::= cls.head
          }
        case _ =>
      }
    }
    uniqLinears
  }
    
  /**
   * inlines a set of non-recursive Horn clauses until fix-point
   */
  def inlineUntilFixpoint(originalClauses: Seq[HornClause],rules: HashMap[String,HornClause]): Seq[HornClause] = {
    var changed = true
    var finishedClauses = Seq[HornClause]()
    var unfinishedClauses = originalClauses
    while(!unfinishedClauses.isEmpty) {
      val (unreducable,reducable) = unfinishedClauses.partition {
        case HornClause(head, body) => ((for(RelVar(vn,_) <- body) yield vn).toSet intersect rules.keySet).isEmpty  
      }
      unfinishedClauses = reducable.map {
        case HornClause(head, body) => HornClause(head, body.map {
            case RelVar(callName,callParams) if (rules.contains(callName)) =>
              val HornClause(RelVar(_,replaceParams),replaceBody) = Horn.fresh(rules(callName))
              val replaceMap = replaceParams.zip(callParams).map(pp => (pp._1.name,pp._2.name)).toMap
              replaceBody.map {
                case RelVar(rbName,rbParams) => RelVar(rbName,rbParams.map(p => Parameter(replaceMap.getOrElse(p.name,p.name),IntegerType()))) 
                case Interp(rbFunc) => Interp(lazabs.utils.Manip.substitute(rbFunc, replaceMap.map(pp => (Variable(pp._1).stype(IntegerType()),Variable(pp._2).stype(IntegerType())))))
              }
            case l@_ => List(l)
          }.flatten
        )
      }
      finishedClauses ++= unreducable
    }
    finishedClauses
  }
  
  def linearClausesToMap(clauses: Seq[HornClause]): HashMap[String,HornClause] = {
    new HashMap[String,HornClause]() ++ ((for (hc@HornClause(RelVar(vName,_),_) <- clauses) yield (vName,hc)).toMap)
  }

  def apply(originalClauses: Seq[HornClause]): Seq[HornClause] = {
    var linearNonRecCls = UniqueLinearNonRec(originalClauses)
    var result = originalClauses
    while(!linearNonRecCls.isEmpty) {
      val rules = linearClausesToMap(inlineUntilFixpoint(linearNonRecCls,linearClausesToMap(linearNonRecCls)))
      result = inlineUntilFixpoint(result.diff(linearNonRecCls),rules)
      linearNonRecCls = UniqueLinearNonRec(result)
    }
    result
  }
}