/**
 * Copyright (c) 2022 Zafer Esen, Philipp Ruemmer. All rights reserved.
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
package lazabs.horn.symex

import lazabs.horn.bottomup.{NormClause, RelationSymbol}
import ap.terfor.preds.Predicate

import scala.collection.{AbstractSeq, IndexedSeqLike}
import scala.collection.mutable.{
  ListBuffer,
  ArrayBuffer => MArrayBuffer,
  HashMap => MHashMap,
  HashSet => MHashSet,
  LinkedHashSet => MLinkedHashSet,
  Stack => MStack
}

/**
 * Class to keep track of CUCs
 * Also keeps track of execution paths, i.e., clauses used to generate a CUC.
 */
class UnitClauseDB(preds: Set[RelationSymbol]) {
  // for each predicate, keep an ordered set of inferred unit clauses
  // caution: the code in pop below will break if this map is made mutable and
  //           the predicates change over time!
  private val inferredCUCsForPred =
    new MHashMap[RelationSymbol, Vector[UnitClause]]
  preds.foreach(pred => inferredCUCsForPred += ((pred, Vector())))

  private var cucs: collection.immutable.Vector[UnitClause] = Vector()

  private var cucParents
    : collection.immutable.Vector[(UnitClause, (NormClause, Set[UnitClause]))] =
    Vector()

  private case class FrameInfo(numCUCs:                Int,
                               numInferredCUCsForPred: Map[RelationSymbol, Int])

  private val frameStack = new MStack[FrameInfo]

  /**
   * Getters and predicates of the database
   */
  def head = cucs.head
  def last = cucs.last
  def headOption: Option[UnitClause] = cucs.headOption
  def lastOption = cucs.lastOption
  def apply(cucIndex: Int): UnitClause = cucs(cucIndex)
  def size:     Int     = cucs.size
  def isEmpty:  Boolean = cucs isEmpty
  def nonEmpty: Boolean = cucs nonEmpty

  /**
   * @param child to return parents for
   * @return optionally, the parents for the child unit clause
   */
  def parentsOption(child: UnitClause): Option[(NormClause, Set[UnitClause])] =
    cucParents find (_._1 == child) match {
      case Some((_, parents)) => Some(parents)
      case None               => None
    }

  def inferred(rel: RelationSymbol): Option[Vector[UnitClause]] =
    inferredCUCsForPred get rel

  /**
   * Push a snapshot of the database into the stack.
   * returns: the latest number of frames
   */
  def push(): Int = {
    assert(cucs.length == cucParents.length) // todo: convert to Eldarica
    // assertion or remove
    frameStack push
      FrameInfo(
        numCUCs = cucs.length,
        numInferredCUCsForPred = (inferredCUCsForPred.map {
          case (pred, cucs) => (pred, cucs.length)
        }).toMap
      )
    //println("(DB) Pushed " + frameStack.length)
    //println("(DB) Last " + cucs.last)
    frameStack.length
  }

  /**
   * Restore the database to its last pushed state.
   * returns: the latest number of frames
   */
  def pop(): Int = {
    val frameInfo = frameStack.pop()
    val dropCount = cucs.size - frameInfo.numCUCs
    cucs = cucs.dropRight(dropCount)
    cucParents = cucParents.dropRight(dropCount)
    inferredCUCsForPred.foreach {
      case (pred, inferredCucs) =>
        val oldSize = frameInfo.numInferredCUCsForPred(pred)
        val newSize = inferredCUCsForPred(pred).length
        inferredCUCsForPred(pred) = inferredCucs.dropRight(newSize - oldSize)
    }
    //println("(DB) Popped " + frameStack.length)
    //println("(DB) Last " + cucs.last)
    frameStack.length
  }

  /**
   * Add a clause to the database. Returns true if inserted, false if unit
   * clause already exists in the database.
   * @param clause to be inserted.
   * @param parents the nucleus and the electrons used in the derivation of this
   *                unit clause.
   * @return true if inserted, false if unit clause exists in the database
   */
  def add(clause:  UnitClause,
          parents: (NormClause, Set[UnitClause])): Boolean = {
    if (cucs contains clause) {
      false
    } else {
      cucs = cucs :+ clause
      cucParents = cucParents :+ ((clause, parents))
      inferredCUCsForPred(clause.rs) :+ clause
      true
    }
  }

  // todo: which datatype to use for cucs? support removal?
  //def remove(clauses: Set[UnitClause]): Unit = {
  //  clauses.foreach(cucs -= _)
  //  clauses.foreach(cuc =>
  //    cucParents.filter(_._1 == cuc).foreach(pair => cucParents -= pair))
  //  clauses.foreach(cuc => inferredCUCsForPred(cuc.rel) -= cuc)
  //}

//    def getAllParents(clause : UnitClause) : Set[UnitClause] = {
//      getAllParentsHelper(clause, Set())
//    }
//    @tailrec
//    private def getAllParentsHelper(clause : UnitClause, acc
//    : Set[UnitClause]) :
//    Set[UnitClause] = {
//      val curParents: Set[UnitClause] = cucParents.filter(p => p._1 ==
//      clause).flatMap(_._2).toSet
//      val newAcc = acc union curParents
//      val remParents = curParents diff acc
//      ??? // how to list all parents?
//    }

}
