/**
 * Copyright (c) 2011-2018 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.bottomup

import ap.interpolants.{ProofSimplifier, InterpolationContext, Interpolator}
import ap.parser.{PartName, IInterpolantSpec}
import ap.proof.certificates.Certificate
import ap.terfor.conjunctions.Conjunction
import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.substitutions.ConstantSubst

import lazabs.prover.Tree

import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet,
                                 HashMap => MHashMap}

/**
 * Optimised version of tree interpolation, in which binary search
 * is used to minimise the number of formulas that have to be extracted
 * from a proof
 */
object BSTreeInterpolator extends TreeInterpolator {

  def computeInts(cert : Certificate,
                  names : Tree[PartName],
                  namedParts : Map[PartName, Conjunction],
                  fors  : Tree[Conjunction],
                  symbolTranslation : Tree[Map[ConstantTerm, ConstantTerm]],
                  order : TermOrder) : Tree[Conjunction] = {

    val allNames = names.toSet

//    print("Found proof (" + cert.inferenceCount + "), simplifying ")
    val simpCert = ProofSimplifier(cert)
//    println("(" + simpCert.inferenceCount + ")")

    def interpolate(subNames : List[PartName]) : Conjunction = {
      val superNames = (allNames -- subNames).toList
      if (superNames.isEmpty) {
        Conjunction.FALSE
      } else {
        val spec = IInterpolantSpec(subNames, superNames)
        val iContext = InterpolationContext(namedParts, spec, order)
        Interpolator(simpCert, iContext, true)
      }
    }

    def computeSeqInts(namesBuffer : ArrayBuffer[PartName],
                       afterNames : List[PartName],
                       begin : Int,
                       end : Int,
                       result : Array[Conjunction]) : Unit =
      if (begin + 1 < end) {
        if (result(begin) == result(end)) {
          for (n <- (begin + 1) until end)
            result(n) = result(begin)
        } else {
          val mid = (begin + end) / 2
          val subNames = namesBuffer.view(mid, end).toList ::: afterNames
          result(mid) = interpolate(subNames)
          computeSeqInts(namesBuffer, subNames, begin, mid, result)
          computeSeqInts(namesBuffer, afterNames, mid, end, result)
        }
      }

    def computeTreeInts(names : Tree[PartName]) : Tree[Conjunction] = {
      val thisInt = interpolate(names.toList)
  
      if (thisInt.isTrue) {
        // interpolants in the whole subtree can be assumed to be true
        for (_ <- names) yield Conjunction.TRUE
      } else {
        val Tree(namesRoot, namesChildren) = names

        if (namesChildren.size == 1) {
          // optimised sequence interpolation mode

          val namesBuffer = new ArrayBuffer[PartName]
          namesBuffer += namesRoot

          var subNames = namesChildren.head
          while (subNames.children.size == 1) {
            namesBuffer += subNames.d
            subNames = subNames.children.head
          }

          val afterNames = subNames.toList
          val lastInt = interpolate(afterNames)

          val result = new Array[Conjunction](namesBuffer.size + 1)

          result(0) = thisInt
          result(namesBuffer.size) = lastInt

          computeSeqInts(namesBuffer, afterNames, 0, namesBuffer.size, result)

          var res =
            if (lastInt.isTrue)
              for (_ <- subNames) yield Conjunction.TRUE
            else
              Tree(lastInt,
                   for (s <- subNames.children) yield computeTreeInts(s))

          for (n <- (namesBuffer.size - 1) to 0 by -1)
            res = Tree(result(n), List(res))

          res
        } else {
          Tree(thisInt, for (s <- names.children) yield computeTreeInts(s))
        }
      }
    }

    val rawInts = computeTreeInts(names)

    for (p <- rawInts zip symbolTranslation) yield {
      val trans = (for ((c, d) <- p._2.iterator) yield (d, c)).toMap
      ConstantSubst(trans, order)(p._1)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  override def propagateSymbols(problem : Tree[Conjunction],
                                order : TermOrder)
                             : (Tree[Conjunction],
                                Tree[Map[ConstantTerm, ConstantTerm]]) = {

    val symOccurrenceNum = new MHashMap[ConstantTerm, Int]
    for (c <- problem) {
      for (s <- c.constants)
        symOccurrenceNum.put(s, symOccurrenceNum.getOrElse(s, 0) + 1)
    }

    def prop(subProblem : Tree[Conjunction])
            : (Tree[Conjunction],
               MHashMap[ConstantTerm, Int],
               MHashSet[ConstantTerm],
               Tree[Map[ConstantTerm, ConstantTerm]]) = {
      val Tree(conjunct, children) =
        subProblem
      val (newChildren, childNums, childLocalSyms, childReplacements) =
        unzip4(children map (prop(_)))

      val allRepls =
        (for (repl <- childReplacements.iterator; (c, d) <- repl.d.iterator)
         yield (c, d)).toMap

      val newConjunct = ConstantSubst(allRepls, order)(conjunct)

      val newLocalSyms = childLocalSyms match {
        case List() =>
          new MHashSet[ConstantTerm]
        case syms :: rest => {
          for (s <- rest)
            syms ++= s
          syms
        }
      }

      val newNums = childNums match {
        case List() =>
          new MHashMap[ConstantTerm, Int]
        case nums :: rest => {
          for (n <- rest)
            for ((c, num) <- n) {
              val newNum = nums.getOrElse(c, 0) + num
              if (newNum == symOccurrenceNum(c))
                newLocalSyms += c
              nums.put(c, newNum)
            }
          nums
        }
      }

      val replacementCandidates = new MHashSet[ConstantTerm]

      for (c <- conjunct.constants) {
        val totalNum = symOccurrenceNum(c)
        val newNum = newNums.getOrElse(c, 0) + 1

        if (newNum == 1 && totalNum == 2)
          replacementCandidates += c
        else if (newNum == totalNum)
          newLocalSyms += c

        newNums.put(c, newNum)
      }

      val replacements = new MHashMap[ConstantTerm, ConstantTerm]
      val usedLocalSyms = new MHashSet[ConstantTerm]

      if (!replacementCandidates.isEmpty && !newLocalSyms.isEmpty)
        for (lc <- newConjunct.arithConj.positiveEqs)
          if (isSimpleEq(lc)) {
            val c = (lc getTerm 0).asInstanceOf[ConstantTerm]
            val d = (lc getTerm 1).asInstanceOf[ConstantTerm]
            if (newLocalSyms(c) &&
                !usedLocalSyms(c) &&
                replacementCandidates(d)) {
              replacements.put(d, c)
              usedLocalSyms += c
            } else if (newLocalSyms(d) &&
                       !usedLocalSyms(d) &&
                       replacementCandidates(c)) {
              replacements.put(c, d)
              usedLocalSyms += d
            }
          }

      (Tree(newConjunct, newChildren),
       newNums, newLocalSyms, Tree(replacements.toMap, childReplacements))
    }

    val (newProblem, _, _, replacements) = prop(problem)

    (newProblem, replacements)
  }

  def unzip4[A, B, C, D](l : List[(A, B, C, D)])
            : (List[A], List[B], List[C], List[D]) = l match {
    case List() =>
      (List(), List(), List(), List())
    case (a, b, c, d) :: rest => {
      val (la, lb, lc, ld) = unzip4(rest)
      (a :: la, b :: lb, c :: lc, d :: ld)
    }
  }

}