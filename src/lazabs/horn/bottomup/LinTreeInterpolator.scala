/**
 * Copyright (c) 2011-2019 Philipp Ruemmer. All rights reserved.
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
import ap.util.Timeout

import ap.proof.certificates.{CertificatePrettyPrinter, CertFormula}

import lazabs.prover.Tree

import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet,
                                 HashMap => MHashMap}

/**
 * Simple implementation of tree interpolation, in which the formulas of
 * the tree interpolant are extracted one by one from a proof
 */
object LinTreeInterpolator extends TreeInterpolator {

  def computeInts(cert : Certificate,
                  partNames : Tree[PartName],
                  namedParts : Map[PartName, Conjunction],
                  problem  : Tree[Conjunction],
                  symbolTranslation : Tree[Map[ConstantTerm, ConstantTerm]],
                  order : TermOrder) : Tree[Conjunction] = {
    
    val allNames = partNames.toSet

//      print("Found proof (" + cert.inferenceCount + "), simplifying ")
      val simpCert = ProofSimplifier(cert) // simplify the proof if possible
//      println("(" + simpCert.inferenceCount + ")")

    /*
      Some code for printing the generated proof:

      val formulaParts = namedParts mapValues {
        f => CertFormula(f.negate)
      }
      val printer = new ap.proof.certificates.CertificatePrettyPrinter (new CertificatePrettyPrinter.PrincessFormulaPrinter(Map()))
      printer(List(cert), formulaParts)
    */

      def computeInts(names : Tree[PartName],
                      fors  : Tree[Conjunction],
                      intKnown : Option[Conjunction]) : Tree[Conjunction] = {
        val Tree(rootFor, forChildren) = fors

        val thisInt =
          if (intKnown.isDefined) {
            intKnown.get
          } else if (fors.iterator forall (_.isTrue)) {
            // trivial sub-tree
            Conjunction.TRUE
          } else {
            val subNames = names.toList
            val superNames = (allNames -- subNames).toList
            val spec = IInterpolantSpec(subNames, superNames)
            val iContext = InterpolationContext(namedParts, spec, order)
            Interpolator(simpCert, iContext, true)
          }

        if (thisInt.isTrue) {
          // interpolants in the whole subtree can be assumed to be true
          for (_ <- names) yield Conjunction.TRUE
        } else {
          val kI =
            if (rootFor.isTrue && names.children.size == 1)
              Some(thisInt)
            else
              None
          Tree(thisInt,
               for ((s, f) <- names.children zip forChildren)
                 yield computeInts(s, f, kI))
        }
      }

/*
        val trueRightParts = new ArrayBuffer[Set[PartName]]
        Left(for (s <- partitions) yield {
          if (s.right.isEmpty) {
            Conjunction.FALSE
          } else if (trueRightParts exists {
                       case rp => rp subsetOf s.right.toSet }) {
            Conjunction.TRUE
          } else {
            val iContext = InterpolationContext(namedParts, s, order)
            val interpolant = Interpolator(simpCert, iContext, true)
            if (interpolant.isTrue)
              trueRightParts += s.right.toSet
            interpolant
          }
        })
*/

    Timeout.withChecker(lazabs.GlobalParameters.get.timeoutChecker) {
      computeInts(partNames, problem, Some(Conjunction.FALSE))
    }
  }

}
