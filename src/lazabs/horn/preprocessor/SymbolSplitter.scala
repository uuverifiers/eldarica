/**
 * Copyright (c) 2018 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.preprocessor

import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.parser.HornReader

import ap.basetypes.IdealInt
import ap.parser._
import ap.types.MonoSortedPredicate
import ap.types.Sort
import IExpression._
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}
import scala.collection.immutable.BitSet

/**
 * Preprocessor that clones relation symbols that always receive
 * concrete values as some of the arguments.
 */
object SymbolSplitter extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "cloning of relation symbols"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {

    val clauseArguments =
      for (clause <- clauses) yield concreteArguments(clause)

    val concreteArgsPerPred =
      (for ((clause, allArgs) <-
              clauses.iterator zip clauseArguments.iterator;
            (IAtom(p, _), args) <-
              clause.allAtoms.iterator zip allArgs.iterator;
            bits =
              BitSet((for ((Some(_), i) <- args.zipWithIndex) yield i) : _*))
       yield (p -> bits)).toSeq groupBy (_._1) mapValues {
         bits => (bits map (_._2)) reduceLeft (_ & _)
       }

    if (concreteArgsPerPred.valuesIterator forall (_.isEmpty)) {

      (clauses, hints, IDENTITY_TRANSLATOR)

    } else {

      // duplicate relation symbols with concrete arguments

      val predMapping = new MHashMap[(Predicate, Seq[ITerm]), Predicate]
      val clauseBackMapping = new MHashMap[Clause, Clause]

      def renamePred(p : Predicate,
                     concreteArgs : Seq[Option[ITerm]]) : Option[Predicate] = {
        val fixedArgPositions = concreteArgsPerPred(p)
        if (fixedArgPositions.isEmpty) {
          None
        } else {
          val fixedArgs =
            (for ((a, i) <- concreteArgs.zipWithIndex;
                  if fixedArgPositions contains i)
             yield a.get).toList
          Some(predMapping.getOrElseUpdate(
                 (p, fixedArgs),
                 MonoSortedPredicate(p.name + "_" + predMapping.size,
                                     predArgumentSorts(p))))
        }
      }

      def renameFormalArgs(p : Predicate,
                           args : Seq[ITerm]) : Seq[ITerm] = {
        val fixedArgPositions = concreteArgsPerPred(p)
        (for ((arg, argNum) <- args.iterator.zipWithIndex) yield {
           if (fixedArgPositions contains argNum) {
             // we can use a fresh constant as argument, since
             // the value of the argument is determined by the constraint
             // anyway
             IConstant(new ConstantTerm (p.name + "_" + argNum))
           } else {
             arg
           }
         }).toList
      }

      val newClauses =
        (for ((clause, concreteArgs) <-
                clauses.iterator zip clauseArguments.iterator) yield {
          val newLits =
            for ((IAtom(p, as), concArgs) <- clause.allAtoms zip concreteArgs)
            yield (for (newP <- renamePred(p, concArgs))
                   yield IAtom(newP, renameFormalArgs(p, as)))

          if (newLits exists (_.isDefined)) {
            val allLits =
              for ((nl, a) <- newLits zip clause.allAtoms)
              yield (nl getOrElse a)
            val newClause =
              Clause(allLits.head, allLits.tail, clause.constraint)
            clauseBackMapping.put(newClause, clause)
            newClause
          } else {
            clauseBackMapping.put(clause, clause)
            clause
          }
        }).toIndexedSeq

      val allNewPredicates = new MHashMap[Predicate, List[Predicate]]

      for (((p, _), newP) <- predMapping)
        allNewPredicates.put(p, newP :: allNewPredicates.getOrElse(p, List()))

      val newHints = hints duplicatePredicates {
        p => allNewPredicates.getOrElse(p, List(p))
      }

      val predBackMapping =
        (for ((p, newP) <- predMapping.iterator) yield (newP, p)).toMap

      val translator = new BackTranslator {

        def translate(solution : Solution) =
          if (predBackMapping.isEmpty) {
            solution
          } else {
            val aggregatedFormulas = new MHashMap[Predicate, IFormula]
            val sortedSolution = solution.toIndexedSeq.sortBy(_._1.name)
            for ((p, sol) <- sortedSolution) (predBackMapping get p) match {
              case Some((oldPred, fixedArgs)) => {
                val bits =
                  concreteArgsPerPred(oldPred)

                var offset = -1
                val subst =
                  for (ind <- (0 until oldPred.arity).toList) yield
                    if (bits contains ind) {
                      offset = offset + 1
                      fixedArgs(offset)
                    } else {
                      v(ind)
                    }

                val simpSol = SimplifyingVariableSubstVisitor(sol, (subst, 0))

                val newSol =
                  and(for ((ind, arg) <- bits.iterator zip fixedArgs.iterator)
                      yield arg match {
                        // don't introduce a simple equation in case of
                        // False, this would be too strong
                        case Sort.MultipleValueBool.False =>
                          (v(ind) =/= Sort.MultipleValueBool.True)
                        case arg =>
                          (v(ind) === arg)
                      }) &&& simpSol
                aggregatedFormulas.put(
                  oldPred,
                  aggregatedFormulas.getOrElse(oldPred, i(false)) ||| newSol)
              }

              case None =>
                aggregatedFormulas.put(p, sol)
            }

            aggregatedFormulas.toMap
          }

        def translate(cex : CounterExample) =
          if (predBackMapping.isEmpty) {
            cex
          } else {
            for (p <- cex) yield {
              val IAtom(pred, args) = p._1
              val newAtom = (predBackMapping get pred) match {
                case Some((oldPred, fixedArgs)) => {
                  val fixedArgPositions = concreteArgsPerPred(oldPred)
                  var fixedArgInd = 0
                  val fullArgs =
                    (for ((arg, argNum) <- args.iterator.zipWithIndex) yield {
                       if (fixedArgPositions contains argNum) {
                         fixedArgInd = fixedArgInd + 1
                         fixedArgs(fixedArgInd - 1)
                       } else {
                         arg
                       }
                     }).toList
                  IAtom(oldPred, fullArgs)
                }
                case None => p._1
              }
              (newAtom, clauseBackMapping(p._2))
            }
          }
      }

      (newClauses, newHints, translator)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def concreteArguments(clause : Clause) : Seq[Seq[Option[ITerm]]] = {
    import Sort.:::
    import Sort.MultipleValueBool.{True, False}

    val constValue = new MHashMap[ConstantTerm, ITerm]

    // TODO: generalise to terms with constructors
    object ConcreteTerm {
      def unapply(t : ITerm) : Option[ITerm] = t match {
        case t : IIntLit                  => Some(t)
        case IConstant(c)                 => constValue get c
        case True | False                 => Some(t)
        case _                            => None
      }
    }

    val literals =
      LineariseVisitor(Transform2NNF(clause.constraint), IBinJunctor.And)

    var oldConstSize = -1
    while (constValue.size > oldConstSize) {
      oldConstSize = constValue.size
      for (f <- literals) f match {
        case Eq(IConstant(c), ConcreteTerm(t)) =>
          constValue.getOrElseUpdate(c, t)
        case Eq(ConcreteTerm(t), IConstant(c)) =>
          constValue.getOrElseUpdate(c, t)

        // special handling of Boolean values
        case INot(EqZ(IConstant(c) ::: BoolSort())) =>
          constValue.getOrElseUpdate(c, False)

        case INot(Eq(IConstant(c) ::: BoolSort(),
                     IIntLit(IdealInt.ONE) | False)) =>
          constValue.getOrElseUpdate(c, False)
        case INot(Eq(IIntLit(IdealInt.ONE) | False,
                     IConstant(c) ::: BoolSort())) =>
          constValue.getOrElseUpdate(c, True)

        case _ =>
          // nothing
      }
    }

    // make sure that Booleans are not represented using numbers
    constValue transform {
      case (c, IIntLit(IdealInt.ZERO)) if BoolSort.unapply(Sort sortOf c) =>
        True
      case (c, IIntLit(IdealInt.ONE)) if BoolSort.unapply(Sort sortOf c) =>
        False
      case (_, t) =>
        t
    }

    for (IAtom(_, args) <- clause.allAtoms)
    yield (for (a <- args) yield (ConcreteTerm unapply a))
  }

  private object BoolSort {
    def unapply(s : Sort) : Boolean = s match {
      case Sort.Bool              => true
      case Sort.MultipleValueBool => true
      case _                      => false
    }
  }

}