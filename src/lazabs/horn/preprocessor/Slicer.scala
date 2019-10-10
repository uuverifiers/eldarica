/**
 * Copyright (c) 2016-2019 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.bottomup.{HornClauses, HornPredAbs}
import lazabs.horn.bottomup.Util.{Dag, DagNode, DagEmpty}
import lazabs.horn.abstractions.VerificationHints
import HornClauses._

import ap.theories.ADT
import ap.basetypes.IdealInt
import ap.parser._
import ap.types.MonoSortedPredicate
import IExpression._
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer, BitSet => MBitSet}

/**
 * Slice clauses by removing arguments that are never read later on.
 */
object Slicer extends HornPreprocessor {

  import HornPreprocessor._

  val name : String = "slicing"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val usedArgs =
      determineUsedArguments(clauses)
    val (newClauses, clauseMapping, predMapping) =
      elimArguments(clauses, usedArgs)
    val predBackMapping =
      (for ((p1, p2) <- predMapping.iterator) yield (p2, p1)).toMap

    ////////////////////////////////////////////////////////////////////////////
    // Back-translation of solutions

    val translator = new BackTranslator {
    
      def translate(solution : Solution) =
        (for ((newPred, sol) <- solution.iterator) yield
          (predBackMapping get newPred) match {
            case Some(pred) => {
              val used = usedArgs(pred)
              val shifts =
                (for ((oldInd, newInd) <- used.iterator.zipWithIndex)
                 yield (oldInd - newInd)).toList
              (pred, VariablePermVisitor(sol, IVarShift(shifts, 0)))
            }
            case None =>
              (newPred, sol)
          }).toMap
          
      def translate(cex : CounterExample) =
        if (clauseMapping == null)
          cex
        else SimpleAPI.withProver { p =>
          translateHelp(cex)(p)
        }

      private def translateHelp(cex : CounterExample)
                               (implicit p : SimpleAPI) : CounterExample =
        cex match {
          case DagNode((state@IAtom(newHeadPred, newHeadArgs), clause),
                       children, next) => {
            val newNext = translateHelp(next)
            val oldClause@Clause(head, body, constraint) =
              clauseMapping(clause)
            
            if ((clause eq oldClause) ||
                !(predBackMapping contains newHeadPred)) {
              DagNode((state, oldClause), children, newNext)
            } else {
              val bodyStates =
                for (c <- children) yield newNext(c - 1)._1
              val simpleMapping =
                (for ((IAtom(_, formal), IAtom(_, actual)) <-
                        body.iterator zip bodyStates.iterator;
                      (IConstant(c), t) <- formal.iterator zip actual.iterator)
                 yield (c, t)).toMap

              val usedHeadArgs = usedArgs(head.pred)
              val argIt = newHeadArgs.iterator
              val oldHeadArgs =
                (for ((t, i) <- head.args.iterator.zipWithIndex) yield {
                   if (usedHeadArgs contains i)
                     argIt.next
                   else
                     SimplifyingConstantSubstVisitor(t, simpleMapping) match {
                       case ConcreteTerm(t) => t
                       case _ => null
                     }
                 }).toList

              val completeOldHeadArgs =
                if (oldHeadArgs contains null) p.scope {
                  // do a more expensive semantic inference of the head state
                  import p._

                  addConstants(
                    oldClause.constants.toSeq.sortWith(_.name < _.name))

                  !! (constraint)
                  for ((IAtom(_, formal), IAtom(_, actual)) <-
                         body.iterator zip bodyStates.iterator)
                    !! (formal === actual)

                  !! (clause.head.args === newHeadArgs)

                  val stat = ???
                  assert(stat == ProverStatus.Sat)
                  
                  for (t <- head.args) yield evalToTerm(t)
                } else {
                  oldHeadArgs
                }

              val newState = IAtom(head.pred, completeOldHeadArgs)
              DagNode((newState, oldClause), children, newNext)
            }
          }
          case DagEmpty => DagEmpty
        }
    }

    ////////////////////////////////////////////////////////////////////////////
    // Hints need to be adapted

    val newHints =
      if (predMapping.isEmpty) {
        hints
      } else {
        val newPredicateHints =
          (for ((pred, hintList) <- hints.predicateHints.iterator;
                newPred = predMapping.getOrElse(pred, pred);
                newList =
                  if (newPred eq pred) {
                    hintList
                  } else {
                    val used = usedArgs(pred)
                    val mapping =
                      (for ((oldInd, newInd) <- used.iterator.zipWithIndex)
                       yield (oldInd, newInd - oldInd)).toMap
                    for (hint <- hintList;
                         newHint <- hint.shiftArguments(mapping))
                    yield newHint
                  }
                if !newList.isEmpty)
           yield (newPred, newList)).toMap

        VerificationHints(newPredicateHints)
      }

    (newClauses, newHints, translator)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def determineUsedArguments(clauses : Clauses)
                              : Map[Predicate, MBitSet] = {
    val clausesWithHead = clauses groupBy (_.head.pred)
    val usedArgs = new MHashMap[Predicate, MBitSet]

    for (clause <- clauses; pred <- clause.predicates)
      if (!(usedArgs contains pred))
        usedArgs.put(pred, new MBitSet)

    { // initially mark all arguments read in clauses
      val argIndexes = new MHashMap[ConstantTerm, (Predicate, Int)]
      val seenConsts = new MHashSet[ConstantTerm]

      def makeConstUsed(argC : ConstantTerm) : Unit =
        (argIndexes get argC) match {
          case Some((otherPred, otherArgInd)) => {
            usedArgs(otherPred) += otherArgInd
            argIndexes -= argC
          }
          case None => // nothing
        }

      for (Clause(_, body, constraint) <- clauses) {
        seenConsts ++= SymbolCollector constants constraint

        for (IAtom(pred, args) <- body.iterator;
             usedArgSet = usedArgs(pred);
             (arg, argInd) <- args.iterator.zipWithIndex)
          arg match {
            case IConstant(argC) =>
              if (seenConsts add argC) {
                argIndexes.put(argC, (pred, argInd))
              } else {
                usedArgSet += argInd
                makeConstUsed(argC)
              }
            case _ => {
              usedArgSet += argInd
              for (argC <- SymbolCollector constants arg)
                if (!(seenConsts add argC))
                  makeConstUsed(argC)
            }
          }

        argIndexes.clear
        seenConsts.clear
      }
    }

    { // fixed-point iteration, to transitivitely find all read arguments
      val workList = new LinkedHashSet[Predicate]
      for ((pred, set) <- usedArgs.iterator)
        if (!set.isEmpty)
          workList += pred

      val readConsts = new MHashSet[ConstantTerm]

      while (!workList.isEmpty) {
        val pred = workList.head
        workList -= pred

        val usedHeadArgs = usedArgs(pred)

        for (Clause(IAtom(_, headArgs), body, _) <-
               clausesWithHead.getOrElse(pred, List())) {
          for (ind <- usedHeadArgs)
            readConsts ++= SymbolCollector constants headArgs(ind)

          for (IAtom(bodyPred, bodyArgs) <- body) {
            var changed = false
            val usedBodyArgs = usedArgs(bodyPred)

            for ((IConstant(argC), argInd) <- bodyArgs.iterator.zipWithIndex)
              if (readConsts contains argC)
                if (usedBodyArgs add argInd)
                  changed = true

            if (changed)
              workList += bodyPred
          }

          readConsts.clear
        }
      }
    }

    usedArgs.toMap
  }

  //////////////////////////////////////////////////////////////////////////////

  private def elimArguments(clauses : Clauses,
                            usedArgs : Map[Predicate, MBitSet])
                         : (Clauses,
                            Map[Clause, Clause],
                            Map[Predicate, Predicate]) = {
    val predMapping =
      (for ((pred, set) <- usedArgs.iterator;
            if set.size < pred.arity)
       yield {
         val sorts = HornPredAbs predArgumentSorts pred
         val keptSorts =
           for ((s, n) <- sorts.zipWithIndex; if (set contains n)) yield s
         val newPred = MonoSortedPredicate(pred.name, keptSorts)
         (pred, newPred)
       }).toMap

    def translateAtom(atom : IAtom) : IAtom = {
      val IAtom(pred, args) = atom
      (predMapping get pred) match {
        case Some(newPred) => {
          val set = usedArgs(pred)
          val newArgs =
            (for ((arg, ind) <- args.iterator.zipWithIndex;
                  if set contains ind)
             yield arg).toVector
          IAtom(newPred, newArgs)
        }
        case None =>
          atom
      }
    }

    if (predMapping.isEmpty) {
      (clauses, null, predMapping)
    } else {
      val clauseMapping =
        for (clause@Clause(head, body, constraint) <- clauses) yield {
          val newHead = translateAtom(head)
          var changed = !(newHead eq head)

          val newBody = for (a <- body) yield {
            val newA = translateAtom(a)
            if (!(newA eq a))
              changed = true
            newA
          }

          if (changed)
            (Clause(newHead, newBody, constraint), clause)
          else
            (clause, clause)
        }

       (clauseMapping map (_._1), clauseMapping.toMap, predMapping)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private object ConcreteTerm {
    def unapply(t : ITerm) : Option[ITerm] = t match {
      case t : IIntLit =>
        Some(t)
      case Sort.MultipleValueBool.True | Sort.MultipleValueBool.False =>
        Some(t)
      case IFunApp(f@ADT.Constructor(_, _), args) => {
        val argTerms = args map (unapply(_))
        if (argTerms forall (_.isDefined))
          Some(IFunApp(f, argTerms map (_.get)))
        else
          None
      }
      case _
        => None
    }
  }

}
