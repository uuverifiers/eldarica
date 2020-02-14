/**
 * Copyright (c) 2019-2020 Philipp Ruemmer. All rights reserved.
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

import lazabs.horn.bottomup.HornClauses
import HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.abstractions.VerificationHints

import ap.parser._
import IExpression.{Predicate, Sort, and}
import ap.theories.ADT
import ap.types.MonoSortedPredicate

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer,
                                 LinkedHashMap}


object ADTExpander {

  /**
   * Interface for adding auxiliary predicate arguments for ADT types
   */
  trait Expansion {

    /**
     * Decide whether to expand an ADT sort should be expanded. In
     * this case, the method returns a list of new terms and their sorts
     * to be added as. The new terms can contain the variable <code>_0</code>
     * which has to be substituted with the actual argument.
     */
    def expand(pred : Predicate,
               argNum : Int,
               sort : ADT.ADTProxySort)
             : Option[Seq[(ITerm, Sort, String)]]
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class used to expand ADT predicate arguments into multiple arguments;
 * for instance, to explicitly keep track of the size of ADT arguments.
 */
class ADTExpander(val name : String,
                  expansion : ADTExpander.Expansion) extends HornPreprocessor {
  import HornPreprocessor._
  import ADTExpander._

  override def isApplicable(clauses : Clauses) : Boolean =
    (HornClauses allPredicates clauses) exists {
      p => predArgumentSorts(p) exists (_.isInstanceOf[ADT.ADTProxySort])
    }

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val predicates =
      HornClauses allPredicates clauses
    val newPreds =
      new MHashMap[Predicate,
                   (Predicate,                         // new predicate
                    Seq[Option[Seq[(ITerm, String)]]], // additional arguments
                    Map[Int, Int])]                    // argument mapping,
                                                       //   needed for
                                                       //   VerifHintElement
                                                       //      .shiftArguments

    val predBackMapping =
      new MHashMap[Predicate,
                   (Predicate,                         // old predicate
                    List[ITerm],                       // solution substitution
                    Seq[ITerm])]                       // argument list for
                                                       //   counterexamples

    //
    // First search for predicates with arguments that should be expanded
    //

    for (pred <- predicates) {
      val oldSorts   = predArgumentSorts(pred)
      val newSorts   = new ArrayBuffer[Sort]
      val addedArgs  = new ArrayBuffer[Option[Seq[(ITerm, String)]]]
      val argMapping = new MHashMap[Int, Int]
      val solSubst   = new ArrayBuffer[ITerm]
      val cexArgs    = new ArrayBuffer[ITerm]
      var changed    = false

      for ((sort, argNum) <- oldSorts.iterator.zipWithIndex) {
        argMapping.put(argNum, newSorts.size - argNum)
        solSubst  += IVariable(argNum)
        cexArgs   += IVariable(newSorts.size)
        newSorts  += sort
        addedArgs += None

        sort match {
          case sort : ADT.ADTProxySort =>
            for (newArguments <-
                   expansion.expand(pred, argNum,
                                    sort.asInstanceOf[ADT.ADTProxySort])) {
              val (addArgs, addSorts, addNames) = newArguments.unzip3
              newSorts ++= addSorts
              addedArgs(addedArgs.size - 1) = Some(addArgs zip addNames)
              val subst = (List(solSubst.last), 1)
              for (t <- addArgs)
                solSubst += VariableSubstVisitor(t, subst)
              changed = true
            }
          case _ => // nothing
        }
      }

      if (changed) {
        val newPred = MonoSortedPredicate(pred.name + "_exp", newSorts)
        newPreds       .put(pred,    (newPred, addedArgs, argMapping.toMap))
        predBackMapping.put(newPred, (pred, solSubst.toList, cexArgs))
      }
    }

    if (newPreds.isEmpty)
      return (clauses, hints, HornPreprocessor.IDENTITY_TRANSLATOR)

    //
    // Then rewrite clauses and replace predicates
    //

    val clauseBackMapping = new MHashMap[Clause, Clause]
    var symCounter = 0
    def newConst(prefix : String, s : Sort) : IConstant = {
      symCounter = symCounter + 1
      IConstant(s newConstant (prefix + "_" + (symCounter - 1)))
    }

    val newClauses = for (clause <- clauses) yield {

      if (clause.predicates exists (newPreds contains _)) {

        val Clause(head, body, constraint) = clause

        val additionalConstraints = new ArrayBuffer[IFormula]
        val newTerms = new LinkedHashMap[ITerm, IConstant]

        def rewriteAtom(a : IAtom) : IAtom =
          (newPreds get a.pred) match {
            case Some((newPred, addedArgs, _)) => {
              val sorts = predArgumentSorts(newPred)
              val newArgs = new ArrayBuffer[ITerm]

              for (((t, maybeArgs), sort) <-
                     a.args.iterator zip addedArgs.iterator zip sorts.iterator){
                newArgs += t
                for (newArgSpecs <- maybeArgs) {
                  val subst = (List(t), 1)
                  for ((s, name) <- newArgSpecs) {
                    val instArg =
                      VariableSubstVisitor(s, subst)
                    newArgs +=
                      newTerms.getOrElseUpdate(instArg, newConst(name, sort))
                  }

//                  if (!constraint.isTrue)
//                    additionalConstraints += constraint
                }
              }

              IAtom(newPred, newArgs)
            }
            case None =>
              a
          }

        val newHead = rewriteAtom(head)
        val newBody = for (a <- body) yield rewriteAtom(a)

        val newConstraint =
          ConstraintSimplifier.rewriteConstraint(constraint, newTerms) &&&
          and(additionalConstraints) &&&
          and(for ((t, c) <- newTerms.iterator) yield (t === c))

        val newClause = Clause(newHead, newBody, newConstraint)
        clauseBackMapping.put(newClause, clause)

        newClause

      } else {
        clause
      }
    }

    //
    // Hints need to be adapted
    //

    val newPredicateHints =
      (for ((pred, hintList) <- hints.predicateHints.iterator) yield {
        (newPreds get pred) match {
          case Some((newPred, _, mapping)) => {
            val newList = for (hint <- hintList;
                               newHint <- hint.shiftArguments(mapping))
                          yield newHint
            (newPred, newList)
          }
          case None =>
            (pred, hintList)
        }
       }).toMap

    val newHints = VerificationHints(newPredicateHints)

    //
    // Back-translator for solutions
    //

    val translator = new BackTranslator {
      def translate(solution : Solution) =
        (for ((newPred, sol) <- solution.iterator) yield
          (predBackMapping get newPred) match {
            case Some((pred, subst, _)) =>
              (pred, VariableSubstVisitor(sol, (subst, 1)))
            case None =>
              (newPred, sol)
          }).toMap

      def translate(cex : CounterExample) =
        for (p <- cex) yield {
          val (a@IAtom(pred, args), clause) = p
          (clauseBackMapping get clause) match {
            case Some(newClause) =>
              (predBackMapping get pred) match {
                case Some((newPred, _, oldArgsTemplates)) => {
                  val subst   = (args.toList, 0)
                  val oldArgs = for (p <- oldArgsTemplates)
                                yield VariableSubstVisitor(p, subst)
                  (IAtom(newPred, oldArgs), newClause)
                }
                case None =>
                  (a, newClause)
              }
            case None =>
              p
          }
        }
    }

    (newClauses, newHints, translator)
  }
}

////////////////////////////////////////////////////////////////////////////////

object SizeArgumentExtender {

  import ADTExpander._

  /**
   * Preprocessor that adds explicit size arguments for each predicate
   * argument for a recursive ADT
   */
  class SizeArgumentAdder extends Expansion {

    import IExpression._

    def expand(pred : Predicate,
               argNum : Int,
               sort : ADT.ADTProxySort)
             : Option[Seq[(ITerm, Sort, String)]] =
      if (sort.adtTheory.termSize != null &&
          recursiveADTSorts.getOrElseUpdate(sort, isRecursive(sort))) {
        val sizefun = sort.adtTheory.termSize(sort.sortNum)
        Some(List((sizefun(v(0)), Sort.Nat, "adt_size")))
      } else {
        None
      }

    private val recursiveADTSorts = new MHashMap[ADT.ADTProxySort, Boolean]

    private def isRecursive(sort : ADT.ADTProxySort) : Boolean =
      isRecursive(sort.sortNum, List(), sort.adtTheory)

    private def isRecursive(sortNum : Int,
                            seenSorts : List[Int],
                            adt : ADT)  : Boolean =
      if (seenSorts contains sortNum) {
        true
      } else {
        val newSeen = sortNum :: seenSorts
        (for (ctor <- adt.constructors.iterator;
              sort <- ctor.argSorts.iterator)
         yield sort) exists {
           case sort : ADT.ADTProxySort if sort.adtTheory == adt =>
             isRecursive(sort.sortNum, newSeen, adt)
           case _ =>
             false
         }
      }
  }
}

/**
 * Preprocessor that adds explicit size arguments for each predicate
 * argument for a recursive ADT
 */
class SizeArgumentExtender
      extends ADTExpander("adding size arguments",
                          new SizeArgumentExtender.SizeArgumentAdder) {

}
