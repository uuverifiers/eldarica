/**
 * Copyright (c) 2019-2021 Philipp Ruemmer. All rights reserved.
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
import ap.types.MonoSortedPredicate

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer,
                                 LinkedHashMap}


/**
 * Class used to expand predicate arguments into multiple arguments;
 * for instance, to explicitly keep track of the size of ADT arguments.
 */
abstract class ArgumentExpander extends HornPreprocessor {
  import HornPreprocessor._

  val name : String

  /**
   * Determine whether arguments of the given sort might be expanded.
   */
  def isExpandableSort(s : Sort) : Boolean

  /**
   * Set up the preprocessor for the given set of clauses.
   */
  def setup(clauses : Clauses) : Unit = {}

  override def isApplicable(clauses : Clauses) : Boolean =
    (HornClauses allPredicates clauses) exists {
      p => predArgumentSorts(p) exists isExpandableSort
    }

  /**
   * Decide whether to expand a predicate argument. In this case, the
   * method returns a list of new terms and their sorts to be added
   * as. The new terms can contain the variable <code>_0</code> which
   * has to be substituted with the actual argument. The last optional
   * describes how to recompute the original term from the newly
   * introduced terms; the last term can contain variables <code>_0,
   * _1, ...</code> for this purpose.
   */
  def expand(pred : Predicate, argNum : Int, sort : Sort)
           : Option[(Seq[(ITerm, Sort, String)], Option[ITerm])]

  /**
   * Optionally, apply a postprocessor to solution formulas.
   */
  def postprocessSolution(p : Predicate, f : IFormula) : IFormula = f

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    setup(clauses)

    val predicates =
      HornClauses allPredicates clauses
    val newPreds =
      new MHashMap[Predicate,
                   (Predicate,                         // new predicate
                    Seq[Option[(Seq[(ITerm, Sort, String)],
                                Option[ITerm])]],      // additional arguments
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
      val addedArgs  = new ArrayBuffer[Option[(Seq[(ITerm, Sort, String)],
                                               Option[ITerm])]]
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

        if (isExpandableSort(sort))
          for ((newArguments, oldArgReconstr) <- expand(pred, argNum, sort)) {
            val (addArgs, addSorts, _) = newArguments.unzip3

            for (reconstr <- oldArgReconstr) {
              // in that case we can remove the old argument
              solSubst.reduceToSize(solSubst.size - 1)
              newSorts.reduceToSize(newSorts.size - 1)
              argMapping -= argNum
              cexArgs(cexArgs.size - 1) =
                IExpression.shiftVars(reconstr, newSorts.size)
            }

            newSorts ++= addSorts
            addedArgs(addedArgs.size - 1) = Some((newArguments, oldArgReconstr))

            val subst = (List(IVariable(argNum)), 1)
            for (t <- addArgs)
              solSubst += VariableSubstVisitor(t, subst)

            changed = true
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
              val newArgs = new ArrayBuffer[ITerm]

              for ((t, maybeArgs) <- a.args.iterator zip addedArgs.iterator){
                newArgs += t
                for ((newArgSpecs, oldArgReconstr) <- maybeArgs) {
                  if (oldArgReconstr.isDefined)
                    newArgs.reduceToSize(newArgs.size - 1)

                  val subst = (List(t), 1)
                  for ((s, sort, name) <- newArgSpecs) {
                    val instArg =
                      VariableSubstVisitor(s, subst)
                    newArgs +=
                      newTerms.getOrElseUpdate(instArg, newConst(name, sort))
                  }

                  for (reconstr <- oldArgReconstr) {
                    val arity = newArgSpecs.size
                    val args  = (newArgs takeRight arity).toList
                    val rec   = VariableSubstVisitor(reconstr, (args, arity))
                    additionalConstraints += (rec === t)
                  }
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
            case Some((pred, subst, _)) => {
              val newSol = VariableSubstVisitor(sol, (subst, 1))
              (pred, postprocessSolution(pred, newSol))
            }
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
