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

import ap.parser.IExpression.{Predicate, Sort, and}
import ap.parser._
import ap.theories.Heap
import ap.theories.Heap._
//import lazabs.horn.Heap._
import ap.types.{MonoSortedIFunction, MonoSortedPredicate}
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts

import scala.collection.mutable.{ArrayBuffer, LinkedHashMap, HashMap => MHashMap}


object HeapExpander {

  /**
   * Interface for expanding heap operations with their sizes (num. allocations)
   */
  trait Expansion {

    /**
     * Decide if an ADT sort should be expanded. In this case,
     * the method returns a list of new terms and their sorts
     * to be added as. The new terms can contain the variable <code>_0</code>
     * which has to be substituted with the actual argument.
     */
    def expand(pred : Predicate,
               argNum : Int,
               sort : HeapSort)
             : Option[Seq[(ITerm, Sort, String)]]
  }

}

////////////////////////////////////////////////////////////////////////////////
class HeapModifyExtractor(allocs : ArrayBuffer[IFunApp],
                          writes : ArrayBuffer[IFunApp], theory : Heap)
  extends CollectingVisitor[Int, Unit] {
  def postVisit(t : IExpression, boundVars : Int, subres : Seq[Unit]) : Unit =
    t match {
      case f@IFunApp(theory.alloc, _) => allocs += f
      case f@IFunApp(theory.write, _) => writes += f
      case _ => // nothing
    }
}
////////////////////////////////////////////////////////////////////////////////
/**
 * Class used to expand ADT predicate arguments into multiple arguments;
 * for instance, to explicitly keep track of the size of ADT arguments.
 */
class HeapExpander(val name : String,
                  expansion : HeapExpander.Expansion) extends HornPreprocessor {
  import HornPreprocessor._

  override def isApplicable(clauses : Clauses) : Boolean =
    (HornClauses allPredicates clauses) exists {
      p => predArgumentSorts(p) exists (_.isInstanceOf[HeapSort])
    }

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val predicates =
      HornClauses allPredicates clauses
    val newPreds =
      new MHashMap[Predicate,
                   (Predicate,                         // new predicate
                    Seq[Option[Seq[(ITerm, Sort, String)]]], // additional arguments
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
      val addedArgs  = new ArrayBuffer[Option[Seq[(ITerm, Sort, String)]]]
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

        //println(clauses)

        sort match {
          case sort : HeapSort =>
            for (newArguments <-
                   expansion.expand(pred, argNum,
                                    sort.asInstanceOf[HeapSort])) {
              val (addArgs, addSorts, _) = newArguments.unzip3
              newSorts ++= addSorts
              addedArgs(addedArgs.size - 1) = Some(newArguments)
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
              val newArgs = new ArrayBuffer[ITerm]

              for ((t, maybeArgs) <- a.args.iterator zip addedArgs.iterator){
                newArgs += t
                for (newArgSpecs <- maybeArgs) {
                  val subst = (List(t), 1)
                  for ((s, sort, name) <- newArgSpecs) {
                    val instArg =
                      VariableSubstVisitor(s, subst)
                    newArgs +=
                      newTerms.getOrElseUpdate(instArg, newConst(name, sort))
                  }

                  //additionalConstraints += constraint
                }
              }

              IAtom(newPred, newArgs)
            }
            case None =>
              a
          }

        val newHead = rewriteAtom(head)
        val newBody = for (a <- body) yield rewriteAtom(a)

        /*todo: refactor to get rid of below stupid part*/
        import scala.collection.mutable.{HashSet => MHashSet}
        val theory : Heap = newTerms.head._1.asInstanceOf[IFunApp].fun.
          asInstanceOf[MonoSortedIFunction].argSorts.head.asInstanceOf[HeapSort].heapTheory

        def collectHeapModifications(theory : Heap, t : IExpression) :
        (ArrayBuffer[IFunApp], ArrayBuffer[IFunApp]) = {
          val allocs = new ArrayBuffer[IFunApp]
          val writes = new ArrayBuffer[IFunApp]
          val c = new HeapModifyExtractor(allocs, writes, theory)
          c.visitWithoutResult (t, 0)
          (allocs, writes)
        }

        val (allocs, writes) = collectHeapModifications(theory, constraint)
        import IExpression._
        val constraintsFromAllocs : IFormula =
          (for (alloc <- allocs) yield {
            val h = alloc.args(0)
            val o = alloc.args(1)
            theory.counter(theory.allocHeap(h, o)) === theory.counter(h) + 1
          }).fold(i(true))((f1, f2) => Conj(f1, f2))
        val constraintsFromWrites : IFormula =
          (for (write <- writes) yield {
            val h = write.args(0)
            val p = write.args(1)
            val o = write.args(2)
            theory.counter(h) === theory.counter(theory.write(h, p, o))
          }).fold(i(true))((f1, f2) => Conj(f1, f2))

        val sizeChangeConstraint = constraintsFromAllocs &&& constraintsFromWrites
        //println("sizeChangeConstraint: " + sizeChangeConstraint)

        val newConstraint =
          ConstraintSimplifier.rewriteConstraint(constraint, newTerms) &&&
          and(additionalConstraints) &&&
          and(for ((t, c) <- newTerms.iterator) yield (t === c)) &&&
          sizeChangeConstraint

        val newClause = Clause(newHead, newBody, newConstraint)
        clauseBackMapping.put(newClause, clause)

        //println("old clause: " + clause)
        //println("new clause: " + newClause)

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

object HeapSizeArgumentExtender {

  import HeapExpander._

  /**
   * Preprocessor that adds explicit size arguments for each predicate
   * argument for a recursive ADT
   */
  class SizeArgumentAdder extends Expansion {
    import IExpression._

    def expand(pred : Predicate,
               argNum : Int,
               sort : HeapSort)
             : Option[Seq[(ITerm, Sort, String)]] = {
      val sizefun = sort.heapTheory.counter
      Some(List((sizefun(v(0)), Sort.Nat, "heap_size")))
    }
  }
}

/**
 * Preprocessor that adds explicit size arguments for each predicate
 * argument for a recursive ADT
 */
class HeapSizeArgumentExtender
      extends HeapExpander("adding heap size arguments",
                          new HeapSizeArgumentExtender.SizeArgumentAdder) {

}
