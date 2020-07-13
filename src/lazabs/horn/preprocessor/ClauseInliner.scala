/**
 * Copyright (c) 2011-2020 Philipp Ruemmer. All rights reserved.
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
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import HornClauses._
import lazabs.horn.bottomup.Util.{Dag, DagNode, DagEmpty}

import ap.basetypes.IdealInt
import ap.parser._
import IExpression._
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

/**
 * Inline linear definitions.
 */
class ClauseInliner extends HornPreprocessor {
  import HornPreprocessor._

  val name : String = "clause inlining"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val (newClauses, newHints) = elimLinearDefs(clauses, hints)

    val translator = new BackTranslator {
      private val inlinedClauses = originalInlinedClauses.toMap
      private val backMapping = clauseBackMapping.toMap

      //////////////////////////////////////////////////////////////////////////

      // TODO: this should really use interpolation, not QE to compute
      // solutions

      def translate(solution : Solution) = {
        // augment solution to also satisfy inlined clauses
        var remaining =
          (for ((p, c) <- inlinedClauses.iterator;
                if !(solution contains p))
           yield c).toList

        if (remaining.isEmpty) {
          solution
        } else SimpleAPI.withProver { p =>
          import p._

          assert(!(remaining contains HornClauses.FALSE))

          var curSolution = solution

          while (!remaining.isEmpty) {
            val oldSize = remaining.size

            remaining = for (c <- remaining; if {
              if (c.body forall {
                    case IAtom(p, _) => curSolution contains p
                  }) scope {
                  
                // compute the value of the head symbol through quantifier elimination
                val Clause(head, body, constraint) = c
                val headVars = for (s <- predArgumentSorts(head.pred))
                               yield createConstant("X", s)
                addConstants(c.constants.toSeq.sortWith(_.name < _.name))
                
                val completeConstraint =
                  constraint &
                  and(for (IAtom(pred, args) <- body)
                      yield subst(curSolution(pred), args.toList, 0)) &
                  (head.args === headVars)

                val simpSol = (new Simplifier)(projectEx(completeConstraint, headVars))
                val simpSolVar =
                  ConstantSubstVisitor(simpSol,
                                       (for ((IConstant(c), n) <-
                                          headVars.iterator.zipWithIndex)
                                        yield (c -> v(n))).toMap)
                curSolution = curSolution + (c.head.pred -> simpSolVar)
                
                false
              } else {
                true
              }
            }) yield c

            // if there was no progress, select some undefined
            // predicate that occurs in the body of a clause and set it to false
            if (remaining.size == oldSize) {
              val headPreds =
                (for (Clause(IAtom(p, _), _, _) <- remaining.iterator) yield p).toSet
              val danglingPreds =
                for (Clause(_, body, _) <- remaining.iterator;
                     IAtom(p, _) <- body.iterator;
                     if !(headPreds contains p) && !(curSolution contains p))
                yield p
              curSolution = curSolution + (danglingPreds.next -> i(false))
            }
          }

          curSolution
        }
      }

      //////////////////////////////////////////////////////////////////////////

      def translate(cex : CounterExample) =
        simplify((cex substitute buildSubst(cex)).elimUnconnectedNodes)

      private def buildSubst(cex : CounterExample) : Map[Int, CounterExample] =
        SimpleAPI.withProver { p =>
          implicit val _ = p
          
          (for ((subCEX@DagNode((a, clause), children, _), i) <-
                  cex.subdagIterator.zipWithIndex;
                replDag = backMapping get clause;
                if replDag.isDefined)
           yield {
             val bodyAtoms = for (c <- children) yield subCEX(c)._1
             i -> transformCEXFragment(a, bodyAtoms, replDag.get)
           }).toMap
        }

      private def transformCEXFragment(rootAtom : IAtom,
                                       bodyAtoms : Seq[IAtom],
                                       dag : Dag[Option[Clause]])
                                      (implicit p : SimpleAPI)
                                      : CounterExample = p.scope {
        import p._

        // discover leafs in the dag
        val leafIndexes =
          (for ((None, i) <- dag.iterator.zipWithIndex) yield i).toList
        val leafNum =
          leafIndexes.iterator.zipWithIndex.toMap
        val dagSize = dag.size

        // introduce variables for intermediate states
        val varDag = for (p <- dag.zipWithIndex) yield p match {
          case (Some(clause), _) =>
            IAtom(clause.head.pred,
                  for (s <- predArgumentSorts(clause.head.pred))
                    yield createConstant("X", s))
          case (None, num) =>
            bodyAtoms(leafNum(num))
        }

        // add constraints to find intermediate states
        for (subdag@DagNode((Some(clause), rootVars), children, _) <-
               (dag zip varDag).subdagIterator) {
          val bodyVars = for (c <- children) yield subdag(c)._2
          val (Clause(head, body, constraint), newConsts) = clause.refresh

          addConstants(newConsts)

          !! (constraint)
          !! (rootVars.args === head.args)
          for ((atom, vars) <- body.iterator zip bodyVars.iterator)
            !! (atom.args === vars.args)
        }

        !! (varDag.head.args === rootAtom.args)

        val pRes = ???
        assert(pRes == ProverStatus.Sat)

        val interStates = for (symState <- varDag) yield {
          val IAtom(p, vars) = symState
          IAtom(p, for (v <- vars) yield evalToTerm(v))
        }

        def translate(depth : Int, dag : Dag[(IAtom, Option[Clause])]) : CounterExample =
          dag match {
            case DagNode((_, None), _, next) =>
              DagNode(null, List(), translate(depth + 1, next))
            case DagNode((state, Some(clause)), children, next) => {
              val newChildren = for (c <- children; n = c + depth) yield
                (leafNum get n) match {
                  case Some(leaf) => dagSize - depth + leaf
                  case None => c
                }
              DagNode((state, clause), newChildren, translate(depth + 1, next))
            }
            case DagEmpty =>
              DagEmpty
          }

        translate(0, interStates zip dag)
      }
    }

    originalInlinedClauses.clear
    clauseBackMapping.clear

    (newClauses, newHints, translator)
  }

  //////////////////////////////////////////////////////////////////////////////

  // all clauses that were inlined and thus eliminated
  private val originalInlinedClauses = new MHashMap[Predicate, Clause]

  // mapping from the newly produced clauses to trees of the orginal clauses
  private val clauseBackMapping = new MHashMap[Clause, Dag[Option[Clause]]]

  private def defaultBackMapping(c : Clause) = {
    val N = c.body.size
    DagNode(Some(c), (1 to N).toList,
            (DagEmpty.asInstanceOf[Dag[Option[Clause]]] /: (0 until N)) {
              case (d, _) => DagNode(None, List(), d) })
  }

  private def elimLinearDefs(allClauses : Seq[HornClauses.Clause],
                             hints : VerificationHints)
                  : (Seq[HornClauses.Clause], VerificationHints) = {
    var changed = true
    var clauses = allClauses
    var removedPreds : Set[Predicate] = Set()

    while (changed) {
      changed = false

      // determine relation symbols that are uniquely defined

      val uniqueDefs =
        extractUniqueDefs(clauses)
      val finalDefs =
        extractAcyclicDefs(allClauses, uniqueDefs)

      val newClauses =
        for (clause@Clause(IAtom(p, _), _, _) <- clauses;
             if (!(finalDefs contains p)))
        yield applyDefs(clause, finalDefs)

      if (newClauses.size < clauses.size) {
        clauses = newClauses
        changed = true
      }

      removedPreds = removedPreds ++ finalDefs.keys
    }

    (clauses, hints filterNotPredicates removedPreds)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def extractUniqueDefs(clauses : Iterable[Clause]) = {
    val uniqueDefs = new MHashMap[Predicate, Clause]
    val badHeads = new MHashSet[Predicate]
    badHeads += FALSE

    for (clause@Clause(head, body, _) <- clauses)
      if (!(badHeads contains head.pred)) {
        if ((uniqueDefs contains head.pred) ||
            body.size > 1 ||
            (body.size == 1 && head.pred == body.head.pred)) {
          badHeads += head.pred
          uniqueDefs -= head.pred
        } else {
          uniqueDefs.put(head.pred, clause)
        }
      }

    uniqueDefs.toMap
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Extract an acyclic subset of the definitions, and
   * shorten definition paths
   */
  private def extractAcyclicDefs(clauses : Clauses,
                                 uniqueDefs : Map[Predicate, Clause]) = {
    var remDefs = new MHashMap[Predicate, Clause] ++ uniqueDefs
    val finalDefs = new MHashMap[Predicate, Clause]

    while (!remDefs.isEmpty) {
      val bodyPreds =
        (for (Clause(_, body, _) <- remDefs.valuesIterator;
              IAtom(p, _) <- body.iterator)
         yield p).toSet
      val (remainingDefs, defsToInline) =
        remDefs partition { case (p, _) => bodyPreds contains p }

      if (defsToInline.isEmpty) {
        // we have to drop some definitions to eliminate cycles
        val pred =
          (for (Clause(IAtom(p, _), _, _) <- clauses.iterator;
                if ((remDefs contains p) && (bodyPreds contains p)))
           yield p).next

        remDefs retain {
          case (_, Clause(_, Seq(), _)) => true
          case (_, Clause(_, Seq(IAtom(p, _)), _)) => p != pred
        }
      } else {
        remDefs = remainingDefs

        finalDefs transform {
          case (_, clause) => applyDefs(clause, defsToInline)
        }

        finalDefs ++= defsToInline
        originalInlinedClauses ++= defsToInline
      }
    }

    finalDefs.toMap
  }

  //////////////////////////////////////////////////////////////////////////////

  def applyDefs(clause : Clause,
                defs : scala.collection.Map[Predicate, Clause]) : Clause = {
    val Clause(head, body, constraint) = clause
    assert(!(defs contains head.pred))

    var changed = false

    val (newBody, newConstraints, inlinedClauses) =
      (for (bodyLit@IAtom(p, args) <- body) yield {
        (defs get p) match {
          case None =>
            (List(bodyLit), i(true), DagNode(None, List(), DagEmpty))
          case Some(defClause) => {
            changed = true
            val (lit, constr) = defClause inline args
            val inlinedClauses = (clauseBackMapping get defClause) match {
              case Some(dag) => dag
              case None => defaultBackMapping(defClause)
            }
            (lit, constr, inlinedClauses)
          }
       }
      }).unzip3

    if (changed) {
      val res = Clause(head, newBody.flatten, constraint &&& and(newConstraints))

      val oldMapping = (clauseBackMapping get clause) match {
        case Some(dag) => dag
        case None => defaultBackMapping(clause)
      }

      val leafIndexes =
        (for ((None, i) <- oldMapping.iterator.zipWithIndex) yield i).toList

      assert(leafIndexes.size == inlinedClauses.size)

      val newMapping =
        oldMapping.substitute(
          (leafIndexes.iterator zip inlinedClauses.iterator).toMap)

      clauseBackMapping.put(res, newMapping)
      res
    } else {
      clause
    }
  }

}
