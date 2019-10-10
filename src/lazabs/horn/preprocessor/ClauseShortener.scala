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

package lazabs.horn.preprocessor

import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.bottomup.Util.{Dag, DagNode, DagEmpty}

import ap.basetypes.{IdealInt, Leaf, Tree}
import ap.parser._
import IExpression._
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashSet, ArrayBuffer}

object ClauseShortener {
  import HornPreprocessor._

  object BTranslator {
  
    def apply(tempPreds : Set[Predicate],
              backMapping : Map[Clause, Clause]) : BTranslator = {
      val extendedMapping =
        for ((newClause, oldClause) <- backMapping) yield {
          assert(newClause.body.size == oldClause.body.size)
          val indexTree =
            Tree(-1,
                 (for (n <- 0 until newClause.body.size) yield Leaf(n)).toList)
          (newClause, (oldClause, indexTree))
        }
      new BTranslator(tempPreds, extendedMapping)
    }

    def withIndexes(tempPreds : Set[Predicate],
                    backMapping : Map[Clause, (Clause, Tree[Int])])
                  : BTranslator =
      new BTranslator(tempPreds, backMapping)

  }

  class BTranslator private (tempPreds : Set[Predicate],
                             backMapping : Map[Clause, (Clause, Tree[Int])])
        extends BackTranslator {

    def translate(solution : Solution) =
      solution -- tempPreds

    def translate(cex : CounterExample) =
      if (tempPreds.isEmpty && backMapping.isEmpty)
        cex
      else {
        val res = simplify(translateCEX(cex).elimUnconnectedNodes)

        assert(res.subdagIterator forall {
          case dag@DagNode((state, clause@Clause(head, body, constraint)),
                           children, _) =>
            // syntactic check: do clauses fit together?
            state.pred == head.pred &&
            children.size == body.size &&
            ((children.iterator zip body.iterator) forall {
               case (c, IAtom(pred, _)) =>
                 c > 0 && dag(c)._1.pred == pred })
          })

        res
      }

    private def translateCEX(dag : CounterExample) : CounterExample =
      dag match {
        case DagNode(p@(a, clause), children, next) => {
          val newNext = translateCEX(next)
          (backMapping get clause) match {
            case Some((oldClause, indexTree)) => {
              val newChildrenAr =
                new Array[Int](oldClause.body.size)
              for ((c, t) <- children.iterator zip indexTree.children.iterator)
                allProperChildren(dag drop c, t, newChildrenAr, c)
              DagNode((a, oldClause), newChildrenAr.toList, newNext)
            }
            case None =>
              DagNode(p, children, newNext)
          }
        }
        case DagEmpty =>
          DagEmpty
      }

    private def allProperChildren(dag : CounterExample,
                                  indexTree : Tree[Int],
                                  newChildrenAr : Array[Int],
                                  offset : Int) : Unit = {
      val DagNode((IAtom(p, _), _), children, _) = dag
      if (tempPreds contains p)
        for ((c, t) <- children.iterator zip indexTree.children.iterator)
          allProperChildren(dag drop c, t, newChildrenAr, offset + c)
      else
        newChildrenAr(indexTree.d) = offset
    }
  }
}

/**
 * Split clauses with large bodies into multiple clauses.
 */
class ClauseShortener extends HornPreprocessor {
  import HornPreprocessor._
  import ClauseShortener._

  private val maxClauseBodySize = 3
  private val tempPredicates = new MHashSet[Predicate]
  private val clauseBackMapping = new MHashMap[Clause, (Clause, Tree[Int])]

  val name : String = "shortening of clauses"

  def process(clauses : Clauses, hints : VerificationHints)
             : (Clauses, VerificationHints, BackTranslator) = {
    val (newClauses, newHints) =
      splitClauseBodies3(clauses, hints)

    val translator = BTranslator.withIndexes(tempPredicates.toSet,
                                             clauseBackMapping.toMap)

    tempPredicates.clear
    clauseBackMapping.clear

    (newClauses, newHints, translator)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def splitClauseBody(clause : Clause,
                              initialPreds : Map[Predicate, Seq[IFormula]])
                             : (List[Clause], Map[Predicate, Seq[IFormula]]) = {
    val Clause(head, body, constraint) = clause

    if (body.size > 2) {
      val body1 = body take 2
      val remainingBody = body drop 2

      val body1Syms =
        (for (a <- body1;
              c <- SymbolCollector constantsSorted a) yield c).distinct
      val body1SymsSet = body1Syms.toSet

      val (constraintList1, constraintList2) =
        LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And) partition {
          f => (SymbolCollector constants f) subsetOf body1SymsSet
        }

      val constraint1 = and(constraintList1)
      val constraint2 = and(constraintList2)

      val otherSyms =
        SymbolCollector constants (constraint2 & and(remainingBody) & head)

      val commonSyms = (body1Syms filter otherSyms) match {
        case Seq() =>
          // make sure that there is at least one argument, otherwise
          // later assumptions in the model checker will be violated
          List(body1Syms.head)
        case syms => syms
      }
      val tempPred = new Predicate ("temp" + tempPredicates.size, commonSyms.size)
      tempPredicates += tempPred

      val head1 = IAtom(tempPred, commonSyms)

      val newClause =
        Clause(head1, body1, constraint1)
      val (nextClause :: otherClauses, newInitialPreds) =
        splitClauseBody(Clause(head, head1 :: remainingBody, constraint2),
                        initialPreds)

      val Clause(nextHead, Seq(_, nextBodyLit), nextConstraint) = nextClause

      val newInitialPreds2 =
      (newInitialPreds get nextHead.pred) match {
        case Some(preds) if (!preds.isEmpty) => SimpleAPI.withProver { p =>
          import p._

          setMostGeneralConstraints(true)
          addConstantsRaw(nextClause.constants.toSeq.sortBy(_.name))
          makeExistentialRaw(SymbolCollector constants head1)

          !! (nextConstraint)

          val headInitialPreds = new LinkedHashSet[IFormula]
          val backSubst = (for ((t, n) <- commonSyms.iterator.zipWithIndex)
                           yield (t -> v(n))).toMap

          //////////////////////////////////////////////////////////////////////

          def getInitialPred : IFormula = ??? match {
            case ProverStatus.Valid => getConstraint match {
              case f@IBoolLit(true) => f
              case f => ConstantSubstVisitor(f, backSubst)
            }
            case ProverStatus.Invalid =>
              IBoolLit(false)
          }

          //////////////////////////////////////////////////////////////////////

          def testByPreds(remainingPreds : List[(IFormula, Set[ConstantTerm])],
                          uneligiblePreds : List[(IFormula, Set[ConstantTerm])],
                          relevantSyms : Set[ConstantTerm],
                          lastRelevantSymsSize : Int) : Unit =
            remainingPreds match {
              case (byPred, byPredSyms) :: otherByPreds =>
                if (Seqs.disjointSeq(relevantSyms, byPredSyms)) {
                  testByPreds(otherByPreds,
                              (byPred, byPredSyms) :: uneligiblePreds,
                              relevantSyms,
                              lastRelevantSymsSize)
                } else {
                  testByPreds(otherByPreds,
                              uneligiblePreds,
                              relevantSyms,
                              lastRelevantSymsSize)
                  scope {
                    !! (byPred)
                    getInitialPred match {
                      case IBoolLit(true) =>
                        // useless predicate, and no need to search further
                      case f => {
                        headInitialPreds += f
                        testByPreds(otherByPreds,
                                    uneligiblePreds,
                                    relevantSyms ++ byPredSyms,
                                    lastRelevantSymsSize)
                      }
                    }
                  }
                }
              case List() =>
                if (!uneligiblePreds.isEmpty &&
                    relevantSyms.size > lastRelevantSymsSize)
                  testByPreds(uneligiblePreds, List(),
                              relevantSyms, relevantSyms.size)
            }

          val allByPreds =
            for (f <- newInitialPreds.getOrElse(nextBodyLit.pred, List()).toList)
            yield {
              val instF = VariableSubstVisitor(f, (nextBodyLit.args.toList, 0))
              (instF, (SymbolCollector constants instF).toSet)
            }

          //////////////////////////////////////////////////////////////////////

          for (pred <- preds) scope {
            val instPred = VariableSubstVisitor(pred, (nextHead.args.toList, 0))
            ?? (instPred)

            val syms = (SymbolCollector constants (nextConstraint & instPred)).toSet
            testByPreds(allByPreds, List(), syms, syms.size)
          }

          headInitialPreds -= IBoolLit(false)

          newInitialPreds + (tempPred -> headInitialPreds.toSeq)
        }
        case _ => newInitialPreds
      }

      (newClause :: nextClause :: otherClauses, newInitialPreds2)
    } else {
      (List(clause), initialPreds)
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Alternative implementation, creating wider but less deep trees

  private def splitClauseBody2(clause : Clause,
                               initialPredicates : Map[IExpression.Predicate,
                                                       Seq[IFormula]])
                               : List[Clause] =
    if (clause.body.size <= maxClauseBodySize ||
        ((initialPredicates get clause.head.pred) match {
          case Some(s) => !s.isEmpty
          case None => false
        }))
      List(clause)
    else
      splitClauseBody2(clause.head, clause.body,
                       LineariseVisitor(Transform2NNF(clause.constraint),
                                        IBinJunctor.And))

  private def splitClauseBody2(head : IAtom,
                               body : List[IAtom],
                               constraint : Seq[IFormula]) : List[Clause] =
    if (body.size <= maxClauseBodySize) {
      List(Clause(head, body, and(constraint)))
    } else {
      val halfSize = (body.size + 1) / 2
      val bodyHalf1 = body take halfSize
      val bodyHalf2 = body drop halfSize

      def findRelevantConstraints(terms : Seq[ITerm]) : Seq[IFormula] = {
        val syms = new MHashSet[ConstantTerm]
        for (t <- terms)
          syms ++= SymbolCollector constants t

/*        val selConstraints = new LinkedHashSet[IFormula]
        var selConstraintsSize = -1
        while (selConstraints.size > selConstraintsSize) {
          selConstraintsSize = selConstraints.size
          for (f <- constraint)
            if (!(selConstraints contains f) &&
                ContainsSymbol(f, (x:IExpression) => x match {
                  case IConstant(c) => syms contains c
                  case _ => false
                })) {
              selConstraints += f
              syms ++= SymbolCollector constants f
            }
        } */

        constraint filter { f => (SymbolCollector constants f) subsetOf syms }

//        selConstraints.toSeq
      }

      val args1 = (for (IAtom(_, a) <- bodyHalf1; t <- a) yield t).distinct
      val half1Constraints = findRelevantConstraints(args1)

      val half1Pred = new Predicate ("temp" + tempPredicates.size, args1.size)
      tempPredicates += half1Pred

      val head1 = IAtom(half1Pred, args1)
      val clauses1 = splitClauseBody2(head1, bodyHalf1, half1Constraints)

      val (head2, clauses2) = bodyHalf2 match {
        case Seq(head2) => (head2, List[Clause]())
        case bodyHalf2  => {
          val args2 = (for (IAtom(_, a) <- bodyHalf2; t <- a) yield t).distinct
          val half2Constraints = findRelevantConstraints(args2)

          val half2Pred = new Predicate ("temp" + tempPredicates.size, args2.size)
          tempPredicates += half2Pred

          val head2 = IAtom(half2Pred, args2)
          (head2, splitClauseBody2(head2, bodyHalf2, half2Constraints))
        }
      }

      clauses1 ++ clauses2 ++ List(Clause(head, List(head1, head2), and(constraint)))
    }

  //////////////////////////////////////////////////////////////////////////////
  // Alternative implementation, using fewer new predicates

  private def splitClauseBodies3(clauses : Seq[Clause],
                                 initialPreds : VerificationHints)
                               : (List[Clause], VerificationHints) = {
    // global list of all predicates, to ensure determinism
    val allPredicates = new LinkedHashSet[Predicate]

    // List of newly introduced predicates. Each new predicates represents
    // a vector of old predicates, possible containing some predicates multiple
    // times. An entry <List((p, 2), (q, 1)), p_q> expresses that the new
    // predicate p_q stands for the predicate vector <p, p, q>.
    val combiningPreds = new ArrayBuffer[(List[(Predicate, Int)], Predicate)]

    val newClauses = new ArrayBuffer[Clause]
    var newInitialPreds = initialPreds

    ////////////////////////////////////////////////////////////////////////////

    def createNewPredicateCounting(predCounts : List[(Predicate, Int)])
                                  : Predicate = {
      assert((predCounts map (_._1)).toSet.size == predCounts.size)

      val allPreds =
        (for ((p, num) <- predCounts; _ <- 0 until num) yield p).toList

      val newPred = new Predicate ((allPreds map (_.name)) mkString "_",
                                   (allPreds map (_.arity)).sum)
      combiningPreds += ((predCounts, newPred))
      allPredicates += newPred
      tempPredicates += newPred

      val definingBody = for ((p, num) <- allPreds.zipWithIndex) yield
        IAtom(p, for (k <- 0 until p.arity)
                 yield i(new ConstantTerm (p.name + "_" + num + "_" + k)))
      val definingHead = IAtom(newPred, for (IAtom(_, args) <- definingBody;
                                             a <- args) yield a)
      newClauses += Clause(definingHead, definingBody, i(true))

      // create initial predicates for the new symbol as well  
      var offset = 0
      var nextOffset = 0
      val initPreds =
        for (p <- allPreds;
             initPred <- {
               offset = nextOffset
               nextOffset = nextOffset + p.arity
               newInitialPreds.predicateHints.getOrElse(p, List())
             })
        yield initPred.shiftArguments(0, offset)

      if (!initPreds.isEmpty)
        newInitialPreds =
          newInitialPreds.addPredicateHints(Map(newPred -> initPreds))

      newPred
    }

    ////////////////////////////////////////////////////////////////////////////

    var changed = false

    for (clause <- clauses)
      newClauses += (
        if (clause.body.size <= maxClauseBodySize) {
          clause
        } else {
          changed = true

          val Clause(head, body, constraint) = clause

          for (IAtom(p, _) <- head :: body)
            allPredicates += p

          var bodySize = body.size
          val bodyLits = new MHashMap[Predicate, List[(IAtom, Tree[Int])]]
          val bodyWithIndexes =
            for ((a, n) <- body.zipWithIndex) yield (a, Leaf(n))
          for ((p, atoms) <- bodyWithIndexes groupBy (_._1.pred))
            bodyLits.put(p, atoms.toList)

          def combinePredicates(predCounts : List[(Predicate, Int)],
                                newPred : Predicate) = {
            val selAtoms =
              (for ((pred, num) <- predCounts; _ <- 0 until num) yield {
                 val atom :: rest = bodyLits(pred)
                 bodyLits.put(pred, rest)
                 atom
               }).toList
            val allArgs =
              (for (oldAtom <- selAtoms; a <- oldAtom._1.args) yield a).toList
            val indexTree =
              Tree(-1, selAtoms map (_._2))
            bodyLits.put(newPred,
              bodyLits.getOrElse(
                newPred,
                List()) ::: List((IAtom(newPred, allArgs), indexTree)))
          }

          while (bodySize > maxClauseBodySize) {
            (combiningPreds find {
               case (counts, pred) => counts forall {
                 case (p, num) => bodyLits.getOrElse(p, List()).size >= num
               }
             }) match {

              case Some((predCounts, newPred)) =>
                combinePredicates(predCounts, newPred)

              case None => {
                val selectedPredicates =
                  (allPredicates find {
                     p => bodyLits.getOrElse(p, List()).size >= maxClauseBodySize
                   }) match {
                    case Some(pred) =>
                      List((pred, maxClauseBodySize))
                    case None => {
                      var remaining = maxClauseBodySize
                      val counts = new ArrayBuffer[(Predicate, Int)]

                      val it = allPredicates.iterator
                      while (remaining > 0) {
                        val nextPred = it.next
                        val num = bodyLits.getOrElse(nextPred, List()).size
                        if (num > 0) {
                          val chosen = num min remaining
                          remaining = remaining - chosen
                          counts += ((nextPred, chosen))
                        }
                      }

                      counts.toList
                    }
                  }

                val newPred = createNewPredicateCounting(selectedPredicates)
                combinePredicates(selectedPredicates, newPred)
              }

            }

            bodySize = bodySize - maxClauseBodySize + 1
          }

          val newBody =
            (for (p <- allPredicates.iterator;
                  a <- bodyLits.getOrElse(p, List()).iterator)
             yield a).toList

          val newClause = Clause(head, newBody map (_._1), constraint)
          clauseBackMapping.put(newClause,
                                (clause, Tree(-1, newBody map (_._2))))

          newClause
        })

    if (changed)
      (newClauses.toList, newInitialPreds)
    else
      (clauses.toList, initialPreds)
  }
}
