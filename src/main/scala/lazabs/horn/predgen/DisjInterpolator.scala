/**
 * Copyright (c) 2011-2024 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.predgen

import ap.basetypes.{Tree, Leaf}
import ap.theories.{Theory, TheoryCollector}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               LazyConjunction}
import ap.terfor.{TermOrder, TerForConvenience, Term, OneTerm}
import ap.terfor.preds.Atom
import ap.terfor.substitutions.ConstantSubst
import ap.parser._
import ap.parameters.PreprocessingSettings
import ap.Signature
import ap.util.Timeout
import IExpression.{ConstantTerm, Predicate}

import lazabs.horn.Util._

import lazabs.horn.bottomup.HornClauses._

import ap.SimpleAPI
import SimpleAPI.ProverStatus

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 LinkedHashMap, ArrayBuffer}

object DisjInterpolator {

  import PredicateGenerator.{AndOrNode, AndNode, OrNode}

  /**
   * The predicate generator receives an and/or-clause-dag, and either
   * returns a list of new predicates, or a counterexample dag.
   */
  def iPredicateGenerator[CC <% ConstraintClause]
                         (clauseDag : Dag[AndOrNode[CC, Unit]])
                        : Either[Seq[(Predicate, Seq[IFormula])],
                                 Dag[(IAtom, Option[CC])]] = predicateGenerator(clauseDag) match {
    case Left(predicates) => {
      val simplifier = new Simplifier
      Left(for ((p, preds) <- predicates) yield {
        (p, for (c <- preds) yield simplifier(Internal2InputAbsy(c)))
      })
    }
    case Right(cex) =>
      Right(cex)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * The predicate generator receives an and/or-clause-dag, and either
   * returns a list of new predicates, or a counterexample dag.
   *
   * <code>orInterpolationTimeout</code> specifies the maximum time
   * (in milli-seconds) to
   * try disjunctive interpolation, before aborting and restarting
   * interpolation with a reduced number of or-nodes.
   */
  def predicateGenerator[CC <% ConstraintClause]
                        (clauseDag : Dag[AndOrNode[CC, Unit]],
                         orInterpolationTimeout : Int = Int.MaxValue)
                       : Either[Seq[(Predicate, Seq[Conjunction])],
                                Dag[(IAtom, Option[CC])]] = {
    val (factoredDag, localPreds) = factoring(clauseDag)
    var dag = factoredDag
    var res : Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, Option[CC])]] = null

    def simplify(andNum : Int, orNum : Int) = {
        // simplify the clause dag by removing some or-nodes
        val redirectedNodes =
          (for ((d, i) <- dag.iterator.zipWithIndex;
                if (d.isInstanceOf[OrNode[_, _]])) yield i).take((orNum+1)/2).toSet

        def redirect[A](cdag : Dag[AndOrNode[A, Unit]]) : Dag[AndOrNode[A, Unit]] = cdag match {
          case DagNode(d, children, next) => {
            val newNext = redirect(next)
            val newChildren = for (c <- children) yield {
              val redir = redirectedNodes contains (dag.size - cdag.size + c)
              (newNext drop (c - 1)) match {
                case DagNode(OrNode(_), c2 :: _, _) if (redir) => c + c2
                case _ => c
              }
            }
            DagNode(d, newChildren, newNext)
          }
          case DagEmpty => DagEmpty
        }

        dag = redirect(dag).elimUnconnectedNodes
      }

    while (res == null) {
      val andNum = dag.iterator.count(_.isInstanceOf[AndNode[_, _]])
      val orNum = dag.iterator.count(_.isInstanceOf[OrNode[_, _]])

      if (lazabs.GlobalParameters.get.log)
        print("(" + andNum + "and/" + orNum + "or) ")

      if (orInterpolationTimeout == Int.MaxValue ||
          isProbablyFeasible(andNum, orNum)) {
      Timeout.withTimeoutMillis(
        if (orNum == 0) Long.MaxValue else orInterpolationTimeout
      ) {
//        val bef = System.currentTimeMillis
        res = predicateGeneratorHelp(dag, {
                case (andNum, orNum) =>
                  !(orInterpolationTimeout == Int.MaxValue ||
                   isProbablyFeasible(andNum, orNum))
              }) match {
          case Left(preds) =>
            Left(for (pair@(p, conjs) <- preds;
                      if (!(localPreds contains p))) yield pair)
          case Right(cex) =>
            // TODO: properly reconstruct counterexample with original clauses
            Right(for (d <- cex) yield d match {
              case (a, Left(c)) => (a, Some(c))
              case (a, Right(_)) => (a, None)
            })
        }
//        println
//        println("success: " + (System.currentTimeMillis - bef) + ", " + andNum + ", " + orNum)
      } {
        // simplify the clause dag by removing some or-nodes
        if (lazabs.GlobalParameters.get.log)
          print(" ... restarting ")
      }
      } else {
        if (lazabs.GlobalParameters.get.log)
          print(" ... simplifying ")
      }

      if (res == null)
        simplify(andNum, orNum)
    }

/*
    printHornSMT(clauseDag,
                 if (res.isLeft && (dag eq factoredDag))
                   Some(true)
                 else if (res.isRight)
                   Some(false)
                 else
                   None)
*/

    res
  }

  /**
   * Is it likely that we can solve this problem in reasonable time?
   */
  private def isProbablyFeasible(andNum : Int, orNum : Int) : Boolean =
//    orNum == 0 || (andNum <= 65 && orNum <= 8 && orNum <= 25 - andNum * 3 / 10)
    orNum == 0 || (andNum <= 100 && orNum <= 20)

  //////////////////////////////////////////////////////////////////////////////

  private def predicateGeneratorHelp[CC <% ConstraintClause]
                        (clauseDag : Dag[AndOrNode[CC, Unit]],
                         giveUpCondition : (Int, Int) => Boolean)
                       : Either[Seq[(Predicate, Seq[Conjunction])],
                                Dag[(IAtom, CC)]] =
    SimpleAPI.withProver(enableAssert = lazabs.GlobalParameters.get.assertions) { p =>
      import p._

      val coll = new TheoryCollector

      for (AndNode(clause) <- clauseDag.iterator)
        clause collectTheories coll
      addTheories(coll.newTheories)
      coll.reset

      type SpanTree =
        Tree[(Int,                                   // Index of node in clauseDag
              AndOrNode[Seq[ConstantTerm],           // And: Local variables
                        (Seq[ConstantTerm],          // Or:  Relation variable arguments
                         Seq[IFormula])])]           //      Boolean variables for branches

      val definedArgSyms =
        Array.fill[List[(Seq[ConstantTerm], IFormula)]](clauseDag.size)(List())

      val branchFlagAncestors =
        new MHashMap[IFormula, Set[IFormula]]

      def createBranchFlags(num : Int, currentBFlag : IFormula) : List[IFormula] = {
        val res = createBooleanVariables(num).toList
        val anc : Set[IFormula] = currentBFlag match {
          case null => Set()
          case f => branchFlagAncestors(f)
        }
        for (f <- res)
          branchFlagAncestors.put(f, anc + f)
        res
      }

      def flag2Conj(f : IFormula) : Conjunction = {
        implicit val _ = order
        import TerForConvenience._
        f match {
          case IAtom(p, Seq()) => p(List())
        }
      }

      //////////////////////////////////////////////////////////////////////////

      var constCopyNum = 0

      def dag2TreeAnd(d : Dag[AndOrNode[CC, Unit]],
                      depth : Int,
                      recursionLimit : Int,
                      currentBFlag : IFormula) : SpanTree = d match {
        case DagNode(AndNode(clause), children, _) => {
          Timeout.check
          Tree((depth,
                AndNode(createConstantsRaw(clause.head.predicate.name + "_local",
                                           0 until clause.localVariableNum))),
               for (c <- children)
                 yield dag2TreeOr(d drop c, depth + c, recursionLimit, currentBFlag))
        }
        case _ => { assert(false); null } // should not be reachable
      }

      def dag2TreeOr(d : Dag[AndOrNode[CC, Unit]],
                     depth : Int,
                     recursionLimit : Int,
                     currentBFlag : IFormula) : SpanTree = {
        val (headLit, branchFlags, leafClauses) = d match {
          case DagNode(AndNode(clause), _, _) =>
            (clause.head, List(currentBFlag), clause.body.isEmpty)
          case DagNode(OrNode(_), children, _) => {
            val AndNode(clause) = d(children.head)
            val branchFlags = createBranchFlags(children.size, currentBFlag)
            (clause.head, branchFlags,
             (for (c <- children.iterator; AndNode(clause) = d(c))
              yield clause) forall (_.body.isEmpty))
          }
          case _ => { assert(false); null } // should not be reachable
        }

        val syms = for ((s, n) <- headLit.argumentSorts.zipWithIndex)
                   yield createConstantRaw(headLit.predicate.name + "_" +
                                           constCopyNum + "_" + n, s)
        constCopyNum = constCopyNum + 1

        dag2TreeOr2(d, depth,
                    if (leafClauses)
                      Int.MaxValue
                    else if (definedArgSyms(depth) exists {
                               case (_, f) => branchFlagAncestors(currentBFlag) contains f
                             })
                             //!definedArgSyms(depth).isEmpty)
                      0
//                     else if (branchFlags.size != 1)
//                      1
                    else
                      (recursionLimit - 1),
                    currentBFlag, branchFlags, syms)
      }

      def dag2TreeOr2(d : Dag[AndOrNode[CC, Unit]],
                      depth : Int,
                      recursionLimit : Int,
                      currentBFlag : IFormula,
                      branchFlags : Seq[IFormula],
                      syms : Seq[ConstantTerm]) : SpanTree = {
        val andChildren = d match {
          case DagNode(AndNode(_), _, _) => List(0)
          case DagNode(OrNode(_), children, _) => children
          case _ => { assert(false); null } // should not be reachable
        }

        Tree((depth, OrNode((syms, branchFlags))),
             if (recursionLimit > 0) {
               definedArgSyms(depth) =
                 (syms, currentBFlag) :: definedArgSyms(depth)
               for ((c, f) <- andChildren zip branchFlags)
                 yield dag2TreeAnd(d drop c, depth + c, recursionLimit, f)
             } else {
               List()
             })
      }

      val List(rootFlag) = createBranchFlags(1, null)
      var partialTree = dag2TreeOr(clauseDag, 0, Int.MaxValue, rootFlag)
//      partialTree.prettyPrint

      //////////////////////////////////////////////////////////////////////////

      def buildExpansion(t : SpanTree, headArgs : Seq[ConstantTerm])
                        : LazyConjunction = t match {
        case Tree((dagIndex, AndNode(localSyms)), children) => {
          implicit val o = order
          val AndNode(clause) = clauseDag(dagIndex)
          LazyConjunction(clause.instantiateConstraint(
            headArgs,
            for (Tree((_, OrNode((syms, _))), _) <- children) yield syms,
            localSyms,
            order)) &
          LazyConjunction.conj(for (c <- children.iterator)
                               yield buildExpansion(c, headArgs))
        }
        case Tree((_, OrNode((headArgs, branchFlags))), children)
            if (branchFlags.size == children.size) => {
          implicit val o = order
          LazyConjunction.disj(
            for ((c, f) <- children.iterator zip branchFlags.iterator)
            yield (buildExpansion(c, headArgs) &
                   LazyConjunction(flag2Conj(f))))
        }
        case Tree((_, OrNode((headArgs, branchFlags))), children) => {
//          implicit val o = order
//          LazyConjunction.disj(for (f <- branchFlags)
//                                 yield LazyConjunction(flag2Conj(f)))
          LazyConjunction.TRUE
        }
      }

      var expansion =
        ReduceWithConjunction(Conjunction.TRUE, order)(
                              buildExpansion(partialTree, null).toConjunction)

      //////////////////////////////////////////////////////////////////////////
      // The refinement loop to incrementally expand the clause dag to a tree

      def checkOrNodeNum = {
            var orNodes = 0
            var andNodes = 0
            for (t <- partialTree.subtrees.iterator) t match {
              case Tree((_, OrNode(_)), children) if (children.size > 1) =>
                orNodes = orNodes + 1
              case Tree((_, AndNode(_)), _) =>
                andNodes = andNodes + 1
              case _ => // nothing
            }
//            print("(after expansion: " + andNodes + "and/" + orNodes + "or) ")
            if (giveUpCondition(andNodes, orNodes))
              Timeout.raise
          }

      checkOrNodeNum

      push
      addAssertion(expansion)

      var didRefinement = true
      while (didRefinement &&
             {
               checkSat(false)
               while (getStatus(100) == ProverStatus.Running)
                 Timeout.check
               ???
             } == ProverStatus.Sat) {

// ??? == ProverStatus.Sat) {

        // search for leaves where the tree could be refined

        didRefinement = false

        // we simply store the first relation argument to remember at which
        // point we want to refine
        val refinementPoints = new MHashSet[ConstantTerm]
        val refinementDagIndexes = new MHashSet[Int]
        val newConstraints = new ArrayBuffer[(Predicate, Conjunction)]

        def findRefinements(t : SpanTree,
                            incomingClause : Option[CC],
                            clauseBodyIndex : Int) : Unit = t match {
          case Tree((dagIndex, AndNode(_)), children) => {
            val AndNode(clause) = clauseDag(dagIndex)
            for ((c, i) <- children.iterator.zipWithIndex)
              findRefinements(c, Some(clause), i)
          }

          case Tree((dagIndex, OrNode((syms, branchFlags))), List()) => {
            // check whether the values of the argument symbols
            // are genuine
            val bodyLit = incomingClause.get.body(clauseBodyIndex)

            if (!(refinementDagIndexes contains dagIndex) &&
                !(definedArgSyms(dagIndex) exists {
                    case (defSyms, flag) =>
                      evalPartial(flag) == Some(true) &&
                      (bodyLit.relevantArguments forall {
                         case j => eval(syms(j)) == eval(defSyms(j))
                       })
                  })) {
              // found a point to refine
              refinementDagIndexes += dagIndex
              refinementPoints += syms.head
            }
          }

          case Tree((_, OrNode((_, branchFlags))), List(child)) => {
//            assert(evalPartial(branchFlags.head) == Some(true))
            findRefinements(child, incomingClause, clauseBodyIndex)
          }

          case Tree((_, OrNode((_, branchFlags))), children) =>
            val contInd = branchFlags indexWhere (evalPartial(_) == Some(true))
            assert(contInd >= 0)
            findRefinements(children(contInd), incomingClause, clauseBodyIndex)
        }

        def refine(t : SpanTree,
                   currentBFlag : IFormula) : SpanTree = t match {
          case Tree((dagIndex, OrNode((syms, branchFlags))), List())
              if (!syms.isEmpty && (refinementPoints contains syms.head)) => {
            val newT = 
              dag2TreeOr2(clauseDag drop dagIndex,
                          dagIndex, 1, currentBFlag, branchFlags, syms)
            val IAtom(f, _) = currentBFlag
            newConstraints += ((f, buildExpansion(newT, syms).toConjunction))
            newT
          }
          case Tree((dagIndex, OrNode((syms, branchFlags))), children)
              if (branchFlags.size == children.size) => {
            val newChildren =
              for ((s, f) <- children zip branchFlags.toList) yield refine(s, f)
            if ((children.iterator zip newChildren.iterator) forall {
                  case (c1, c2) => c1 eq c2
                })
              // nothing changed
              t
            else
              Tree((dagIndex, OrNode((syms, branchFlags))), newChildren)
          }
          case Tree(d, children) => {
            val newChildren = for (s <- children) yield refine(s, currentBFlag)
            if ((children.iterator zip newChildren.iterator) forall {
                  case (c1, c2) => c1 eq c2
                })
              // nothing changed
              t
            else
              Tree(d, newChildren)
          }
        }

        def addConstraints(c : Conjunction) : Conjunction = {
          implicit val o = order
          import TerForConvenience._

          val predConj = c.predConj
          val newNegConjs =
            c.negatedConjs.update(c.negatedConjs map (addConstraints(_)),
                                  order)
          val newCons =
            (for ((f, con) <- newConstraints.iterator;
                  if (predConj.positiveLits exists (_.pred == f)))
             yield con) ++
            (for ((f, con) <- newConstraints.iterator;
                  if (predConj.negativeLits exists (_.pred == f)))
             yield !con)

          if ((newNegConjs eq c.negatedConjs) && !newCons.hasNext)
            c
          else
            conj(Iterator.single(c updateNegatedConjs newNegConjs) ++ newCons)
        }

        findRefinements(partialTree, None, 0)

        if (!refinementPoints.isEmpty) {
          pop

          if (lazabs.GlobalParameters.get.log)
            print(".")
          didRefinement = true
          partialTree = refine(partialTree, rootFlag)

          // check how many nodes we now have
          // (if the tree grows too big, give up and restart with a
          // subtree)
          checkOrNodeNum

          expansion = ReduceWithConjunction(Conjunction.TRUE, order)(
                                            addConstraints(expansion))
//      println(expansion)

          push
          addAssertion(expansion)
        }
      }

//      partialTree.prettyPrint

      //////////////////////////////////////////////////////////////////////////
      // Put together the result

      import TerForConvenience._
      ??? match {
        ////////////////////////////////////////////////////////////////////////
        case ProverStatus.Unsat => {
          // found a solvable clause tree, extract interpolants

          val allFlagConjs = new ArrayBuffer[Conjunction]

          val (constraintTree, vocTree) = {
            def conTree(t : SpanTree, currentGuard : Option[Conjunction])
                       : Tree[(Conjunction, (Predicate, Seq[ConstantTerm]))] = t match {
              case Tree((_, OrNode((headArgs, branchFlags))), children)
                  if (branchFlags.size == children.size) => {

                val clauseConstraints =
                  for (Tree((dagIndex, AndNode(localSyms)), children2) <- children)
                    yield {
                      val AndNode(clause) = clauseDag(dagIndex)
                      clause.instantiateConstraint(
                        headArgs,
                        for (Tree((_, OrNode((syms, _))), _) <- children2)
                          yield syms,
                        localSyms,
                        order)
                    }

                val headPred = {
                  val Tree((dagIndex, AndNode(_)), _) = children.head
                  val AndNode(clause) = clauseDag(dagIndex)
                  clause.head.predicate
                }

                if (children.size == 1) {
                  implicit val o = order
                  val Tree((_, AndNode(_)), children2) = children.head
                  Tree((currentGuard match {
                          case Some(g) => forall(g ==> clauseConstraints.head)
                          case None    => clauseConstraints.head
                        },
                        (headPred, headArgs)),
                       for (c <- children2) yield conTree(c, currentGuard))
                } else {
                  val flagPreds =
                    (for (IAtom(p, _) <- branchFlags.iterator)
                     yield createRelation(p.name, 1)).toList
                  implicit val o = order

                  for (p <- flagPreds)
                    allFlagConjs += p(List(l(0)))

//                  val flagsConj =
//                    (for (f <- branchFlags.iterator) yield flag2Conj(f)).toList

                  val cons =
                    disj(for ((c, p) <- clauseConstraints zip flagPreds) yield (c & p(List(l(0)))))
                  Tree((currentGuard match {
                          case Some(g) => forall(g ==> cons)
                          case None    => cons
                        },
                        (headPred, headArgs)),
                       for ((Tree(_, children2), p) <- children zip flagPreds;
                            c <- children2) yield conTree(c, Some(p(List(l(v(0)))))))
                }
              }
              case Tree((dagIndex, OrNode((headArgs, _))), List()) => {
                val headLit = (clauseDag drop dagIndex) match {
                  case DagNode(AndNode(clause), _, _) =>
                    clause.head
                  case DagNode(OrNode(_), c :: _, next) => {
                    val AndNode(clause) = next(c - 1)
                    clause.head
                  }
                  case _ => {
                    assert(false); null
                  }
                }
                Leaf((Conjunction.TRUE, (headLit.predicate, headArgs)))
              }
            }

            conTree(partialTree, None).unzip
          }

//          constraintTree.prettyPrint

          implicit val o = order

          TreeInterpolator.treeInterpolate(constraintTree, order, false,
                                           coll.theories) match {

            case Left(ints) => {

//            ints.prettyPrint
    
              val res = new LinkedHashMap[Predicate, List[Conjunction]]
              val reducer = ReduceWithConjunction(conj(allFlagConjs), order)
              for ((inter, (pred, syms)) <- (ints zip vocTree).iterator;
                   if (!inter.isTrue && !inter.isFalse)) {
                val symMap =
                  (syms.iterator zip (
                     for (i <- 0 until syms.size) yield v(i)).iterator).toMap
                val finalPred = reducer(ConstantSubst(symMap, order)(inter))
    
                def addPred(f : Conjunction) = {
                  val oldList = res.getOrElse(pred, List())
                  if (!(oldList contains f))
                    res.put(pred, f :: oldList)
                }
    
                if (!finalPred.isTrue && !finalPred.isFalse) {
                  addPred(finalPred)
    /*              if (!finalPred.isLiteral)
                    for (d <- enumAtoms(finalPred, false))
                      addPred(d) */
                }
              }
              Left(res.toSeq)
            }

            case _ => {
              throw new Exception ("Could not generate interpolants")
            }
          }
        }

        ////////////////////////////////////////////////////////////////////////
        case ProverStatus.Sat => {
          // found a genuine counterexample,
          // build a minimal counterexample dag

          implicit val o = order

          val cexNodes = {
            val nodes = new ArrayBuffer[SpanTree]

            def addNodes(t : SpanTree) : Unit = t match {
              case t@Tree((_, OrNode(_)), List()) =>
                nodes += t
              case t@Tree((_, OrNode((_, branchFlags))), children) => {
                nodes += t
                val contInd = branchFlags indexWhere (evalPartial(_) == Some(true))
                assert(contInd >= 0)
                addNodes(children(contInd))
              }
              case t@Tree((_, AndNode(_)), children) =>
                for (c <- children) addNodes(c)
            }
            addNodes(partialTree)

            nodes sortWith {
              case (Tree((c, _), _), Tree((d, _), _)) => c > d
            }
          }

          val fullDag = (DagEmpty.asInstanceOf[Dag[(IAtom, CC)]] /: cexNodes) {
            case (dag, Tree((_, OrNode(_)), List())) =>
              // disconnected node, which can be ignored at this point
              dag
            case (dag, Tree((_, OrNode((syms, branchFlags))), orChildren)) => {
              val contInd = branchFlags indexWhere (evalPartial(_) == Some(true))
              assert(contInd >= 0)

              val Tree((dagIndex, AndNode(_)), children) = orChildren(contInd)
              val AndNode(clause) = clauseDag(dagIndex)

              val bodyAtoms = for ((t, i) <- children.zipWithIndex) yield {
                val Tree((tIndex, OrNode((tSyms, _))), _) = t
                IAtom(clause.body(i).predicate,
                      for (c <- tSyms) yield evalToTerm(c))
              }
              val dagChildren =
                (for ((ba, bodyLit) <- bodyAtoms.iterator zip clause.body.iterator;
                      relevantSyms = bodyLit.relevantArguments) yield {
                   (for (((ba2, _), i) <- dag.iterator.zipWithIndex;
                         if (ba.pred == ba2.pred &&
                             (relevantSyms forall { j => ba(j) == ba2(j) })))
                    yield (i + 1)).toSeq.last
                 }).toList
              DagNode((IAtom(clause.head.predicate,
                             for (c <- syms) yield evalToTerm(c)),
                       clause),
                      dagChildren, dag)
            }
          }

          Right(fullDag.elimUnconnectedNodes)
        }

        ////////////////////////////////////////////////////////////////////////
        case ProverStatus.Inconclusive =>
          throw new Exception ("Could not generate interpolants, likely " +
                               "because of unsupported operators")
      }
    }


  //////////////////////////////////////////////////////////////////////////////

  private def enumAtoms(c : Conjunction,
                        negative : Boolean) : Iterator[Conjunction] =
    if (c.isLiteral || !c.quans.isEmpty) {
      Iterator single (if (negative) !c else c)
    } else if (c.isNegatedConjunction) {
      for (d <- c.negatedConjs.iterator; r <- enumAtoms(d, !negative)) yield r
    } else {
      for (d <- c.iterator; r <- enumAtoms(d, negative)) yield r
    }

  //////////////////////////////////////////////////////////////////////////////

  private def headLiteral[CC <% ConstraintClause]
                         (d : Dag[AndOrNode[CC, Unit]]) : Literal = d match {
    case DagNode(AndNode(c), _, _) => c.head
    case DagNode(OrNode(_), c :: _, next) => headLiteral(next drop (c-1))
    case _ => { assert(false); null }
  }

  /**
   * Simplify a dag by factoring out common sub-trees underneath or-nodes
   *
   * e.g.
   *    p :- q, r, u
   *    p :- s, q, u, v
   * becomes
   *    p :- t, q, u
   *    t :- r
   *    t :- s, v
   * with a fresh relation symbol t
   */
  private def factoring[CC <% ConstraintClause]
                       (clauseDag : Dag[AndOrNode[CC, Unit]])
                       : (Dag[AndOrNode[Either[CC, ConstraintClause], Unit]],
                          Seq[Predicate]) = {
    type CCDag = Dag[AndOrNode[Either[CC, ConstraintClause], Unit]]

    var dag : CCDag = for (c <- clauseDag) yield c match {
      case AndNode(c) => AndNode(Left(c))
      case OrNode(_) => OrNode(())
    }

    var localPreds = new ArrayBuffer[Predicate]

    var cont = true
    while (cont)
      (for ((d, i) <- dag.subdagIterator.zipWithIndex;
            if (d match {
                  case DagNode(OrNode(_), children, next) =>
                    !((for (c <- children.iterator) yield {
                         val DagNode(AndNode(_), children2, _) = next drop (c-1)
                         (for (c2 <- children2.iterator) yield (c + c2)).toSet
                       }) reduceLeft (_ & _)).isEmpty
                  case _ => false
                })) yield i).toSeq.lastOption match {
      case None => cont = false
      case Some(orNodeIndex) => {
        val DagNode(OrNode(_), orNodeChildren, orNodeNext) =
          dag drop orNodeIndex
        val sharedSubnodes = (for (c <- orNodeChildren.iterator) yield {
          val DagNode(AndNode(_), children2, _) = orNodeNext drop (c-1)
          for (c2 <- children2) yield (c + c2)
        }) reduceLeft (_ intersect _)

        val headLit = {
          val AndNode(clause) = orNodeNext(orNodeChildren.head - 1)
          clause.head
        }

        assert(!sharedSubnodes.isEmpty)

        val sharedSubdags = for (c <- sharedSubnodes) yield (orNodeNext drop (c-1))
        val sharedHeadLits = for (d <- sharedSubdags) yield headLiteral(d)

        val tempPred =
          new Predicate("t" + localPreds.size,
                        headLit.predicate.arity +
                        (for (l <- sharedHeadLits.iterator)
                           yield l.predicate.arity).sum)
        localPreds += tempPred

        val tempPredArgOffsets = {
          val it = (sharedHeadLits map (_.predicate.arity)).inits
          it.next
          for (s <- it) yield (s.sum + headLit.predicate.arity)
        }.toSeq.reverse

        var belowOrDag = orNodeNext

        for ((c, childIndex) <- orNodeChildren.zipWithIndex) {
          val DagNode(AndNode(clause), children2, _) = orNodeNext drop (c-1)
          val remainingSharedNodes = new ArrayBuffer[(Int, Int)]
          remainingSharedNodes ++= sharedSubnodes.iterator.zipWithIndex
          var nextLocalInd = 0

          val newBodyLits : List[Either[Int, Int]] =
            for ((c2, i) <- children2.zipWithIndex) yield {
              val target = c + c2
              (remainingSharedNodes indexWhere (_._1 == target)) match {
                case -1 => {
                  // not found, has to be kept as body literal
                  val res = Left(nextLocalInd)
                  nextLocalInd = nextLocalInd + 1
                  res
                }
                case ind => {
                  val (_, sharedInd) = remainingSharedNodes(ind)
                  remainingSharedNodes remove ind
                  Right(sharedInd)
                }
              }
            }

          assert(remainingSharedNodes.isEmpty)

          val newOrClause = new ConstraintClause {
            val head = sLit(tempPred)
            val body = for ((lit, Left(_)) <- clause.body zip newBodyLits)
                       yield lit
            val localVariableNum = clause.localVariableNum
            def instantiateConstraint(headArguments : Seq[ConstantTerm],
                                      bodyArguments: Seq[Seq[ConstantTerm]],
                                      localVariables : Seq[ConstantTerm],
                                      sig : Signature) = {
              val newHeadArgs = headArguments take headLit.predicate.arity
              val newBodyArgs = for (p <- newBodyLits) yield p match {
                case Left(newInd) =>
                  bodyArguments(newInd)
                case Right(sharedInd) => {
                  val o = tempPredArgOffsets(sharedInd)
                  headArguments.view(
                    o, o + sharedHeadLits(sharedInd).predicate.arity)
                }
              }
              clause.instantiateConstraint(newHeadArgs, newBodyArgs,
                                           localVariables, sig)
            }
          }

          belowOrDag = DagNode(
            AndNode(Right(newOrClause)),
            for ((Left(_), c2) <- newBodyLits zip children2)
              yield (c + c2 + childIndex),
            belowOrDag)          
        }

        val topClause = new ConstraintClause {
          val head = sLit(headLit.predicate)
          val body = sLit(tempPred) :: (
                     for (l <- sharedHeadLits.toList) yield sLit(l.predicate))
          val localVariableNum = 0
          def instantiateConstraint(headArguments : Seq[ConstantTerm],
                                    bodyArguments: Seq[Seq[ConstantTerm]],
                                    localVariables : Seq[ConstantTerm],
                                    sig : Signature) = {
            import TerForConvenience._
            implicit val _ = sig.order
            val tempPredArgs = bodyArguments.head
            (headArguments === tempPredArgs.take(headArguments.size)) & conj(
                for ((args, o) <- bodyArguments.tail zip tempPredArgOffsets)
                yield (args === tempPredArgs.view(o, o + args.size)))
          }
        }

        belowOrDag =
          DagNode(AndNode(Right(topClause)),
                  1 :: (for (i <- sharedSubnodes) yield (i + orNodeChildren.size + 1)),
          DagNode(OrNode(()), (1 to orNodeChildren.size).toList, belowOrDag))

//        belowOrDag.prettyPrint

        def replaceSubdag(d : CCDag, depth : Int) : CCDag =
          if (depth == orNodeIndex) {
            belowOrDag
          } else {
            val DagNode(c, children, next) = d
            DagNode(c,
                    for (c <- children) yield (
                      if (depth + c > orNodeIndex) (c + orNodeChildren.size + 1) else c),
                    replaceSubdag(next, depth + 1))
          }

        dag = replaceSubdag(dag, 0).elimUnconnectedNodes

/*(for (d <- dag) yield d match {
  case OrNode(_) => OrNode(())
  case AndNode(c) => AndNode(c.hashCode)
}).prettyPrint */
      }
    }

    (dag, localPreds)
  }

  //////////////////////////////////////////////////////////////////////////////

  private val baseDir           = "/tmp/horn-benchmarks/"
  private val linearTreeLikeDir = baseDir + "linear-tree-like/"
  private val treeLikeDir       = baseDir + "tree-like/"
  private val linearDir         = baseDir + "linear/"
  private val bodyDisjointDir   = baseDir + "body-disjoint/"
  private val headUniqueDir     = baseDir + "head-unique/"
  private val generalDir        = baseDir + "general/"

  var benchmarkCounter = 0

  private def printHornSMT[CC <% ConstraintClause]
                          (clauseDag : Dag[AndOrNode[CC, Unit]],
                           solvable : Option[Boolean]) : Unit = {
    println("printing in SMT format ...")

    val usedIndexes = new MHashSet[Int]
    usedIndexes += 0
    for ((d, i) <- clauseDag.subdagIterator.zipWithIndex) d match {
      case DagNode(AndNode(_), children, _) =>
        for (c <- children)
          usedIndexes += (i + c)
      case _ => // nothing
    }

    val freshRelSyms = new MHashMap[Int, Atom]
    var order = TermOrder.EMPTY

    for ((d, i) <- clauseDag.subdagIterator.zipWithIndex)
      if (usedIndexes contains i) {
        val DagNode(c, children, next) = d
        val headLit = c match {
          case AndNode(clause) =>
            clause.head
          case OrNode(_) => {
            val AndNode(clause) = next(children.head - 1)
            clause.head
          }
        }
        val pred =
          new Predicate (headLit.predicate.name + "_" + i, headLit.predicate.arity)
        val args =
          (for (j <- 0 until pred.arity) yield new ConstantTerm("p" + j)).toList
        order = order extend args
        if (headLit.predicate != FALSE)
          order = order extendPred pred

        implicit val _ = order
        import TerForConvenience._
        freshRelSyms.put(i, Atom(pred, for (c <- args) yield l(c), order))
      }

    ////////////////////////////////////////////////////////////////////////////

    val clauseFormulas = new ArrayBuffer[IFormula]
    val clauseSchemas = new ArrayBuffer[(Predicate, Seq[Predicate])]

    for ((d, i) <- clauseDag.subdagIterator.zipWithIndex)
      (freshRelSyms get i) match {
        case Some(headAtom) => {
          import TerForConvenience._

          def argsAsConsts(a : Atom) =
            for (l <- a) yield l.leadingTerm.asInstanceOf[ConstantTerm]

          def printClause(d : Dag[AndOrNode[CC, Unit]], index : Int) = {
            val DagNode(AndNode(clause), children, _) = d

            val localVars = (for (i <- 0 until clause.localVariableNum)
                               yield new ConstantTerm("v" + i)).toList
            implicit val o = order extend localVars

            val bodyAtoms = for (c <- children) yield freshRelSyms(index + c)
            val constraint =
              clause.instantiateConstraint(argsAsConsts(headAtom),
                                           for (a <- bodyAtoms) yield argsAsConsts(a),
                                           localVars,
                                           o)

            val head = clause.head.predicate match {
              case FALSE => Conjunction.FALSE
              case _ => conj(headAtom)
            }

            val matrix =
              (conj(for (a <- bodyAtoms) yield a) & constraint) ==> head
            val quanClause =
              forall(argsAsConsts(headAtom) ++
                     (for (a <- bodyAtoms; c <- argsAsConsts(a)) yield c) ++
                     localVars,
                     matrix)

            clauseFormulas += !Internal2InputAbsy(
                            ReduceWithConjunction(Conjunction.TRUE, o)(quanClause))
            clauseSchemas += ((clause.head.predicate match {
                                 case FALSE => FALSE
                                 case _ => headAtom.pred
                               },
                               for (a <- bodyAtoms) yield a.pred))
          }

          d match {
            case DagNode(AndNode(_), _, _) =>
              printClause(d, i)
            case DagNode(OrNode(_), children, next) =>
              for (c <- children)
                printClause(next drop (c - 1), i + c)
          }
        }
        case None =>
          // clause that can be ignored here
      }

    ////////////////////////////////////////////////////////////////////////////

    val isLinear = clauseSchemas forall (_._2.size <= 1)
    val isBodyDisjoint = {
      var res = true
      val bodyPreds = new MHashSet[Predicate]
      for ((_, body) <- clauseSchemas; p <- body)
        if (!(bodyPreds add p))
          res = false
      res
    }
    val isHeadUnique = ((clauseSchemas map (_._1)).toSet.size == clauseSchemas.size)

    val dir = (isLinear, isBodyDisjoint, isHeadUnique) match {
      case (true,  true,  true) => linearTreeLikeDir
      case (true,  _,     _)    => linearDir
      case (_,     true,  true) => treeLikeDir
      case (_,     true,     _) => bodyDisjointDir
      case (_,     _  ,   true) => headUniqueDir
      case _                    => generalDir
    }

    (new java.io.File(dir)).mkdirs
    val basename = (new java.io.File(lazabs.GlobalParameters.get.fileName)).getName
    val benchmarkFile =
      new java.io.FileOutputStream(dir + basename + "-" +
                                   ("%04d".format(benchmarkCounter)) + ".smt2")
    benchmarkCounter = benchmarkCounter + 1
    Console.withOut(benchmarkFile) {
      SMTLineariser.printWithDeclsSig(
        formulas      = clauseFormulas,
        signature     = Signature(Set(), Set(), Set(), order restrict Set()),
        logic         = "HORN",
        status        = solvable match {
                          case Some(true) => "sat"
                          case Some(false) => "unsat"
                          case None => "unknown"
                        },
        benchmarkName = "Horn constraint system (" +
                          clauseFormulas.size + " clauses, " +
                          order.orderedPredicates.size + " relation symbols)\n" +
                          "    Generated by Eldarica (https://github.com/uuverifiers/eldarica)")
    }
    benchmarkFile.close
  }

  //////////////////////////////////////////////////////////////////////////////

/*
  {
    println("Testing and-or dag interpolation ...")
    import IExpression._

    val p = new Predicate("p", 1)
    val s = new Predicate("s", 1)

    val c1 = new IConstraintClause {
      val head = sLit(p)
      val body = List()
      val localVariableNum = 0
      def iInstantiateConstraint(headArguments : Seq[ConstantTerm],
                                 bodyArguments: Seq[Seq[ConstantTerm]],
                                 localVariables : Seq[ConstantTerm]) : IFormula = {
        val Seq(x) = headArguments
        x >= 0
      }
      override def toString = "c1"
    }

    val c2 = new IConstraintClause {
      val head = sLit(s)
      val body = List(sLit(p))
      val localVariableNum = 0
      def iInstantiateConstraint(headArguments : Seq[ConstantTerm],
                                 bodyArguments: Seq[Seq[ConstantTerm]],
                                 localVariables : Seq[ConstantTerm]) : IFormula = {
        val Seq(x) = headArguments
        val Seq(Seq(y)) = bodyArguments
        x === y + 1
      }
      override def toString = "c2"
    }

    val c3 = new IConstraintClause {
      val head = sLit(s)
      val body = List(sLit(p))
      val localVariableNum = 0
      def iInstantiateConstraint(headArguments : Seq[ConstantTerm],
                                 bodyArguments: Seq[Seq[ConstantTerm]],
                                 localVariables : Seq[ConstantTerm]) : IFormula = {
        val Seq(x) = headArguments
        val Seq(Seq(y)) = bodyArguments
        x === y + 5
      }
      override def toString = "c3"
    }

    val c4 = new IConstraintClause {
      val head = sLit(s)
      val body = List(sLit(s), sLit(s))
      val localVariableNum = 0
      def iInstantiateConstraint(headArguments : Seq[ConstantTerm],
                                 bodyArguments: Seq[Seq[ConstantTerm]],
                                 localVariables : Seq[ConstantTerm]) : IFormula = {
        val Seq(x) = headArguments
        val Seq(Seq(y), Seq(z)) = bodyArguments
        x === y - 3 & y === z
      }
      override def toString = "c4"
    }

    val c5 = new IConstraintClause {
      val head = sLit(FALSE)
      val body = List(sLit(s))
      val localVariableNum = 0
      def iInstantiateConstraint(headArguments : Seq[ConstantTerm],
                                 bodyArguments: Seq[Seq[ConstantTerm]],
                                 localVariables : Seq[ConstantTerm]) : IFormula = {
        val Seq(Seq(x)) = bodyArguments
        x < 0
      }
      override def toString = "c5"
    }

    val clauseDag =
      DagNode(AndNode[IConstraintClause, Unit](c5), List(1),
      DagNode(OrNode[IConstraintClause, Unit](), List(1, 2),
      DagNode(AndNode[IConstraintClause, Unit](c2), List(3),
      DagNode(AndNode[IConstraintClause, Unit](c4), List(1, 1),
      DagNode(AndNode[IConstraintClause, Unit](c3), List(1),
      DagNode(AndNode[IConstraintClause, Unit](c1), List(),
        DagEmpty
      ))))))

    clauseDag.prettyPrint

    println(iPredicateGenerator(clauseDag))
  }
*/
}
