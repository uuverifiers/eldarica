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

package lazabs.horn.bottomup

import ap.basetypes.IdealInt
import ap.parser._
import ap.Signature
import ap.theories.{Theory, TheoryCollector}
import ap.terfor.{ConstantTerm, TermOrder, TerForConvenience, Term, OneTerm, Formula}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.substitutions.{ConstantSubst, VariableSubst}
import ap.proof.{ModelSearchProver, QuantifierElimProver}
import ap.util.Seqs

import lazabs.prover.{Tree, Leaf}
import Util._
import DisjInterpolator._

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 LinkedHashMap, ArrayBuffer}
import ap.SimpleAPI
import SimpleAPI.ProverStatus

object DagInterpolator {

  import HornPredAbs._
  import TerForConvenience._

  //////////////////////////////////////////////////////////////////////////////

  def stripOrNodes[A, B](dag : Dag[AndOrNode[A, B]]) : Dag[A] = {
    // redirect all edges to or-nodes to the first child
    def redirect(dag : Dag[AndOrNode[A, B]]) : Dag[AndOrNode[A, B]] = dag match {
      case DagNode(d, children, next) => {
        val newNext = redirect(next)
        val newChildren = for (c <- children) yield {
          (newNext drop (c - 1)) match {
            case DagNode(AndNode(_), _, _) => c
            case DagNode(OrNode(_), c2 :: _, _)  => c + c2
            case _ => { assert(false); 1 }
          }
        }
        DagNode(d, newChildren, newNext)
      }
      case DagEmpty => DagEmpty
    }
    val newDag = redirect(dag) match {
      case DagNode(OrNode(_), c :: _, next)  => next drop (c - 1)
      case x => x
    }
    for (d <- newDag.elimUnconnectedNodes) yield d match {
      case AndNode(x) => x
      case _ => { assert(false); throw new Exception }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * takes dag - either new pred or counter example
   * modify clauese dag - introduce relations
   */ 
  def interpolatingPredicateGen(clauseDag : Dag[NormClause])
                               : Either[Seq[(Predicate, Seq[Conjunction])],
                                        Tree[IAtom]] = {
//        (for (c <- clauseDag) yield c.head).prettyPrint

//    val expandedDag = expandSharedClauses(clauseDag)

    def extractSpanningTree(d : Dag[NormClause]) = {
      val coveredNodes = new MHashSet[Int]
      def extractSpanningTreeHelp(d : Dag[NormClause], depth : Int)
                             : Tree[Either[NormClause, RelationSymbol]] =
        if (coveredNodes add depth) {
          val DagNode(clause, children, _) = d
          Tree(Left(clause),
               for (c <- children) yield extractSpanningTreeHelp(d drop c, depth + c))
        } else {
          Leaf(Right(d.head.head._1))
        }
      extractSpanningTreeHelp(d, 0)
    }
 
    partialPredicateGen(extractSpanningTree(clauseDag), false) match {
      case Left(preds) =>
        Left(preds)
      case Right(_) => {
        if (lazabs.GlobalParameters.get.log)
          print(" ... expanding,")
//        partialPredicateGen((for (c <- clauseDag) yield Left(c)).toTree)
        partialPredicateGen(extractSpanningTree(expandSharedClauses(clauseDag)), true)
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Generate predicates using ordinary tree interpolation
   */
  def interpolatingPredicateGenCEX(clauseDag : Dag[AndOrNode[NormClause, Unit]])
                     : Either[Seq[(Predicate, Seq[Conjunction])],
                              Dag[(IAtom, NormClause)]] =
    interpolatingPredicateGenCEX(clauseDag, TreeInterpolator.treeInterpolate _)

  def interpolatingPredicateGenCEX(clauseDag : Dag[AndOrNode[NormClause, Unit]],
                                   treeInterpolator : TreeInterpolator.TreeInterpolatorFun)
                     : Either[Seq[(Predicate, Seq[Conjunction])],
                              Dag[(IAtom, NormClause)]] =
    cexGuidedExpansion(stripOrNodes(clauseDag)) match {
      case Left(partialTree) =>
        partialPredicateGen(partialTree, false, treeInterpolator) match {
          case Left(preds) =>
            Left(preds)
          case _ => { assert(false); null }
        }
      case Right(cex) =>
        Right(cex)
    }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Generate predicates using disjunctive interpolation
   */
  def interpolatingPredicateGenCEXAndOr(clauseDag : Dag[AndOrNode[NormClause, Unit]])
                     : Either[Seq[(Predicate, Seq[Conjunction])],
                              Dag[(IAtom, HornPredAbs.NormClause)]] =
    predicateGenerator(clauseDag, 1500) match {
      case Left(preds) =>
        Left(preds)
      case Right(cex) => {
        var badCEX = false
        val res = Right(for (p <- cex) yield p match {
          case (a, None) => {
            badCEX = true
            (a, null)
          }
          case (a, Some(c)) => (a, c)
        })

        if (badCEX)
          // fall back to tree interpolation to construct a proper
          // counterexample
          interpolatingPredicateGenCEX(clauseDag)
        else
          res
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Generate predicates using disjunctive interpolation, feeding problems
   * with many or-nodes back into the predicate abstraction engine
   */
  def layeredPredicateGen(clauseDag : Dag[AndOrNode[NormClause, Unit]])
                     : Either[Seq[(Predicate, Seq[Conjunction])],
                              Dag[(IAtom, NormClause)]] = {
    val orNum = clauseDag.iterator.count(_.isInstanceOf[OrNode[_, _]])

    if (orNum <= 4) {
      interpolatingPredicateGenCEXAndOr(clauseDag)
    } else {
      // extract a set of recursion-free Horn clauses
      if (lazabs.GlobalParameters.get.log)
        print("(" + orNum + "or) CEGAR interpolator")
      layeredPredicateGenHelp(clauseDag)
    }
  }

  def layeredPredicateGenHelp[CC <% HornClauses.ConstraintClause]
                             (clauseDag : Dag[AndOrNode[CC, Unit]])
                     : Either[Seq[(Predicate, Seq[Conjunction])],
                              Dag[(IAtom, CC)]] = {
      import HornClauses._

      val usedIndexes = new MHashSet[Int]
      usedIndexes += 0
      for ((d, i) <- clauseDag.subdagIterator.zipWithIndex) d match {
        case DagNode(AndNode(_), children, _) =>
          for (c <- children)
            usedIndexes += (i + c)
        case _ => // nothing
      }

      val freshPredicates = new MHashMap[Int, HornClauses.Literal]
      val predMap = new LinkedHashMap[Predicate, List[Predicate]]

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
          if (headLit.predicate == FALSE) {
            freshPredicates.put(i, headLit)
          } else {
            val pred =
              new Predicate (headLit.predicate.name + "_" + i, headLit.predicate.arity)
            freshPredicates.put(i, sLit(pred))
            predMap.put(headLit.predicate,
                        pred :: predMap.getOrElse(headLit.predicate, List()))
          }
        }
      
      //////////////////////////////////////////////////////////////////////////

      val clauses = new ArrayBuffer[ConstraintClause]
      val clauseMapping = new MHashMap[ConstraintClause, CC]

      for ((d, i) <- clauseDag.subdagIterator.zipWithIndex)
        (freshPredicates get i) match {
          case Some(headLit) => {
            def genClause(d : Dag[AndOrNode[CC, Unit]], index : Int) = {
              val DagNode(AndNode(clause), children, _) = d
              val newClause = new ConstraintClause {
                val head : Literal = headLit
                val body : Seq[Literal] =
                  for (c <- children) yield freshPredicates(index + c)
                def localVariableNum : Int = clause.localVariableNum
                def instantiateConstraint(headArguments : Seq[ConstantTerm],
                                          bodyArguments: Seq[Seq[ConstantTerm]],
                                          localVariables : Seq[ConstantTerm],
                                          sig : Signature) : Conjunction =
                  clause.instantiateConstraint(headArguments, bodyArguments,
                                               localVariables, sig)
              }
              clauses += newClause
              clauseMapping.put(newClause, clause)
            }

            d match {
              case DagNode(AndNode(_), _, _) =>
                genClause(d, i)
              case DagNode(OrNode(_), children, next) =>
                for (c <- children)
                  genClause(next drop (c - 1), i + c)
            }
          }
          case None => // no clause here
        }

/*
    // Version 1 (of predicate extraction)
    Console.withOut(HornWrapper.NullStream)(
      new HornPredAbs(clauses, Map(),
                      DagInterpolator.interpolatingPredicateGenCEXAndOr _,
                      HornPredAbs.CounterexampleMethod.FirstBestShortest).rawResult) match {
      case Left(solution) =>
        Left((for ((p, freshPs) <- predMap.iterator;
                   formulas = for (q <- freshPs;
                                   c <- (solution get q).toSeq;
                                   if (!c.isTrue && !c.isFalse)) yield c;
                   if (!formulas.isEmpty)) yield (p, formulas.distinct)).toList)
      case Right(cex) =>
        Right(cex)
    }
*/

    // Version 2 (of predicate extraction)
    Console.withOut(HornWrapper.NullStream){
      val predAbs = new HornPredAbs(clauses, Map(),
                                    DagInterpolator.interpolatingPredicateGenCEXAndOr _,
                                    HornPredAbs.CounterexampleMethod.FirstBestShortest)
      predAbs.rawResult match {
      case Left(_) =>
        // extract the predicates used for the sub-proof
        Left((for ((p, freshPs) <- predMap.iterator;
                   formulas = for (q <- freshPs;
                                   c <- predAbs.relevantRawPredicates.getOrElse(q, List())) yield c;
                   if (!formulas.isEmpty)) yield (p, formulas.distinct)).toList)
      case Right(cex) =>
        // TODO: used predicates at this point are not correct!
        Right(for (p <- cex) yield (p._1, clauseMapping(p._2)))
    }}

/*
    // Version 3 (of predicate extraction)
    Console.withOut(HornWrapper.NullStream){
      val predAbs = new HornPredAbs(clauses, Map(),
                                    DagInterpolator.interpolatingPredicateGenCEXAndOr _,
                                    HornPredAbs.CounterexampleMethod.FirstBestShortest)
      predAbs.rawResult match {
      case Left(_) =>
        // extract the predicates used for the sub-proof
        Left((for ((p, freshPs) <- predMap.iterator;
                   formulas = for (q <- freshPs;
                                   c <- predAbs.relevantDisjuncts.getOrElse(q, List())) yield c;
                   if (!formulas.isEmpty)) yield (p, formulas.distinct)).toList)
      case Right(cex) =>
        Right(cex)
    }}
*/
  }


  //////////////////////////////////////////////////////////////////////////////

  def partialPredicateGen(spanningTree : Tree[Either[NormClause, RelationSymbol]],
                          fullCEX : Boolean)
                 : Either[Seq[(Predicate, Seq[Conjunction])], Tree[IAtom]] =
    partialPredicateGen(spanningTree, fullCEX, TreeInterpolator.treeInterpolate _)

  def partialPredicateGen(spanningTree : Tree[Either[NormClause, RelationSymbol]],
                          fullCEX : Boolean,
                          treeInterpolator : TreeInterpolator.TreeInterpolatorFun)
                 : Either[Seq[(Predicate, Seq[Conjunction])], Tree[IAtom]] = {
    val theories = {
      val coll = new TheoryCollector
      for (Left(NormClause(constraint, _, _)) <- spanningTree.iterator)
        coll(constraint.order)
      coll.theories
    }

    implicit val sf = new SymbolFactory (theories)

    if (lazabs.GlobalParameters.get.log)
      print(" " + spanningTree.size + " clauses ...")

/*
    assert(clauseTree.d.head._1.pred == HornClauses.FALSE &&
           (clauseTree.subtrees.iterator forall {
             case(Tree(clause, children)) =>
               clause.body.size == children.size &&
               ((clause.body.iterator zip children.iterator) forall {
                 case ((RelationSymbol(p), _), Tree(NormClause(_, _, (RelationSymbol(q), _)), _)) =>
                   p == q
               })
           }))
*/

    val vocabularyTree = for (c <- spanningTree) yield c match {
      case Left(NormClause(_, _, (rs, _))) =>
        sf.genConstants(rs.name, rs.arity, "")
      case Right(rs) =>
        sf.genConstants(rs.name, rs.arity, "")
    }

    val constraintTree =
      for (p <- spanningTree zip vocabularyTree.subtrees;
           (eitherClause, Tree(args, subVocTrees)) = p) yield eitherClause match {
        case Right(_) => Conjunction.TRUE
        case Left(clause) => {
          val newLocalSyms = sf duplicateConstants clause.localSymbols
          clause.substituteSyms(newLocalSyms, args,
                                for (Tree(cs, _) <- subVocTrees) yield cs)(sf.order)
        }
      }
    
    callInterpolator(spanningTree, constraintTree, vocabularyTree, sf.order,
                     theories, treeInterpolator)
  }

  def callInterpolator(spanningTree : Tree[Either[NormClause, RelationSymbol]],
                       constraintTree : Tree[Conjunction],
                       vocabularyTree : Tree[Seq[ConstantTerm]],
                       order : TermOrder)
                      : Either[Seq[(Predicate, Seq[Conjunction])], Tree[IAtom]] = {
    val theories = {
      val coll = new TheoryCollector
      for (c <- constraintTree)
        coll(c.order)
      coll.theories
    }

    callInterpolator(spanningTree, constraintTree, vocabularyTree, order, theories,
                     TreeInterpolator.treeInterpolate _)
  }

  def callInterpolator(spanningTree : Tree[Either[NormClause, RelationSymbol]],
                       constraintTree : Tree[Conjunction],
                       vocabularyTree : Tree[Seq[ConstantTerm]],
                       order : TermOrder,
                       theories : Seq[Theory],
                       treeInterpolator : TreeInterpolator.TreeInterpolatorFun)
                      : Either[Seq[(Predicate, Seq[Conjunction])], Tree[IAtom]] = {
    treeInterpolator(constraintTree, order, false, theories) match {
      case Right(m) => { assert(false); null } // should not happen
/*
        if (fullCEX) => {
        // found a countermodel
        val reducer = sf reducer m
        implicit val o = order
        def createAtom(p : Predicate, syms : Seq[ConstantTerm]) =
                  Atom(p, for (c <- syms) yield {
                            val redEq = reducer(c === v(0))
                            if ((redEq(0) get c).isZero)
                              l(-redEq(0).constant)
                            else
                              l(c)
                          },
                       order)
        Right(for (pair <- vocabularyTree zip spanningTree;
                   val (syms, eitherClause) = pair) yield eitherClause match {
                case Right(RelationSymbol(p)) =>
                  createAtom(p, syms)
                case Left(NormClause(_, _, (RelationSymbol(p), _))) =>
                  createAtom(p, syms)
        })
      }
      case Right(m) => {
        // found a countermodel
        Right(null)
      } */
      case Left(ints) => {
        val res = new LinkedHashMap[Predicate, List[Conjunction]]
        for (((pred, Left(NormClause(_, _, (RelationSymbol(p), _)))), syms) <-
                (ints zip spanningTree zip vocabularyTree).iterator;
             if (!pred.isTrue && !pred.isFalse)) {
          val symMap =
            (syms.iterator zip (
               for (i <- 0 until syms.size) yield v(i)).iterator).toMap
          val finalPred = ConstantSubst(symMap, order)(pred)
          val oldList = res.getOrElse(p, List())
          if (!(oldList contains finalPred))
            res.put(p, finalPred :: oldList)
        }
        Left(res.toSeq)
      }
    }
  }


  //////////////////////////////////////////////////////////////////////////////

  /**
   * Duplicate nodes of the dag that are called with possibly different
   * arguments
   */
  def expandSharedClauses(clauseDag : Dag[NormClause]) : Dag[NormClause] = {
    implicit val sf = new SymbolFactory (List())

    var currentDag = clauseDag
    val currentEquations = new UnionFind[ConstantTerm]
    val literalSyms = new MHashMap[IdealInt, ConstantTerm]

    val childrenSyms = new ArrayBuffer[Seq[Seq[ConstantTerm]]]

    def addConstraint(clause : NormClause,
                      connectedSyms : Option[(Int, Int)]) = {
      val newSyms = new MHashMap[ConstantTerm, ConstantTerm]
      for (c <- clause.allSymbols) {
        val newSym = new ConstantTerm(c.name)
        newSyms.put(c, newSym)
        currentEquations makeSet newSym
      }
      childrenSyms +=
        (for (cs <- clause.bodySyms) yield (cs map (newSyms(_))))

      connectedSyms match {
        case None => // nothing
        case Some((i, j)) =>
          for ((c, d) <- clause.headSyms.iterator zip childrenSyms(i)(j).iterator)
            currentEquations.union(newSyms(c), d)
      }

      for (lc <- clause.constraint.arithConj.positiveEqs) lc match {
        case Seq((IdealInt.ONE, c : ConstantTerm),
                 (IdealInt.MINUS_ONE, d : ConstantTerm)) => {
          currentEquations.union(newSyms(c), newSyms(d))
        }
        case Seq((IdealInt.ONE, c : ConstantTerm),
                 (value, OneTerm)) => {
          val litSym = literalSyms.getOrElseUpdate(-value, {
            val const = new ConstantTerm("v"+(-value))
            currentEquations makeSet const
            const
          })
          currentEquations.union(newSyms(c), litSym)
        }
        case _ =>
          // nothing
      }
    }

    var currentInd = 0
    while (currentInd < currentDag.size &&
           (literalSyms.valuesIterator map (currentEquations(_))).toSet.size ==
             literalSyms.size) {
      val suffixDag@DagNode(clause, children, _) = currentDag drop currentInd

      // are there multiple paths leading to the next node?
      val preds = currentDag incoming currentInd

      if (preds.size > 1) {
        // then this node might have to be duplicated. compute equivalence
        // classes of the passed arguments

        def equalArgs(i : Int, j : Int) = {
          val (i1, i2) = preds(i)
          val (j1, j2) = preds(j)
          (childrenSyms(i1)(i2).iterator zip childrenSyms(j1)(j2).iterator) forall {
            case (c, d) => currentEquations(c) == currentEquations(d)
          }
        }

        val classes = new ArrayBuffer[List[Int]]
        for (i <- 0 until preds.size) {
          val exClass = classes indexWhere {
            case List() => false // unreachable
            case j :: _ => equalArgs(i, j)
          }
          if (exClass >= 0)
            classes(exClass) = i :: classes(exClass)
          else
            classes += List(i)
        }

        if (classes.size > 1) {
          // ok, need to duplicate
          var newDag = suffixDag
          
          for (i <- 1 until classes.size)
            newDag = DagNode(clause, children map (_ + i), newDag)

          def addPrefix(todo : Dag[NormClause], ind : Int) : Unit = if (ind < currentInd) {
            val DagNode(prefixClause, children, tail) = todo
            addPrefix(tail, ind + 1)
            newDag = DagNode(prefixClause,
                             for ((c, i) <- children.zipWithIndex) yield {
                               if (ind + c < currentInd) {
                                 c
                               } else if (ind + c > currentInd) {
                                 c + classes.size - 1
                               } else {
                                 val j = preds indexOf ((ind, i))
                                 val classNum = classes indexWhere (_ contains j)
                                 assert(classNum >= 0)
                                 c + classNum
                               }
                             },
                             newDag)
          }

          addPrefix(currentDag, 0)
          currentDag = newDag

          for (i :: _ <- classes)
            addConstraint(clause, Some(preds(i)))
          currentInd = currentInd + classes.size - 1

        } else {
          addConstraint(clause, preds.headOption)
        }
      } else {
        addConstraint(clause, preds.headOption)
      }

      currentInd = currentInd + 1
    }

    currentDag
  }

  //////////////////////////////////////////////////////////////////////////////

  def cexGuidedExpansion(clauseDag : Dag[NormClause])
                        : Either[Tree[Either[NormClause, RelationSymbol]],
                                 Dag[(IAtom, NormClause)]] = SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>
    import p._

    type SpanTree = Tree[(Int, Seq[ConstantTerm], Option[Seq[ConstantTerm]])]

    val definedArgSyms =
      Array.fill[List[Seq[ConstantTerm]]](clauseDag.size)(List())

    def dag2Tree(d : Dag[NormClause], depth : Int) : SpanTree = {
      val DagNode(clause@NormClause(constraint, _, (rs, _)), children, _) = d
      addTheoriesFor(constraint.order)
      val syms = for ((s, n) <- rs.argumentSorts.zipWithIndex)
                 yield createConstantRaw(rs.name + "_" + n, s)
      if (children.isEmpty || definedArgSyms(depth).isEmpty) {
        definedArgSyms(depth) = syms :: definedArgSyms(depth)
        Tree((depth, syms,
              Some(createConstantsRaw(rs.name + "_local",
                                      0 until clause.localSymbols.size))),
             for (c <- children) yield dag2Tree(d drop c, depth + c))
      } else {
        Leaf((depth, syms, None))
      }
    }

    var partialTree = dag2Tree(clauseDag, 0)

    // assert the clause constraints so far

    def assertClause(t : SpanTree) = {
      val Tree((dagIndex, rsArgs, Some(newLocalSyms)), subTrees) =
        t
      val clause@NormClause(constraint, _, _) =
        clauseDag(dagIndex)
      val oldSyms =
        clause.localSymbols.iterator ++ clause.headSyms.iterator ++ (
          for (cs <- clause.bodySyms.iterator; c <- cs.iterator) yield c)
      val newSyms =
        newLocalSyms.iterator ++ rsArgs.iterator ++ (
          for (Tree((_, cs, _), _) <- subTrees.iterator; c <- cs.iterator) yield c)
      val subst = ConstantSubst((oldSyms zip newSyms).toMap, p.order)
      addAssertion(subst(constraint))
    }

    for (t@Tree((_, _, Some(_)), _) <- partialTree.subtrees.iterator)
      assertClause(t)

    var didRefinement = true
    while (didRefinement && ??? == ProverStatus.Sat) {
      // search for leafs where the tree could be refined
      lazabs.GlobalParameters.get.timeoutChecker()

      didRefinement = false

      // we simply store the first relation argument to remember at which
      // point we want to refine
      val refinementPoints = new MHashSet[ConstantTerm]
      val refinementDagIndexes = new MHashSet[Int]

      def findRefinements(t : SpanTree,
                          incomingClause : NormClause,
                          clauseBodyIndex : Int) : Unit = t match {
        case Leaf(dagIndex, syms, None) =>
          // check whether the values of the argument symbols
          // are genuine

          if (!(refinementDagIndexes contains dagIndex) &&
              !(definedArgSyms(dagIndex) exists {
                  case defSyms =>
                    incomingClause.relevantBodySyms(clauseBodyIndex) forall {
                      case j => eval(syms(j)) == eval(defSyms(j))
                    }
                })) {
            // found a point to refine
            refinementDagIndexes += dagIndex
            refinementPoints += syms.head
          }

        case Tree(d@(dagIndex, _, _), children) => {
          val clause = clauseDag(dagIndex)
          for ((s, i) <- children.iterator.zipWithIndex)
            findRefinements(s, clause, i)
        }
      }

      def refine(t : SpanTree) : SpanTree = t match {
        case Leaf(dagIndex, syms, None)
          if (!syms.isEmpty && (refinementPoints contains syms.head)) => {
          // a point to refine

          val d@DagNode(clause@NormClause(_, _, (rs, _)), children, _) =
            clauseDag drop dagIndex
          val newT =
            Tree((dagIndex, syms,
                  Some(createConstantsRaw(rs.name + "_local",
                                          0 until clause.localSymbols.size))),
                 for (c <- children) yield dag2Tree(d drop c, dagIndex + c))

          for (t@Tree((_, _, Some(_)), _) <- newT.subtrees.iterator)
            assertClause(t)
          newT
        }
        case Tree(d, children) => {
          val newChildren = for (s <- children) yield refine(s)
          if ((children.iterator zip newChildren.iterator) forall {
                case (c1, c2) => c1 eq c2
              })
            // nothing changed
            t
          else
            Tree(d, newChildren)
        }
      }

      findRefinements(partialTree, null, 0)

      if (!refinementPoints.isEmpty) {
        if (lazabs.GlobalParameters.get.log)
          print(".")
        didRefinement = true
        partialTree = refine(partialTree)
      }
    }

    implicit val o = order
    ??? match {
      case ProverStatus.Unsat =>
        // found a solvable clause tree
        Left(for (t <- partialTree) yield t match {
          case (dagIndex, _, Some(_)) =>
            Left(clauseDag(dagIndex))
          case (dagIndex, _, None) => {
            val NormClause(_, _, (rs, _)) = clauseDag(dagIndex)
            Right(rs)
          }
        })
      case ProverStatus.Sat => {
        // found a genuine counterexample,
        // build a minimal counterexample dag

        def cexAtom(dagIndex : Int, syms : Seq[ConstantTerm]) : IAtom = {
          val NormClause(_, _, (RelationSymbol(pred), _)) = clauseDag(dagIndex)
          IAtom(pred, for (c <- syms) yield evalToTerm(c))
        }

        val cexNodes = partialTree.subtrees.toSeq sortWith {
          case (Tree((c, _, _), _), Tree((d, _, _), _)) => c > d
        }

        val fullDag = (DagEmpty.asInstanceOf[Dag[(IAtom, NormClause)]] /: cexNodes) {
          case (dag, Tree((_, _, None), _)) =>
            // disconnected node, which can be ignored at this point
            dag
          case (dag, Tree((dagIndex, syms, _), children)) => {
            val clause = clauseDag(dagIndex)
            val bodyAtoms = for (t <- children) yield {
              val Tree((tIndex, tSyms, _), _) = t
              cexAtom(tIndex, tSyms)
            }
            val dagChildren =
              (for ((ba, relevantSyms) <-
                    bodyAtoms.iterator zip clause.relevantBodySyms.iterator) yield {
                 (for (((ba2, _), i) <- dag.iterator.zipWithIndex;
                       if (ba.pred == ba2.pred &&
                           (relevantSyms forall { j => ba(j) == ba2(j) })))
                  yield (i + 1)).toSeq.last
               }).toList
            DagNode((cexAtom(dagIndex, syms), clause), dagChildren, dag)
          }
        }

        Right(fullDag.elimUnconnectedNodes)
      }
    }
  }
}
