/**
 * Copyright (c) 2021 Philipp Ruemmer. All rights reserved.
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

import ap.SimpleAPI
import ap.basetypes.IdealInt
import ap.parser._
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction
import SimpleAPI.ProverStatus

import Util._
import DisjInterpolator.{AndOrNode, AndNode, OrNode}
import lazabs.horn.abstractions.{VerificationHints, EmptyVerificationHints,
                                 AbsReader}
import VerificationHints._
import lazabs.horn.concurrency.ReaderMain

import lattopt._

import scala.collection.mutable.{ArrayBuffer, LinkedHashSet, LinkedHashMap,
                                 HashMap => MHashMap}

object PredicateMiner {
  object TemplateExtraction extends Enumeration {
    val Variables, UnitTwoVariables = Value
  }

  private val EqVarCost       = 8
  private val InEqVarCost     = 7
  private val EqVarDiffCost   = 5
  private val EqVarSumCost    = 6
  private val InEqVarDiffCost = 3
  private val InEqVarSumCost  = 4

}

/**
 * A class to analyse the predicates generated during a CEGAR run.
 */
class PredicateMiner[CC <% HornClauses.ConstraintClause]
                    (predAbs : HornPredAbs[CC]) {

  import PredicateMiner._
  import predAbs.{context, predStore}

  /**
   * All predicates that have been considered by CEGAR.
   */
  val allPredicates =
    for ((rs, preds) <- predStore.predicates.toIndexedSeq;
         pred <- preds.toIndexedSeq)
    yield pred

  private def conjSize(c : Conjunction) : Int = {
    c.quans.size +
      (for (lc <- c.arithConj.positiveEqs ++
                  c.arithConj.negativeEqs ++
                  c.arithConj.inEqs) yield lc.size).sum +
    c.predConj.size +
    (for (d <- c.negatedConjs) yield conjSize(d)).sum
  }

  private val allPredsWithSize =
    for (pred <- allPredicates) yield (pred, conjSize(pred.posInstances.head))

  /**
   * A lattice representing all sufficient subsets of predicates.
   */
  val predicateLattice =
    CachedFilteredLattice(PowerSetLattice.invertedWithCosts(allPredsWithSize),
                          isSufficient)

  def printPreds(preds : Seq[RelationSymbolPred]) : Unit = {
    val rses = preds.map(_.rs).distinct.sortBy(_.name)
    for (rs <- rses) {
      println("" + rs + ":")
      for (pred <- preds)
        if (pred.rs == rs)
          println("\t" + pred)
    }
  }

  private implicit val randomData = new SeededRandomDataSource(123)

  /**
   * An arbitrary minimal sufficient set of predicates.
   */
  lazy val minimalPredicateSet =
    allPredicates filter predicateLattice.getLabel(
      Algorithms.maximize(predicateLattice)(predicateLattice.bottom))

  /**
   * All sufficient sets of predicates that are minimal in terms of the
   * total size of the predicates.
   */
  lazy val minimalSizePredicateSets =
    for (s <- Algorithms.optimalFeasibleObjects(predicateLattice)(
                                                predicateLattice.bottom))
    yield (allPredicates filter predicateLattice.getLabel(s))

  /**
   * Union of all predicates in <code>minimalSizePredicateSets</code>.
   */
  lazy val minimalSizePredicateUnion = {
    val s = (for (s <- minimalSizePredicateSets; p <- s) yield p).toSet
    allPredicates filter s
  }

  /**
   * The necessary predicates: predicates which are contained in each
   * minimal sufficient set.
   */
  lazy val necessaryPredicates = necessaryPredicates2Help

  /**
   * The non-redundant predicates: the union of all minimal sufficient
   * predicate sets.
   */
  lazy val nonRedundantPredicates =
    if (minimalPredicateSet == necessaryPredicates)
      minimalPredicateSet
    else
      allPredicates filter predicateLattice.getLabel(
        Algorithms.maximalFeasibleObjectMeet(predicateLattice)(predicateLattice.bottom))

  /**
   * Templates consisting of upper and lower bounds of individual variables.
   */
  lazy val variableTemplates =
    extractTemplates(TemplateExtraction.Variables)

  /**
   * Templates consisting of upper and lower bounds of unit-two-variable terms.
   */
  lazy val unitTwoVariableTemplates =
    extractTemplates(TemplateExtraction.UnitTwoVariables)

  //////////////////////////////////////////////////////////////////////////////

  {
    implicit val randomData = new SeededRandomDataSource(123)
    val pl = predicateLattice

    println("All predicates (" + allPredicates.size + "):")
    printPreds(allPredicates)

    println
    println("Minimal predicate set (" + minimalPredicateSet.size + "):")
    printPreds(minimalPredicateSet)

    for (s <- minimalSizePredicateSets) {
      println
      println("Minimal size predicate set (" + s.size + "):")
      printPreds(s)
    }

    println
    println("Necessary predicates, contained in all minimal sufficient sets (" +
              necessaryPredicates.size + "):")
    printPreds(necessaryPredicates)

    println
    println("Non-redundant predicates, contained in some minimal sufficient set (" +
              nonRedundantPredicates.size + "):")
    printPreds(nonRedundantPredicates)

    println
    println("Template consisting of individual variables:")
    ReaderMain.printHints(variableTemplates)

    println
    AbsReader.printHints(variableTemplates)

    println
    println("Unit-two-variable templates:")
    ReaderMain.printHints(unitTwoVariableTemplates)

    println
    AbsReader.printHints(unitTwoVariableTemplates)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Find a minimal sub-set of the given predicates that is sufficient
   * to show satisfiability of the problem. The method will try to
   * remove the first predicates in the sequence first.
   */
  protected def minimizePredSet(preds : Seq[RelationSymbolPred])
                              : Seq[RelationSymbolPred] = {
    var curPredicates = preds.toSet

    for (pred <- preds) {
      val testPreds = curPredicates - pred
      if (isSufficient(testPreds))
        curPredicates = testPreds
    }

    preds filter curPredicates
  }

  /**
   * Find the predicates within the given set of predicates that are
   * elements of every minimal sufficient set of predicates.
   */
  protected def necessaryPredicatesHelp(preds : Seq[RelationSymbolPred])
                                      : Seq[RelationSymbolPred] = {
    val result = new ArrayBuffer[RelationSymbolPred]
    val allPreds = preds.toSet

    for (pred <- preds) {
      if (!isSufficient(allPreds - pred))
        result += pred
    }

    result.toSeq
  }

  /**
   * Find the predicates that are elements of every minimal sufficient
   * set of predicates.
   * 
   * This method will use the predicate lattice for the computation.
   */
  protected def necessaryPredicates2Help : Seq[RelationSymbolPred] = {
    val result = new ArrayBuffer[RelationSymbolPred]

    for (pred <- allPredicates) {
      val obj = (for (x <- predicateLattice succ predicateLattice.bottom;
                      if !(predicateLattice.getLabel(x) contains pred))
                 yield x).next
      if (!predicateLattice.isFeasible(obj))
        result += pred
    }

    result.toSeq
  }

  /**
   * Check whether the given set of predicates is sufficient to show
   * satisfiability of the problem.
   */
  def isSufficient(preds : Iterable[RelationSymbolPred]) : Boolean = {
    print(".")
    val newPredStore = new PredicateStore(context)
    newPredStore addRelationSymbolPreds preds
    try {
      Console.withOut(HornWrapper.NullStream) {
        new CEGAR (context, newPredStore, exceptionalPredGen)
      }
      true
    } catch {
      case PredGenException => {
        false
      }
    }
  }

  private object PredGenException extends Exception

  private def exceptionalPredGen(d : Dag[AndOrNode[NormClause, Unit]]) 
                               : Either[Seq[(Predicate, Seq[Conjunction])],
                                        Dag[(IAtom, NormClause)]] =
   throw PredGenException

  //////////////////////////////////////////////////////////////////////////////

  def extractTemplates(mode : TemplateExtraction.Value)
                     : VerificationHints =
    mergeTemplates(
      VerificationHints.union(
        (nonRedundantPredicates map {
           p => extractTemplates(p, mode,
                                 if (necessaryPredicates contains p)
                                   1
                                 else if (minimalSizePredicateUnion contains p)
                                   2
                                 else
                                   5)
         }) ++ List(defaultTemplates(context.relationSymbols.keys filterNot (
                                       _ == HornClauses.FALSE), 20))
      ))

  def defaultTemplates(preds : Iterable[Predicate],
                       cost : Int)
                     : VerificationHints = {
    val templates =
      (for (pred <- preds) yield {
         val sorts = HornPredAbs predArgumentSorts pred
         val els =
           for ((s, n) <- sorts.zipWithIndex)
           yield VerifHintTplEqTerm(IExpression.v(n, s), cost)
         pred -> els
       }).toMap

    VerificationHints(templates)
  }

  def extractTemplates(preds : Iterable[RelationSymbolPred],
                       mode : TemplateExtraction.Value,
                       costFactor : Int)
                     : VerificationHints =
    VerificationHints.union(
      preds map { p => extractTemplates(p, mode, costFactor) })

  def extractTemplates(pred : RelationSymbolPred,
                       mode : TemplateExtraction.Value,
                       costFactor : Int)
                     : VerificationHints = {
    import IExpression._

    mode match {
      case TemplateExtraction.Variables => {
        val rs =
          pred.rs
        val symMap =
          (for ((c, n) <- rs.arguments.head.iterator.zipWithIndex)
           yield (c -> v(n, Sort sortOf c))).toMap

        val res = new LinkedHashSet[VerifHintElement]

        def extractVars(c : Conjunction, polarity : Int) : Unit = {
          val ac = c.arithConj

          for (lc <- ac.positiveEqs ++ ac.negativeEqs; c <- lc.constants)
            res += VerifHintTplEqTerm(symMap(c), EqVarCost * costFactor)

          for (lc <- ac.inEqs.iterator;
               (coeff, c : ConstantTerm) <- lc.iterator) {
            val t = symMap(c) *** (coeff.signum * polarity)
            res += VerifHintTplInEqTerm(t, InEqVarCost * costFactor)
          }

          for (d <- c.negatedConjs) extractVars(d, -polarity)
        }

        extractVars(pred.posInstances.head, 1)

        VerificationHints(Map(rs.pred -> mergePosNegTemplates(res.toSeq)))
      }

      case TemplateExtraction.UnitTwoVariables => {
        val rs = pred.rs
        VerificationHints(Map(rs.pred ->
                                computeUTVTemplates(rs.arguments.head,
                                                    pred.posInstances.head,
                                                    costFactor)))
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def computeUTVTemplates(allConsts : Seq[IExpression.ConstantTerm],
                                  f : Conjunction,
                                  costFactor : Int) : Seq[VerifHintElement] = {
    import IExpression._
    val fConsts = f.constants

    val rawHints1 =
      for ((c, n) <- allConsts.zipWithIndex;
           if fConsts contains c;
           va = v(n, Sort sortOf c);
           h <- List(VerifHintTplEqTerm(va, EqVarCost * costFactor),
                     VerifHintTplInEqTerm(va, InEqVarCost * costFactor),
                     VerifHintTplInEqTerm(-va, InEqVarCost * costFactor)))
      yield h

    val baseConst =
      (for (c <- allConsts.iterator;
            if (Sort sortOf c) == Sort.Integer)
       yield c).toStream.headOption getOrElse allConsts.head
    val baseVar =
      v(allConsts indexOf baseConst, Sort sortOf baseConst)

    val rawHints2 =
      for (n <- 0 until allConsts.size;
           if fConsts contains allConsts(n);
           c = v(n, Sort sortOf allConsts(n));
           if c != baseVar;
           h <- List(VerifHintTplEqTerm(c + baseVar,
                                        EqVarSumCost * costFactor),
                     VerifHintTplEqTerm(c - baseVar,
                                        EqVarDiffCost * costFactor),
                     VerifHintTplInEqTerm(c + baseVar,
                                          InEqVarSumCost * costFactor),
                     VerifHintTplInEqTerm(c - baseVar,
                                          InEqVarDiffCost * costFactor),
                     VerifHintTplInEqTerm(-c - baseVar,
                                          InEqVarSumCost * costFactor),
                     VerifHintTplInEqTerm(baseVar - c,
                                          InEqVarDiffCost * costFactor)))
      yield h

    filterVerificationHints(f, allConsts, rawHints1 ++ rawHints2)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def filterVerificationHints(c : Conjunction,
                                      allConsts : Seq[IExpression.ConstantTerm],
                                      hints : Seq[VerifHintElement])
                                    : Seq[VerifHintElement] =
    SimpleAPI.withProver { p =>
      import p._
      import IExpression._

//      Algorithms.debug = true

//      println("Templates for " + c)
//      println("" + hints.size + " hints")

      val const2Var =
        (for ((c, n) <- allConsts.iterator.zipWithIndex)
         yield (c, v(n, Sort sortOf c))).toMap

      val hintWithFlags =
        for (h <- hints) yield (createBooleanVariable, h)

      def getCoeff(t : ITerm, c : ITerm) : IdealInt = {
        val IConstant(d) = c
        val Sum = SymbolSum(const2Var(d))
        t match {
          case Sum(coeff, _) => coeff
          case _ => 0
        }
      }

      def addConstraints(c : Conjunction, polarity : Int) : Unit = {
        val ac = c.arithConj

        for (lc <- ac.positiveEqs ++ ac.negativeEqs) {
          val baseCoeff =
            createConstant(Sort.Integer)
          !! (baseCoeff =/= 0)

          val hintCoeff =
            for ((f, h : VerifHintTplEqTerm) <- hintWithFlags) yield {
              val c = createConstant(Sort.Integer)
              !! (f | (c === 0))
              (h, c)
            }

          for ((coeff, c : ConstantTerm) <- lc.iterator) {
            val f = (baseCoeff * coeff ===
                  sum(for ((VerifHintTplEqTerm(t, _), d) <- hintCoeff) yield {
                        d *** getCoeff(t, c)
                      }))
            !! (f)
          }
        }

        for (lc <- ac.inEqs) {
          val baseCoeff =
            createConstant(Sort.Integer)
          !! (baseCoeff > 0)

          val hintCoeff =
            for ((f, h) <- hintWithFlags) yield h match {
              case VerifHintTplEqTerm(t, _) => {
                val c = createConstant(Sort.Integer)
                !! (f | (c === 0))
                (t, c)
              }
              case VerifHintTplInEqTerm(t, _) => {
                val c = createConstant(Sort.Nat)
                !! (f | (c === 0))
                (t, c)
              }
            }

          for ((coeff, c : ConstantTerm) <- lc.iterator) {
            val f = (baseCoeff * coeff * polarity ===
                  sum(for ((t, d) <- hintCoeff) yield {
                        d *** getCoeff(t, c)
                      }))
            !! (f)
          }
        }

        for (d <- c.negatedConjs) addConstraints(d, -polarity)
      }

      addConstraints(c, 1)

      ??? match {
        case ProverStatus.Unsat =>
          // we cannot filter out any hints, just take all of them
          hints

        case ProverStatus.Sat => {
          val flags =
            for ((f, h) <- hintWithFlags) yield h match {
              case h : VerifHintTplElement => (f, h.cost)
            }
          val hintLattice =
            CachedFilteredLattice(
              PowerSetLattice.invertedWithCosts(flags), {
                (flags : Set[IFormula]) => scope {
//                  print("-")
                  for ((f, _) <- hintWithFlags)
                    if (!(flags contains f))
                      !! (!f)
                  val r = ??? == ProverStatus.Sat
//                  print(".")
                  r
                }})

          val results =
            for (s <- Algorithms.optimalFeasibleObjects(hintLattice)(
                                                        hintLattice.bottom))
            yield (hintLattice getLabel s)

          if (results.size > 1) {
            Console.err.println("Warning: no unique optimal set of templates found")
            Console.err.println("  Results:")
            for (r <- results) {
              Console.err.println(
                "  " +
                  (for ((f, h) <- hintWithFlags; if r contains f) yield h))
            }
          }

//          println

          for ((f, h) <- hintWithFlags; if results.head contains f) yield h
        }
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  import IExpression._

  private def mergePosNegTemplates(hints : Seq[VerifHintElement])
                                 : Seq[VerifHintElement] = {
    val augmented =
      hints ++ (
        for (VerifHintTplInEqTerm(s, cost) <- hints;
             if (hints exists {
                   case VerifHintTplInEqTerm(t, _)
                       if equalMinusTerms(s,t) => true
                   case _ =>
                       false
                 }))
        yield VerifHintTplEqTerm(s, cost))

    filterNonRedundant(augmented)
  }

  private def filterNonRedundant(hints : Seq[VerifHintElement])
                               : Seq[VerifHintElement] = {
    val res = new ArrayBuffer[VerifHintElement]

    for (el@VerifHintTplEqTerm(s, cost) <- hints.iterator)
      if (!(res exists {
              case VerifHintTplEqTerm(t, _) =>
                equalTerms(s, t) || equalMinusTerms(s, t)
              case _ =>
                false
            }))
        res += el

    for (el@VerifHintTplInEqTerm(s, cost) <- hints.iterator)
      if (!(res exists {
              case VerifHintTplInEqTerm(t, _) =>
                equalTerms(s, t)
              case VerifHintTplEqTerm(t, _) =>
                equalTerms(s, t) || equalMinusTerms(s, t)
              case _ =>
                false
            }))
        res += el

    res.toSeq
  }

  private def mergeTemplates(hints : VerificationHints) : VerificationHints = {
    val newPredHints =
      (for ((pred, els) <- hints.predicateHints) yield {
         val sorted = els.sortBy {
           case el : VerifHintTplElement => el.cost
           case _ => Int.MinValue
         }

         val res = new ArrayBuffer[VerifHintElement]

         for (el <- sorted) el match {
           case VerifHintTplEqTerm(s, _) =>
             if (!(res exists {
                     case VerifHintTplEqTerm(t, _) =>
                       equalTerms(s, t) || equalMinusTerms(s, t)
                     case _ =>
                       false
                   }))
               res += el
           case VerifHintTplInEqTerm(s, _) =>
             if (!(res exists {
                     case VerifHintTplInEqTerm(t, _) =>
                       equalTerms(s, t)
                     case VerifHintTplEqTerm(t, _) =>
                       equalTerms(s, t) || equalMinusTerms(s, t)
                     case _ =>
                       false
                   }))
               res += el
         }

         pred -> res.toSeq
      }).toMap

    VerificationHints(newPredHints)
  }

  private def equalTerms(s : ITerm, t : ITerm) : Boolean = (s, t) match {
    case (s, t)
        if s == t => true
    case (Difference(s1, s2), Difference(t1, t2))
        if equalTerms(s1, t1) && equalTerms(s2, t2) => true
    case _ =>
        false
  }

  private def equalMinusTerms(s : ITerm, t : ITerm) : Boolean = (s, t) match {
    case (ITimes(IdealInt.MINUS_ONE, s), t)
        if equalTerms(s, t) => true
    case (s, ITimes(IdealInt.MINUS_ONE, t))
        if equalTerms(s, t) => true
    case (Difference(s1, s2), Difference(t1, t2))
        if equalTerms(s1, t2) && equalTerms(s2, t1) => true
    case _ =>
        false
  }

}
