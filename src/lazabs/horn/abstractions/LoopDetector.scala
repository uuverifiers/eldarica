/**
 * Copyright (c) 2011-2017 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.abstractions

import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.TemplateInterpolator.{AbstractionRecord,
                                                  AbstractionMap}
import lazabs.horn.preprocessor.HornPreprocessor

import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.basetypes.IdealInt
import ap.parser._
import ap.util.LRUCache

import scala.collection.mutable.{LinkedHashSet, ArrayBuffer,
                                 HashMap => MHashMap, HashSet => MHashSet}

/**
 * Compute loops and loop heads of the given set of clauses,
 * using a generalised version of the dominator relation.
 */
class LoopDetector(clauses : Seq[HornClauses.Clause]) {

  import IExpression._
  import HornClauses.Clause

  Console.err.println(
         "------------------------------ Analysing loops ---------------------------------")

  val allPredicates = new LinkedHashSet[Predicate]

  {
    var oldSize = -1
    while (oldSize != allPredicates.size) {
      oldSize = allPredicates.size
      for (Clause(IAtom(headP, _), body, _) <- clauses)
        if (body forall { case IAtom(p, _) => allPredicates contains p })
          allPredicates += headP
    }
  }

  val reachableClauses =
    for (clause@Clause(_, body, _) <- clauses;
         if (body forall { case IAtom(p, _) => allPredicates contains p }))
    yield clause

  val clausesWithHead =
    reachableClauses groupBy { case Clause(IAtom(p, _), _, _) => p }

  val dominators = {
    val domCandidates = new MHashMap[Predicate, Set[Predicate]]
    val allPredSet = allPredicates.toSet
    for (p <- allPredicates)
      domCandidates.put(p, allPredSet)

    val body2head =
      ((for (Clause(IAtom(head, _), body, _) <- reachableClauses;
                    IAtom(b, _) <- body)
        yield (b, head)) groupBy (_._1)) mapValues (_ map (_._2))

    val workqueue = new LinkedHashSet[Predicate]
    for (Clause(IAtom(head, _), Seq(), _) <- reachableClauses.iterator)
      workqueue += head

    while (!workqueue.isEmpty) {
      lazabs.GlobalParameters.get.timeoutChecker()

      val p = workqueue.head
      workqueue -= p

      val pClauses = clausesWithHead(p)

      val oldSet = domCandidates(p)
      val newSet =
        (for (Clause(_, body, _) <- pClauses.iterator) yield {
           (Set(p) /: (for (IAtom(q, _) <- body.iterator)
                       yield domCandidates(q))) (_ ++ _)
         }) reduce (_ & _)

      if (newSet.size < oldSet.size) {
        domCandidates.put(p, newSet)
        workqueue ++= body2head.getOrElse(p, List())
      }
    }

    domCandidates.toMap
  }

  def dominates(p : Predicate, q : Predicate) = dominators(q) contains p

  val loopHeads =
    (for (clause@Clause(IAtom(p, _), body, _) <- reachableClauses.iterator;
          if (body exists { case IAtom(q, _) => dominates(p, q) }))
     yield p).toSet

  val loopBodies =
    (for (head <- loopHeads.iterator) yield {
       val bodyPreds = new MHashSet[Predicate]
       bodyPreds += head

       var oldSize = 0
       while (bodyPreds.size != oldSize) {
         oldSize = bodyPreds.size
         for (Clause(IAtom(p, _), body, _) <- reachableClauses.iterator;
              if (bodyPreds contains p);
              IAtom(q, _) <- body.iterator;
              if (dominates(head, q)))
           bodyPreds += q
       }

       (head,
        for (clause@Clause(IAtom(p, _), body, _) <- reachableClauses;
             if ((bodyPreds contains p) &&
                 (body exists { case IAtom(q, _) => bodyPreds contains q })))
        yield clause)
     }).toMap

  val bodyPredicates =
    (for (h <- loopHeads.iterator)
     yield (h, (for (Clause(IAtom(p, _), _, _) <- loopBodies(h).iterator)
                yield p).toList)).toMap

  //////////////////////////////////////////////////////////////////////////////

  import HornPreprocessor.{VerificationHints, VerifHintTplElement,
                           VerifHintTplPred, VerifHintTplPredPosNeg,
                           VerifHintTplEqTerm, VerifHintTplInEqTerm,
                           VerifHintTplInEqTermPosNeg,
                           VerifHintTplIterationThreshold}

  def hints2AbstractionRecord(allHints : VerificationHints) : AbstractionMap =
    (for (head <- loopHeads.iterator;
          maybeHints = allHints.predicateHints get head;
          if maybeHints.isDefined;
          hints = maybeHints.get;
          if (hints exists {
            case _ : VerifHintTplElement => true
            case _ => false
          })) yield {
       val preds = new ArrayBuffer[(IFormula, Int)]
       val terms = new ArrayBuffer[(ITerm, Int)]
       val ineqs = new ArrayBuffer[(ITerm, Int)]
       var iterationThreshold : Option[Int] = None

       for (hint <- hints) hint match {
         case VerifHintTplPred(f, cost) =>
           preds += ((~f, cost))
         case VerifHintTplPredPosNeg(f, cost) => {
           preds += ((f, cost))
           preds += ((~f, cost))
         }
         case VerifHintTplEqTerm(t, cost) =>
           terms += ((t, cost))
         case VerifHintTplInEqTerm(t, cost) =>
           ineqs += ((t, cost))
         case VerifHintTplInEqTermPosNeg(t, cost) => {
           ineqs += ((t, cost))
           ineqs += ((-t, cost))
         }
         case VerifHintTplIterationThreshold(thre) =>
           iterationThreshold = Some(thre)
         case _ =>
           // nothing
       }

       val lattices : List[AbsLattice] =
         (if (preds.isEmpty) List() else List(PredicateLattice(preds))) ++
         (if (terms.isEmpty) List() else List(TermSubsetLattice(terms))) ++
         (if (ineqs.isEmpty) List() else List(TermIneqLattice(ineqs)))

       val latt = lattices reduceLeft (ProductLattice(_, _, true))

       head -> (new AbstractionRecord {
         val loopBody : Set[Predicate] = bodyPredicates(head).toSet
         val lattice : AbsLattice = latt
         val loopIterationAbstractionThreshold : Int =
           iterationThreshold getOrElse 3
       })
     }).toMap

  /*
  Not used, probably bad idea:

  SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>
    import p._
  
    for (clause@Clause(IAtom(headP, headArgs), body, constraint) <- clauses) scope {
      println(clause)

      addConstants(clause.constants)
      !! (constraint)

      if (??? == ProverStatus.Sat) {

        val argNums =
          (for ((t, i) <- headArgs.iterator.zipWithIndex) yield {
             push
             !! (t === i)

             if (??? == ProverStatus.Sat) {
               Some(i)
             } else {
               pop
               None
             }
           }).toList

        for (Some(_) <- argNums) pop

      } else {

        println("unsatisfiable constraint")

      }
    }

  }
  */

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Abstract domains to represent information about relation variables
 */
abstract class AbstractDomain {

  import HornClauses.Clause

  type Element

  def top(arity : Int)    : Element
  def bottom(arity : Int) : Element
  def initial(arity : Int) : Element

  def join(a : Element, b : Element) : Element
  def post(clause : Clause, inputs : Seq[Element]) : Element

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Identity domain: for each argument of a relation variable, just remember
 * whether the value of the argument is equal to some initial argument value.
 */
object IdentityDomain extends AbstractDomain {

  import HornClauses.Clause

  type Element = Option[List[Int]]

  def top(arity : Int)    : Element =
    Some((for (_ <- 0 until arity) yield -1).toList)
  def bottom(arity : Int) : Element =
    None
  def initial(arity : Int) : Element =
    Some((0 until arity).toList)

  def join(a : Element, b : Element) : Element = (a, b) match {
    case (None, x) => x
    case (x, None) => x
    case (Some(a), Some(b)) =>
      Some((for ((x, y) <- a.iterator zip b.iterator) yield {
              if (x < 0 || y < 0)
                -1
              else if (x == y)
                x
              else
                -1
            }).toList)
  }
  
  def post(clause : Clause, inputs : Seq[Element]) : Element = {
    val Clause(IAtom(_, headArgs), body, _) = clause
    assert(inputs.size == body.size)

    if (inputs contains None) {
      None
    } else {
      val knownValues = new MHashMap[ITerm, Int]

      for ((IAtom(_, formalArgs), Some(values)) <-
             body.iterator zip inputs.iterator;
           (t, v) <- formalArgs.iterator zip values.iterator)
        if (v >= 0)
          knownValues.put(t, v)

      Some((for (t <- headArgs.iterator)
            yield knownValues.getOrElse(t, -1)).toList)
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Stride domain: for each argument of a relation variable, remember
 * whether the value of the argument is equal to some initial argument
 * value plus some offset.
 */
class StrideDomain(sizeBound : Int, p : SimpleAPI)
      extends AbstractDomain {

  import HornClauses.Clause

  type Element = List[Option[Set[(Int, IdealInt)]]]

  def top(arity : Int)    : Element =
    (for (_ <- 0 until arity) yield None).toList
  def bottom(arity : Int) : Element =
    (for (_ <- 0 until arity) yield Some(Set[(Int, IdealInt)]())).toList
  def initial(arity : Int) : Element =
    (for (i <- 0 until arity) yield Some(Set((i, IdealInt.ZERO)))).toList

  def canonise(a : Element) : Element =
    if (a contains ((p : Option[Set[(Int, IdealInt)]]) => p match {
                      case Some(s) => s.isEmpty
                      case None => false
                    }))
      bottom(a.size)
    else
      for (s <- a) yield s match {
        case x@Some(t) if (t.size <= sizeBound) => x
        case _ => None
      }

  def join(a : Element, b : Element) : Element =
    canonise((for ((x, y) <- a.iterator zip b.iterator)
              yield (for (s <- x; t <- y) yield (s ++ t))).toList)

  // For each argument of the head of a clause, the following cache
  // contains a list of body arguments that are connected
  // (modulo some constant offset)
  private val clauseOffsets =
    new LRUCache[Clause, Option[List[List[(Int, IdealInt)]]]](10000)

  // Indexes of the offsets (stored in the above cache)
  // that were chosen in the post operation. This map is maintained
  // to prevent cycles
  private val chosenOffsetIndex =
    new MHashMap[Clause, List[Option[Int]]]

//  p setMostGeneralConstraints true

  private def checkWithTO = {
    import p._
    checkSat(false)
    while (getStatus(100) == ProverStatus.Running)
      lazabs.GlobalParameters.get.timeoutChecker()
    ???
  }

  def post(clause : Clause, inputs : Seq[Element]) : Element = {
    val Clause(IAtom(_, headArgs), body, constraint) = clause
    assert(inputs.size == body.size)

    val offsets = clauseOffsets(clause) { try {
      lazabs.GlobalParameters.get.timeoutChecker()

      import p._
      scope {
        
        addConstantsRaw(clause.constants)

        !! (constraint)

        if (checkWithTO == ProverStatus.Unsat) {
          None
        } else {
          val constraintConsts = SymbolCollector constants constraint

          val offsetCandidates : Array[List[(Int, ITerm, IdealInt)]] =
            (for (headArg <- headArgs) yield {
               val headVal = eval(headArg)
               var num = 0
               (for (IAtom(_, b) <- body.iterator;
                     bodyArg <- b.iterator;
                     if ({
                            num = num + 1
                            (headArg, bodyArg) match {
                              case (IConstant(c), IConstant(d)) =>
                                c == d ||
                                ((constraintConsts contains c) &&
                                 (constraintConsts contains d))
                              case _ => true
                            }
                          })) yield {
                  (num - 1, bodyArg, headVal - eval(bodyArg))
                }).toList
             }).toArray

          Some((for ((headArg, headArgNum) <- headArgs.iterator.zipWithIndex) yield {
            var res = List[(Int, IdealInt)]()
            while (!offsetCandidates(headArgNum).isEmpty) {
              lazabs.GlobalParameters.get.timeoutChecker()

              val (bodyArgNum, bodyArg, offset) = offsetCandidates(headArgNum).head
              offsetCandidates(headArgNum) = offsetCandidates(headArgNum).tail
              scope {
                ?? (headArg === bodyArg + offset)
                checkWithTO match {
                  case ProverStatus.Valid =>
                    res = (bodyArgNum, offset) :: res
                  case _ =>
                    // use the new model to rule out other offset candidates
                    for (i <- headArgNum until headArgs.size)
                      for (headVal <- evalPartial(headArgs(i)))
                        offsetCandidates(i) =
                          for(t@(_, bodyArg, offset) <- offsetCandidates(i);
                              if (evalPartial(bodyArg) match {
                                    case Some(bodyVal) => headVal == bodyVal + offset
                                    case None => true
                                  })) yield t
                }
              }
            }
            res
          }).toList)
        }
      }
    } catch {
      case SimpleAPI.NoModelException => {
        Console.err.println("Warning: could not fully compute clause offsets, probably due to quantifiers")
        None
      }
    }}

    if (offsets.isDefined) {
      val allInputs = inputs.flatten

      val newChosenOffsetIndex = for (offset <- offsets.get) yield {
        if (offset.isEmpty)
          None
        else
          Some((offset.iterator.zipWithIndex minBy {
                  case ((inp, _), _) => allInputs(inp) match {
                    case Some(s) => s.size
                    case None => Int.MaxValue
                  }
                })._2)
      }

      val finalChosenOffsetIndex = (chosenOffsetIndex get clause) match {
        case Some(oldChosen) =>
          // take the minimum of the new and the previously chosen
          // indexes, to prevent looping
          (for ((n, o) <- oldChosen.iterator zip newChosenOffsetIndex.iterator)
           yield (for (n2 <- n; o2 <- o) yield (n2 min o2))).toList
        case None =>
          newChosenOffsetIndex
      }

      chosenOffsetIndex.put(clause, finalChosenOffsetIndex)

      (for ((offset, chosenIndex) <-
              offsets.get.iterator zip finalChosenOffsetIndex.iterator) yield {
         for (index <- chosenIndex;
              (bestInput, bestOffset) = offset(index);
              s <- allInputs(bestInput)) yield {
           for ((x, y) <- s) yield (x, y + bestOffset)
         }
       }).toList
    } else {
      bottom(headArgs.size)
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

object ModifiedLoopVarsDetector {

  def simpleModifiedVars(loops : LoopDetector)
                        : Map[IExpression.Predicate, List[Int]] = {
    def detector = new ModifiedLoopVarsDetector(loops, IdentityDomain)
    for ((loopHead, abstractValue) <- detector.abstractValues) yield {
      val modifiedArgs =
        (for ((v, i) <- abstractValue.get.iterator.zipWithIndex;
              if (v < 0)) yield i).toList
      (loopHead, modifiedArgs)
    }
  }

  def varOffsets(loops : LoopDetector)
                : Map[IExpression.Predicate, List[List[IdealInt]]] =
    SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>
      val dom = new StrideDomain(3, p)
      val detector = new ModifiedLoopVarsDetector(loops, dom)

      for ((loopHead, abstractValue) <- detector.abstractValues) yield {
        val offsets =
          (for ((v, i) <- abstractValue.iterator.zipWithIndex) yield v match {
             case Some(l) => (for ((s, o) <- l; if (s == i)) yield o).toList.sorted
             case None => List[IdealInt]()
           }).toList
        (loopHead, offsets)
      }
    }

}

/**
 * Using a simple dataflow/AI analysis, over-approximate the set of
 * variables modified in each loop of a system of Horn clauses.
 */
class ModifiedLoopVarsDetector[Dom <: AbstractDomain]
                              (loops : LoopDetector, val domain : Dom) {

  import IExpression._
  import domain._
  import HornClauses.Clause

  val abstractValues : Map[Predicate, domain.Element] =
    for ((loopHead, clauses) <- loops.loopBodies) yield {
      val clausesWithHead =
        clauses groupBy { case Clause(IAtom(p, _), _, _) => p }
      val body2head =
        ((for (Clause(IAtom(head, _), body, _) <- clauses;
                      IAtom(b, _) <- body)
          yield (b, head)) groupBy (_._1)) mapValues (_ map (_._2))
      val abstractValues =
        new MHashMap[Predicate, Element].withDefault {
          p => if (clausesWithHead contains p) bottom(p.arity) else top(p.arity)
        }

      val initialAbstractValue = initial(loopHead.arity)

      val workqueue = new LinkedHashSet[Predicate]
      workqueue ++= clausesWithHead.keys

      while (!workqueue.isEmpty) {
        lazabs.GlobalParameters.get.timeoutChecker()

        val p = workqueue.head
        workqueue -= p

        val pClauses = clausesWithHead(p)
        val oldValue = abstractValues(p)
        val newValue =
          (bottom(p.arity) /:
           (for (clause@Clause(_, body, _) <- pClauses.iterator) yield {
              val inputs = for (IAtom(q, _) <- body) yield (
                if (q == loopHead)
                  initialAbstractValue
                else
                  abstractValues(q)
              )
              post(clause, inputs)
            })) (join _)
  
        if (newValue != oldValue) {
          abstractValues.put(p, newValue)
          workqueue ++= body2head.getOrElse(p, List())
        }
      }
  
      (loopHead, abstractValues(loopHead))
    }

}

////////////////////////////////////////////////////////////////////////////////

object StaticAbstractionBuilder {
  object AbstractionType extends Enumeration {
    val Empty, Term, Octagon, RelationalEqs, RelationalIneqs = Value
  }
}

class StaticAbstractionBuilder(clauses : Seq[HornClauses.Clause],
                               abstractionType : StaticAbstractionBuilder.AbstractionType.Value) {

  import IExpression._
  import HornClauses.Clause

  val loopDetector = new LoopDetector(clauses)

  Console.err.println("Loop heads:")

  //////////////////////////////////////////////////////////////////////////////

  def octagonAbstractions =
    for ((loopHead, modifiedArgs) <-
           ModifiedLoopVarsDetector.simpleModifiedVars(loopDetector)) yield {
      val unmodArgsCosts =
        for (k <- 0 until loopHead.arity;
             if (!(modifiedArgs contains k))) yield (v(k) -> 1)
      val modArgsCosts =
        for (k <- modifiedArgs) yield (v(k) -> 6)

      val (diffCosts, sumCosts) =
        if (modifiedArgs.isEmpty) {
          (List(), List())
        } else {
          val modHead = modifiedArgs.head
          val diffCosts = (for (k <- modifiedArgs.iterator;
                                if (k != modHead)) yield ((v(modHead) - v(k)) -> 2)).toList
          val sumCosts =  (for (k <- modifiedArgs.iterator;
                                if (k != modHead)) yield ((v(modHead) + v(k)) -> 7)).toList
          (diffCosts, sumCosts)
        }

/*
      val diffCosts =
        (for ((k1, i1) <- modifiedArgs.iterator.zipWithIndex;
              (k2, i2) <- modifiedArgs.iterator.zipWithIndex;
              if (i1 < i2)) yield ((v(k1) - v(k2)) -> 3)).toList
      val sumCosts =
        (for ((k1, i1) <- modifiedArgs.iterator.zipWithIndex;
              (k2, i2) <- modifiedArgs.iterator.zipWithIndex;
              if (i1 < i2)) yield ((v(k1) + v(k2)) -> 10)).toList
*/

      Console.err.println("   " + loopHead +
              " (" + loopDetector.loopBodies(loopHead).size + " clauses, " +
              (unmodArgsCosts.size + modArgsCosts.size + diffCosts.size + sumCosts.size) + " templates)")

      (loopHead,
       (loopDetector bodyPredicates loopHead,
        TermSubsetLattice(unmodArgsCosts ++ modArgsCosts ++ diffCosts ++ sumCosts,
                          loopHead.name)))
    }

  //////////////////////////////////////////////////////////////////////////////

  def termAbstractions =
    for ((loopHead, argOffsets) <-
           ModifiedLoopVarsDetector.varOffsets(loopDetector)) yield {
      val counterArgs =
        (for ((v, k) <- argOffsets.iterator.zipWithIndex;
              if (v == List(IdealInt.ONE))) yield k).toList
      val modifiedArgs =
        (for ((v, k) <- argOffsets.iterator.zipWithIndex;
              if (v != List(IdealInt.ZERO))) yield k).toList

      val unmodArgsCosts =
        for (k <- 0 until loopHead.arity;
             if (!(modifiedArgs contains k))) yield (v(k) -> 1)
      val modArgsCosts =
        for (k <- 0 until loopHead.arity;
             if ((modifiedArgs contains k) &&
                 !(counterArgs contains k))) yield (v(k) -> 4)
      val counterArgsCosts =
        for (k <- counterArgs) yield (v(k) -> 9)

      Console.err.println("   " + loopHead +
              " (" + loopDetector.loopBodies(loopHead).size + " clauses, " +
              (unmodArgsCosts.size + modArgsCosts.size + counterArgsCosts.size) + " templates)")

      (loopHead,
       (loopDetector bodyPredicates loopHead,
        TermSubsetLattice(unmodArgsCosts ++ modArgsCosts ++ counterArgsCosts,
                          loopHead.name)))
    }

  //////////////////////////////////////////////////////////////////////////////

  def emptyAbstractions =
    for ((head, _) <- loopDetector.loopBodies) yield {
      Console.err.println("   " + head +
              " (" + loopDetector.loopBodies(head).size + " clauses)")
      // just create some unit lattice (with exactly one element)
      (head,
       (loopDetector bodyPredicates head,
        TermSubsetLattice(List()).asInstanceOf[AbsLattice]))
    }

  //////////////////////////////////////////////////////////////////////////////

  def relationAbstractions(ineqs : Boolean) =
    for ((loopHead, argOffsets) <-
           ModifiedLoopVarsDetector.varOffsets(loopDetector)) yield {
      val modifiedArgs =
        (for ((v, k) <- argOffsets.iterator.zipWithIndex;
              if (v != List(IdealInt.ZERO))) yield k).toList

      val unmodArgsCosts =
        for (k <- 0 until loopHead.arity;
             if (!(modifiedArgs contains k))) yield (v(k) -> 1)
      val modArgsCosts =
        for (k <- modifiedArgs) yield (v(k) -> 6)

      val counter = (
         for ((List(o), k) <- argOffsets.iterator.zipWithIndex;
              if (o.isUnit)) yield k).toSeq.headOption              orElse (
         for ((l, k) <- argOffsets.iterator.zipWithIndex;
              if (l exists (_.isUnit))) yield k).toSeq.headOption   orElse (
         modifiedArgs.headOption)

      val offsetDiffCosts = counter match {
        case Some(counterInd) =>
          (for (o1 <- argOffsets(counterInd).iterator;
                if (!o1.isZero);
                (l2, i2) <- argOffsets.iterator.zipWithIndex;
                if (i2 != counterInd);
                o2 <- (if (l2.isEmpty)
                         List(IdealInt.ONE, IdealInt.MINUS_ONE)
                       else
                         l2).iterator;
                if (!o2.isZero);
                (op1, op2) = if (o2.signum >= 0) (o1, o2) else (-o1, -o2))
           yield ((v(counterInd)*op2 - v(i2)*op1) -> 2)).toList.distinct
        case None =>
          List()
      }

/*
      val offsetDiffCosts =
        (for ((l1, i1) <- argOffsets.iterator.zipWithIndex;
              o1 <- l1.iterator;
              if (!o1.isZero);
              (l2, i2) <- argOffsets.iterator.zipWithIndex;
              o2 <- l2.iterator;
              if (!o2.isZero /* && !(o1.isUnit && o2.isUnit) */ && i1 < i2))
         yield ((v(i1)*o2 - v(i2)*o1) -> 2)).toList */

      Console.err.println("   " + loopHead +
              " (" + loopDetector.loopBodies(loopHead).size + " clauses, " +
              (unmodArgsCosts.size + modArgsCosts.size + // diffCosts.size +
               offsetDiffCosts.size /* + sumCosts.size */) + " templates)")

      val allCosts = unmodArgsCosts ++ modArgsCosts /* ++ diffCosts ++ sumCosts */ ++ offsetDiffCosts

      (loopHead,
       (loopDetector bodyPredicates loopHead,
        if (ineqs)
          TermIneqLattice(for ((t, c) <- allCosts; s <- List(t, -t)) yield (s, c),
                          loopHead.name)
        else
          TermSubsetLattice(allCosts, loopHead.name)
       ))
    }

  //////////////////////////////////////////////////////////////////////////////

  import StaticAbstractionBuilder._

  val abstractions : Map[Predicate, (Seq[Predicate], AbsLattice)] =
    abstractionType match {
      case AbstractionType.Empty =>
        emptyAbstractions
      case AbstractionType.Term =>
        termAbstractions
      case AbstractionType.Octagon =>
        octagonAbstractions
      case AbstractionType.RelationalEqs =>
        relationAbstractions(false)
      case AbstractionType.RelationalIneqs =>
        relationAbstractions(true)
    }

}
