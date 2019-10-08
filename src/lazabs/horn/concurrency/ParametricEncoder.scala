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

package lazabs.horn.concurrency

import ap.parser._
import ap.types.MonoSortedPredicate
import ap.util.{Seqs, Combinatorics}

import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.abstractions.{VerificationHints, EmptyVerificationHints}

import scala.collection.mutable.{LinkedHashSet, HashSet => MHashSet,
                                 ArrayBuffer, HashMap => MHashMap}

object ParametricEncoder {

  import Combinatorics._

  abstract sealed class Replication
  case object Singleton extends Replication
  case object Infinite  extends Replication

  abstract sealed class TimeSpec
  case object NoTime                                           extends TimeSpec
  case class  DiscreteTime(index : Int)                        extends TimeSpec
  case class  ContinuousTime(numIndex : Int, denomIndex : Int) extends TimeSpec

  type Process = Seq[(HornClauses.Clause, Synchronisation)]
  type ProcessSet = Seq[(Process, Replication)]

  def processPreds(processes : ProcessSet) : Set[IExpression.Predicate] =
    (for ((proc, _) <- processes.iterator;
          (c, _) <- proc.iterator;
          p <- c.predicates.iterator)
     yield p).toSet


  //////////////////////////////////////////////////////////////////////////////

  abstract sealed class Synchronisation
  case object NoSync                         extends Synchronisation
  case class  Send(chan : CommChannel)       extends Synchronisation
  case class  Receive(chan : CommChannel)    extends Synchronisation
  case class  BarrierSync(barrier : Barrier) extends Synchronisation

  class CommChannel(name : String) {
    override def toString = name
  }

  //////////////////////////////////////////////////////////////////////////////

  object Barrier {
    def unapply(b : Barrier) = Some(b.domains)
  }

  abstract sealed class Barrier(val name : String,
                                val domains : Seq[Set[IExpression.Predicate]]) {
    override def toString = name
  }

  class SimpleBarrier(_name : String,
                      _domains : Seq[Set[IExpression.Predicate]])
    extends Barrier(_name, _domains)

  /**
   * A family of barriers is specified like a simple barrier, but in
   * addition an equivalence relation has to be provided that describes
   * which processes can synchronise on the same barriers.
   */
  class BarrierFamily(_name : String,
                      _domains : Seq[Set[IExpression.Predicate]],
                      val equivalentProcesses :
                        (ITerm, ITerm, ITerm, ITerm) => IFormula)
    extends Barrier(_name, _domains)

  //////////////////////////////////////////////////////////////////////////////

  import VerificationHints._

  case class System(processes : ParametricEncoder.ProcessSet,
                    globalVarNum : Int,
                    backgroundAxioms : Option[Seq[ITerm] => IFormula],
                    timeSpec : ParametricEncoder.TimeSpec,
                    timeInvariants : Seq[HornClauses.Clause],
                    assertions : Seq[HornClauses.Clause],
                    hints : VerificationHints = EmptyVerificationHints) {

    import HornClauses.Clause
    import IExpression._

    val localPreds = for ((process, _) <- processes) yield {
      val preds = new LinkedHashSet[Predicate]
      for ((c, _) <- process)
        preds ++= c.predicates
      preds.toSeq
    }

    val allLocalPreds =
      (for (preds <- localPreds.iterator; p <- preds.iterator) yield p).toSet

    assert(hints.predicateHints.keys forall allLocalPreds)

    val globalVarSorts =
      predArgumentSorts(allLocalPreds.iterator.next) take globalVarNum

    val localPredsSet = for (preds <- localPreds) yield preds.toSet
  
    val processIndex =
      (for ((preds, i) <- localPreds.iterator.zipWithIndex;
            p <- preds.iterator)
       yield (p, i)).toMap

    // we assume that all processes use distinct sets of predicates
    {
      val allPreds = new MHashSet[Predicate]
      for (preds <- localPreds.iterator; p <- preds.iterator) {
        val b = allPreds add p
        assert(b)
      }
    }
  
    val localInitClauses =
      for ((process, _) <- processes) yield
        (for ((c@Clause(_, List(), _), NoSync) <- process.iterator)
         yield c).toList
  
    val localPredRanking =
      (for (preds <- localPreds.iterator; p <- preds.iterator)
       yield p).zipWithIndex.toMap

    val barriers = {
      val res = new LinkedHashSet[Barrier]
      for ((process, _) <- processes.iterator;
           (_, BarrierSync(b)) <- process.iterator)
        res += b
      res.toSeq
    }

    // barrier specifications have to be consistent with processes
    // in the system
    assert(barriers forall {
      case Barrier(doms) =>
        doms.size == processes.size &&
        ((0 until doms.size) forall { i => doms(i) subsetOf localPredsSet(i) })
    })

    // barrier synchronisation can only occur within the domain
    // of the barrier
    assert(processes forall { case (process, _) =>
           process forall {
             case (Clause(_, List(IAtom(pred, _)), _),
                   BarrierSync(Barrier(doms))) =>
               doms(processIndex(pred)) contains pred
             case _ => true
           }})

    ////////////////////////////////////////////////////////////////////////////

    /**
     * Create a finite instance of a parametric model,
     * by replacing infinite processes with a finite number of
     * singleton processes
     */
    def finitise(instanceNumbers : Seq[Option[Range]]) : System = {

      assert(instanceNumbers.size == processes.size &&
             ((instanceNumbers.iterator zip processes.iterator) forall {
                case (None, _)                => true
                case (Some(_), (_, Infinite)) => true
                case _                        => false
              }))

      val newPredicateHints =
        new MHashMap[IExpression.Predicate, Seq[VerifHintElement]]

      val predMappings =
        (for (((n, (process, _)), i) <-
                (instanceNumbers.iterator zip processes.iterator).zipWithIndex;
              j <- (n getOrElse (0 until 1)).iterator) yield {

           val mapping =
             (for (p <- localPreds(i).iterator) yield n match {
                case None =>
                  p -> p
                case _ =>
                  p -> MonoSortedPredicate(p.name + "_" + j,
                                           predArgumentSorts(p))
              }).toMap

           for ((a, b) <- mapping)
             (hints.predicateHints get a) match {
               case Some(preds) => newPredicateHints.put(b, preds)
               case None => // nothing
             }

           (mapping + (HornClauses.FALSE -> HornClauses.FALSE),
            i, for (_ <- n) yield j)
         }).toList

      def updateClause(clause : Clause,
                       mapping : Map[Predicate, Predicate],
                       id : Option[Int]) = {
        val Clause(head@IAtom(headP, headArgs), body, constraint) = clause
        val idConstraint : IFormula = id match {
          case None =>
            true
          case Some(id) =>
            (body ++ List(head)).head.args(globalVarNum) === id
        }
        Clause(IAtom(mapping(headP), headArgs),
               for (IAtom(p, a) <- body)
                 yield IAtom(mapping(p), a),
               constraint &&& idConstraint)
      }

      val barrierMapping =
        (for (b <- barriers.iterator) yield {
           val newDomains =
             for ((m, i, _) <- predMappings) yield (b.domains(i) map m)
           b match {
             case b : SimpleBarrier =>
               b -> new SimpleBarrier(b.name, newDomains)
             case b : BarrierFamily =>
               b -> new BarrierFamily(b.name, newDomains,
                                      b.equivalentProcesses)
           }
         }).toMap

      val newProcesses = for ((mapping, i, j) <- predMappings) yield {
        val (oriProcess, t) = processes(i)

        val newProcess =
          for ((clause, sync) <- oriProcess) yield {
          val newSync = sync match {
            case BarrierSync(b) => BarrierSync(barrierMapping(b))
            case s              => s
          }
          (updateClause(clause, mapping, j), newSync)
        }

        (newProcess, if (instanceNumbers(i).isDefined) Singleton else t)
      }

      val newTimeInvs =
        (for ((mapping, i, j) <- predMappings.iterator;
              clause@Clause(_, Seq(IAtom(p, _)), _) <- timeInvariants.iterator;
              if (mapping contains p))
         yield updateClause(clause, mapping, j)).toList

      val newAssertions =
        (for (Clause(head, body, constraint) <- assertions.iterator;
              allAtomsVec =
                for (IAtom(p, args) <- body) yield (
                   for ((m, _, _) <- predMappings;
                      if (m contains p)) yield IAtom(m(p), args));
              newBody <- cartesianProduct(allAtomsVec);
              if ((for (IAtom(p, _) <- newBody.iterator) yield p).toSet.size ==
                  body.size))
         yield (Clause(head, newBody, constraint))).toList

      val newSystem =
        System(newProcesses, globalVarNum, backgroundAxioms,
               timeSpec, newTimeInvs, newAssertions,
               VerificationHints(newPredicateHints.toMap))
      newSystem
    }

    ////////////////////////////////////////////////////////////////////////////

    /**
     * Produce a smaller equi-safe system my merging transitions that only
     * concern local variables.
     */
    def mergeLocalTransitions : System = {

      val predsToKeep, predsWithTimeInvs = new MHashSet[Predicate]
      for (c <- timeInvariants) {
        predsToKeep ++= c.predicates
        predsWithTimeInvs ++= c.predicates
      }
      for (c <- assertions)
        predsToKeep ++= c.predicates

      // also keep initial states
      for (clauses <- localInitClauses.iterator; c <- clauses.iterator)
        predsToKeep ++= c.predicates

      def isLocalClause(p : (Clause, Synchronisation)) =
        p._2 == NoSync &&
        p._1.body.size == 1 &&
        Seqs.disjoint(predsWithTimeInvs, p._1.predicates) && {
          val Clause(head@IAtom(_, headArgs),
                     body@List(IAtom(_, bodyArgs)),
                     constraint) = p._1
          val globalHeadArgs =
            (for (IConstant(c) <- headArgs take globalVarNum) yield c).toSet

          (globalHeadArgs.size == globalVarNum) &&
          (headArgs take globalVarNum) == (bodyArgs take globalVarNum) && {
            val occurringConstants = new MHashSet[ConstantTerm]
            val coll = new SymbolCollector(null, occurringConstants, null)
            coll.visitWithoutResult(constraint, 0)
            for (IAtom(_, args) <- (Iterator single head) ++ body.iterator)
              for (t <- args drop globalVarNum)
                coll.visitWithoutResult(t, 0)
            Seqs.disjoint(globalHeadArgs, occurringConstants)
          }
        }

      val newProcesses =
        (for (((clauses, repl), preds) <-
               processes.iterator zip localPreds.iterator) yield {
          val clauseBuffer = clauses.toBuffer

          // sort the predicates, to eliminate first predicates with high arity,
          // and then predicates with few incoming clauses
          val predsBuffer =
            ((for (pred <- preds.iterator;
                   if !(predsToKeep contains pred);
                   incoming =
                     for (p@(Clause(IAtom(`pred`, _), _, _), _) <- clauseBuffer)
                     yield p)
              yield (pred, incoming.size)).toVector
                                          .sortBy(t => (-t._1.arity, t._2))
                                          .map(_._1)).toBuffer

          var changed = true
          while (changed) {
            changed = false

            val predsIt = predsBuffer.iterator
            while (!changed && predsIt.hasNext) {
              val pred = predsIt.next
              val incoming =
                for (p@(Clause(IAtom(`pred`, _), _, _), _) <- clauseBuffer)
                yield p

              val outgoing =
                for (p@(Clause(_, List(IAtom(`pred`, _)), _), _) <-clauseBuffer)
                yield p

              if (// avoid blow-up
                  (incoming.size * outgoing.size <=
                     incoming.size + outgoing.size) &&
                  (incoming forall {
                     case (c, _) => !(c.bodyPredicates contains pred) &&
                                    (!outgoing.isEmpty ||
                                     Seqs.disjoint(predsWithTimeInvs,
                                                   c.predicates))
                   }) &&
                  (outgoing forall {
                     case (c, _) => c.head.pred != pred
                   })) {

                val newClauses =
                  if (incoming forall (isLocalClause(_)))
                    for ((c1, _) <- incoming; (c2, s) <- outgoing;
                         newClause = c2 mergeWith c1;
                         if !newClause.hasUnsatConstraint)
                    yield (newClause, s)
                  else if (!outgoing.isEmpty &&
                           (outgoing forall (isLocalClause(_))))
                    for ((c1, s) <- incoming; (c2, _) <- outgoing;
                         newClause = c2 mergeWith c1;
                         if !newClause.hasUnsatConstraint)
                    yield (newClause, s)
                  else
                    null

                if (newClauses != null) {
                  predsBuffer -= pred
                  clauseBuffer --= incoming
                  clauseBuffer --= outgoing
                  clauseBuffer ++= newClauses
                  changed = true
                }
              }
            }
          }

          (clauseBuffer.toList, repl)
        }).toList

      val allPreds = processPreds(newProcesses) + HornClauses.FALSE

      val newAssertions =
        assertions filter {
          clause => clause.predicates subsetOf allPreds }

      System(newProcesses,
             globalVarNum,
             backgroundAxioms,
             timeSpec,
             timeInvariants,
             newAssertions,
             hints filterPredicates allPreds)
    }

  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Verify a system specified as a set of processes in terms of
 * linear Horn clauses. Each process in the system can be either
 * Singleton or Infinite (representing infinite replication).
 *
 * It is assumed that the signature of every relation symbol involved
 * in the specification of a process starts with
 * <code>globalVarNum</code> global variables (arguments), following
 * by local variables (to be replicated in Infinite processes). In
 * addition, with Infinite processes, it is assumed that the first
 * local variable represents a unique process id.
 */
class ParametricEncoder(system : ParametricEncoder.System,
                        invariants : Seq[Seq[Int]]) {

  import ParametricEncoder._
  import VerificationHints._
  import HornClauses.Clause
  import IExpression._
  import Combinatorics._

  import system._

  // invariant specifications have to be consistent with the system
  assert(invariants forall {
           inv => inv.size == processes.size &&
                  ((processes.iterator zip inv.iterator) forall {
                     case ((_, Singleton), invNum) => 0 <= invNum && invNum <= 1
                     case ((_, Infinite), invNum)  => 0 <= invNum
                   })
         })

  //////////////////////////////////////////////////////////////////////////////

  val globalPredsSeq =
    (for (inv <- invariants.iterator;
          s <- genSubsequencesWithDups(localPreds, inv)) yield {
       val name = "inv_" + ((s.iterator map (_.name)) mkString "_")
       val sorts = globalVarSorts ++
                   (for (p <- s;
                         argSort <- predArgumentSorts(p) drop globalVarNum)
                    yield argSort)
       (s, MonoSortedPredicate (name, sorts))
     }).toList

  val globalPreds = globalPredsSeq.toMap

  val global2Local =
    (for ((l, p) <- globalPredsSeq.iterator) yield (p, l)).toMap

  /**
   * Given a global state atom, decode to the set of corresponding
   * local atoms (with the predicates used in the orginal
   * system description).
   */
  def decodeLocalStates(globalAtom : IAtom) : Seq[IAtom] = {
    val IAtom(globalPred, allArgs) = globalAtom
    val globalArgs = allArgs take globalVarNum
    var localOffset = globalVarNum
    for (lp <- global2Local(globalAtom.pred)) yield {
      val newLocalOffset = localOffset + lp.arity - globalVarNum
      val a = IAtom(lp, globalArgs ++ allArgs.slice(localOffset, newLocalOffset))
      localOffset = newLocalOffset
      a
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  def invPred(globalParams : Seq[ITerm],
              localParams : Seq[(Predicate, Seq[ITerm])]) : IAtom = {
    val sortedLocalParams =
      localParams sortBy { case (x, _) => localPredRanking(x) }
    val params = globalParams ++ (sortedLocalParams map (_._2)).flatten
    IAtom(globalPreds((sortedLocalParams map (_._1)).toList), params)
  }

  def groupIntoProcesses(localParams : Seq[(Predicate, Seq[ITerm])])
                        : Seq[Seq[(Predicate, Seq[ITerm])]] = {
    assert(compatiblePredicates(localParams map (_._1)))
    val predProcessGroupsMap = localParams groupBy {
      case (pred, _) => processIndex(pred)
    }
    for (i <- 0 until processes.size) yield predProcessGroupsMap.getOrElse(i, List())
  }

  // do the given predicates belong to processes that can coexist in the system?
  // this is not the case if there are two predicates that belong to the same
  // singleton process
  def compatiblePredicates(preds : Seq[Predicate]) = {
    val predProcessGroupsMap = preds groupBy processIndex
    processes.iterator.zipWithIndex forall {
      case ((_, Singleton), i) =>
        predProcessGroupsMap.getOrElse(i, List()).size <= 1
      case _ =>
        true
    }
  }

  def allInvariants(globalParams : Seq[ITerm],
                    localParams : Seq[(Predicate, Seq[ITerm])]) : List[IAtom] = {
    val predProcessGroups = groupIntoProcesses(localParams)
    (for (inv <- invariants.iterator;
          params <- genSubsequences(predProcessGroups, inv))
     yield invPred(globalParams, params)).toList
  }

  // check whether the given set of predicates is such that
  // not all predicates can be covered by available invariants.
  // in this case extra predicates are added to make further
  // invariants available
  def addExtraPreds(preds : Seq[Predicate]) : Iterator[List[Predicate]] = {
    val predProcessGroupsMap = preds groupBy processIndex
    val processNums =
      (for (i <- 0 until processes.size)
       yield (i, predProcessGroupsMap.getOrElse(i, List()).size)).toMap

    val uncoveredProcesses = new MHashSet[Int]
    for (p <- preds)
      uncoveredProcesses += processIndex(p)

    for (inv <- invariants.iterator;
         if (inv.iterator.zipWithIndex forall {
               case (n, i) => processNums(i) >= n
             });
         (n, i) <- inv.iterator.zipWithIndex;
         if (n > 0))
      uncoveredProcesses -= i

    if (uncoveredProcesses.isEmpty)
      return (Iterator single List())

    val interestingInvs =
      (for (inv <- invariants;
            if (uncoveredProcesses exists { i => inv(i) > 0 });
            missingProcesses =
              for ((n, i) <- inv.zipWithIndex) yield ((n - processNums(i)) max 0))
       yield (inv, missingProcesses)) sortBy { case (_, nums) => nums.sum }

    val extraNums = Array.fill(processes.size)(0)
    for ((inv, _) <- interestingInvs.iterator;
         if (uncoveredProcesses exists { i => inv(i) > 0 });
         (n, i) <- inv.iterator.zipWithIndex) {
      uncoveredProcesses -= i
      extraNums(i) = extraNums(i) max (n - processNums(i))
    }

    genSubsequencesWithDups(localPreds, extraNums)
  }

  //////////////////////////////////////////////////////////////////////////////

  def freshGlobalParams =
    (for ((s, j) <- globalVarSorts.iterator.zipWithIndex)
     yield i(s newConstant ("g_" + j))).toList

  def freshParams(preds : Seq[Predicate]) =
    (for ((p, k) <- preds.iterator.zipWithIndex) yield {
       (p,
        (for ((s, j) <- (predArgumentSorts(p).iterator drop globalVarNum)
                                             .zipWithIndex)
           yield i(s newConstant (p.name + "_" + k + "_" + j))).toList)
     }).toList

  def distinctIds(localParams : Seq[(Predicate, Seq[ITerm])]) =
    and(for (params <- groupIntoProcesses(localParams).iterator)
        yield distinct(for ((_, Seq(id, _*)) <- params) yield id))

  def timeAxioms(globalParams : Seq[ITerm]) : IFormula = timeSpec match {
    case ContinuousTime(_, denomIndex) => globalParams(denomIndex) > 0
    case _ => true
  }

  def allAxioms(globalParams : Seq[ITerm]) : IFormula =
    timeAxioms(globalParams) &&& (backgroundAxioms match {
      case Some(fun) => fun(globalParams)
      case None      => true
    })

  //////////////////////////////////////////////////////////////////////////////

  val symmetryTransitions =
    (for ((localPreds, globalPred) <- globalPreds.iterator;
          index <- (0 until (localPreds.size - 1)).iterator;
          if (localPreds(index) == localPreds(index + 1))) yield {
       val globalParams = freshGlobalParams
       val localParams = freshParams(localPreds)
       val shuffledLocalParams =
         (localParams take index) ++
         List(localParams(index + 1), localParams(index)) ++
         (localParams drop (index + 2))

       Clause(invPred(globalParams, localParams),
              List(invPred(globalParams, shuffledLocalParams)),
              distinctIds(localParams) &&& allAxioms(globalParams))
     }).toList

  //////////////////////////////////////////////////////////////////////////////

  val initTransitions =
    (for (inv <- invariants.iterator;
          localClauses <- genSubsequencesWithDups(localInitClauses, inv)) yield {
       // sort clauses, so that their order corresponds to the
       // predicate order in the global predicate
       val sortedLocalClauses =
         localClauses sortWith {
           case (Clause(IAtom(a, _), _, _), Clause(IAtom(b, _), _, _)) =>
             localPredRanking(a) < localPredRanking(b)
       }

       val freshClauses =
         for (c <- sortedLocalClauses) yield c.refresh._1
       val globalParams =
         freshGlobalParams
       val localParams =
         for (Clause(IAtom(p, a), _, _) <- freshClauses) yield (p, a drop globalVarNum)
       val constraint =
         and(for (Clause(IAtom(_, a), _, constraint) <- freshClauses)
             yield (constraint & ((a take globalVarNum) === globalParams)))

       (Clause(invPred(globalParams, localParams), List(),
               constraint &&& allAxioms(globalParams)),
        sortedLocalClauses)
     }).toList

  //////////////////////////////////////////////////////////////////////////////

  val localTransitions =
    (for ((process, _) <- processes.iterator;
          (clause@Clause(IAtom(headPred, headParams),
                         List(IAtom(bodyPred, bodyParams)),
                         constraint),
           NoSync) <- process.iterator;
          (localPreds, _) <- globalPredsSeq.iterator;
          if (localPreds contains bodyPred)) yield {
       val otherPreds = localPreds diff List(bodyPred)
       val otherParams = freshParams(otherPreds).toList

       val newBodyLit = invPred(bodyParams take globalVarNum,
                                (bodyPred, (bodyParams drop globalVarNum)) :: otherParams)
       val newHeadLit = invPred(headParams take globalVarNum,
                                (headPred, (headParams drop globalVarNum)) :: otherParams)

       (Clause(newHeadLit, List(newBodyLit),
               constraint &&&
               distinctIds((bodyPred, (bodyParams drop globalVarNum)) :: otherParams) &&&
               allAxioms(bodyParams take globalVarNum)),
        clause)
     }).toList

  //////////////////////////////////////////////////////////////////////////////

  val nonInterferenceTransitions =
    (for ((process, repl) <- processes.iterator;
          (clause@Clause(IAtom(headPred, headParams),
                         List(IAtom(bodyPred, bodyParams)),
                         constraint),
           NoSync) <- process.iterator;
          if ((headParams take globalVarNum) != (bodyParams take globalVarNum));
          (otherPreds, _) <- globalPredsSeq.iterator;
          if (compatiblePredicates(bodyPred :: otherPreds));
          extraPreds <- addExtraPreds(bodyPred :: otherPreds)) yield {
       val otherParams = freshParams(otherPreds).toList
       val extraParams = freshParams(extraPreds).toList

       val allParams = (bodyPred, (bodyParams drop globalVarNum)) ::
                         otherParams ::: extraParams

       val bodyLits =
         allInvariants(bodyParams take globalVarNum, allParams)
       val newHeadLit = invPred(headParams take globalVarNum, otherParams)

       (Clause(newHeadLit, bodyLits,
               constraint &&& distinctIds(allParams) &&&
               allAxioms(bodyParams take globalVarNum)),
        clause)
     }).toList

  //////////////////////////////////////////////////////////////////////////////

  def sendReceivePairs =
    for (((process1, repl), processNum1) <- processes.iterator.zipWithIndex;
         ((process2, _),    processNum2) <- processes.iterator.zipWithIndex;
         if (processNum1 != processNum2 || repl != Singleton);
         (sendC@Clause(_, List(_), _), Send(commChannel)) <- process1.iterator;
         (recC@Clause(_, List(_), _),  Receive(`commChannel`)) <- process2.iterator)
    yield (sendC, recC, commChannel)

  val sendReceiveTransitions =
    (for ((sendC@Clause(IAtom(headPred, headParams),
                        List(IAtom(bodyPred, bodyParams)),
                        constraint),
           recC@Clause(_, List(IAtom(bodyPred2, _)), _),
           commChannel) <- sendReceivePairs;
          (localPreds, _) <- globalPredsSeq.iterator;
          if ((localPreds intersect List(bodyPred, bodyPred2)).size == 2)) yield {
       val (Clause(IAtom(headPred2, headParams2),
                   List(IAtom(bodyPred2, bodyParams2)),
                   constraint2), _) = recC.refresh

       val otherPreds = localPreds diff List(bodyPred, bodyPred2)
       val otherParams = freshParams(otherPreds).toList

       val preParams =
         (bodyPred, (bodyParams drop globalVarNum)) ::
         (bodyPred2, (bodyParams2 drop globalVarNum)) :: otherParams
       val postParams =
         (headPred, (headParams drop globalVarNum)) ::
         (headPred2, (headParams2 drop globalVarNum)) :: otherParams

       val newBodyLit = invPred(bodyParams take globalVarNum, preParams)
       val newHeadLit = invPred(headParams2 take globalVarNum, postParams)

       (Clause(newHeadLit, List(newBodyLit),
               constraint &&& constraint2 &&& distinctIds(preParams) &&&
               ((headParams take globalVarNum) === (bodyParams2 take globalVarNum)) &&&
               allAxioms(bodyParams take globalVarNum)),
        (sendC, recC, commChannel))
     }).toList

  //////////////////////////////////////////////////////////////////////////////
  
  val sendNonInterTransitions =
    (for ((sendC@Clause(IAtom(headPred, headParams),
                        List(IAtom(bodyPred, bodyParams)),
                        constraint),
           recC@Clause(_, List(IAtom(bodyPred2, _)), _),
           commChannel) <- sendReceivePairs;
          (localPreds, _) <- globalPredsSeq.iterator;
          if ((localPreds contains bodyPred) &&
              compatiblePredicates(bodyPred2 :: localPreds));
          extraPreds <- addExtraPreds(bodyPred2 :: localPreds)) yield {
       val (Clause(IAtom(headPred2, headParams2),
                   List(IAtom(bodyPred2, bodyParams2)),
                   constraint2), _) = recC.refresh

       val otherPreds = localPreds diff List(bodyPred)
       val otherParams = freshParams(otherPreds).toList
       val extraParams = freshParams(extraPreds).toList

       val preParams =
         (bodyPred, (bodyParams drop globalVarNum)) ::
         (bodyPred2, (bodyParams2 drop globalVarNum)) :: otherParams ::: extraParams
       val postParams =
         (headPred, (headParams drop globalVarNum)) :: otherParams

       val newBodyLits = allInvariants(bodyParams take globalVarNum, preParams)
       val newHeadLit = invPred(headParams2 take globalVarNum, postParams)

       (Clause(newHeadLit, newBodyLits,
               constraint &&& constraint2 &&& distinctIds(preParams) &&&
               ((headParams take globalVarNum) === (bodyParams2 take globalVarNum)) &&&
               allAxioms(bodyParams take globalVarNum)),
        (sendC, recC, commChannel))
     }).toList

  //////////////////////////////////////////////////////////////////////////////

  val receiveNonInterTransitions =
    (for ((sendC@Clause(IAtom(headPred, headParams),
                        List(IAtom(bodyPred, bodyParams)),
                        constraint),
           recC@Clause(_, List(IAtom(bodyPred2, _)), _),
           commChannel) <- sendReceivePairs;
          (localPreds, _) <- globalPredsSeq.iterator;
          if ((localPreds contains bodyPred2) &&
              compatiblePredicates(bodyPred :: localPreds));
          extraPreds <- addExtraPreds(bodyPred :: localPreds)) yield {
       val (Clause(IAtom(headPred2, headParams2),
                   List(IAtom(bodyPred2, bodyParams2)),
                   constraint2), _) = recC.refresh

       val otherPreds = localPreds diff List(bodyPred2)
       val otherParams = freshParams(otherPreds).toList
       val extraParams = freshParams(extraPreds).toList

       val preParams =
         (bodyPred, (bodyParams drop globalVarNum)) ::
         (bodyPred2, (bodyParams2 drop globalVarNum)) :: otherParams ::: extraParams
       val postParams =
         (headPred2, (headParams2 drop globalVarNum)) :: otherParams

       val newBodyLits = allInvariants(bodyParams take globalVarNum, preParams)
       val newHeadLit = invPred(headParams2 take globalVarNum, postParams)

       (Clause(newHeadLit, newBodyLits,
               constraint &&& constraint2 &&& distinctIds(preParams) &&&
               ((headParams take globalVarNum) === (bodyParams2 take globalVarNum)) &&&
               allAxioms(bodyParams take globalVarNum)),
        (sendC, recC, commChannel))
     }).toList

  //////////////////////////////////////////////////////////////////////////////

  val sendReceiveNonInterTransitions =
    (for ((sendC@Clause(IAtom(headPred, headParams),
                        List(IAtom(bodyPred, bodyParams)),
                        constraint),
           recC@Clause(IAtom(_, headParams2),
                       List(IAtom(bodyPred2, bodyParams2)),
                       _),
           commChannel) <- sendReceivePairs;
          if ((headParams take globalVarNum) != (bodyParams take globalVarNum) ||
              (headParams2 take globalVarNum) != (bodyParams2 take globalVarNum));
          (otherPreds, _) <- globalPredsSeq.iterator;
          if (compatiblePredicates(bodyPred :: bodyPred2 :: otherPreds));
          extraPreds <- addExtraPreds(bodyPred :: bodyPred2 :: otherPreds)) yield {
       val (Clause(IAtom(headPred2, headParams2),
                   List(IAtom(bodyPred2, bodyParams2)),
                   constraint2), _) = recC.refresh

       val otherParams = freshParams(otherPreds).toList
       val extraParams = freshParams(extraPreds).toList

       val preParams =
         (bodyPred, (bodyParams drop globalVarNum)) ::
         (bodyPred2, (bodyParams2 drop globalVarNum)) :: otherParams ::: extraParams

       val newBodyLits = allInvariants(bodyParams take globalVarNum, preParams)
       val newHeadLit = invPred(headParams2 take globalVarNum, otherParams)

       (Clause(newHeadLit, newBodyLits,
               constraint &&& constraint2 &&& distinctIds(preParams) &&&
               ((headParams take globalVarNum) === (bodyParams2 take globalVarNum)) &&&
               allAxioms(bodyParams take globalVarNum)),
        (sendC, recC, commChannel))
     }).toList

  //////////////////////////////////////////////////////////////////////////////

  def syncClauses(b : Barrier,
                  syncPreds : List[Predicate])
                 : Iterator[List[Clause]] = syncPreds match {
    case List() =>
      Iterator single List()
    case pred :: remPreds =>
      for (suffix <- syncClauses(b, remPreds);
           (c@Clause(_, List(IAtom(`pred`, _)), _), BarrierSync(`b`)) <-
             processes(processIndex(pred))._1.iterator)
      yield c :: suffix
  }

  val barrierTransitions =
    (for (b@Barrier(domains) <- barriers.iterator;
          (allPreds, _) <- globalPredsSeq.iterator;
          syncablePreds =
            allPreds filter { p => domains(processIndex(p)) contains p };
          if (!syncablePreds.isEmpty);
          syncPreds <- b match {
            case b : SimpleBarrier =>
              Iterator single syncablePreds
            case b : BarrierFamily =>
              for (s <- genSubMultisets(syncablePreds); if (!s.isEmpty)) yield s
          };
          unsyncPreds = syncablePreds diff syncPreds;
          clauses <- syncClauses(b, syncPreds)) yield {

       val freshClauses = for (c <- clauses) yield c.refresh._1
       val globalParams = freshGlobalParams

       val otherPreds = allPreds diff syncPreds
       val otherParams = freshParams(otherPreds)

       val syncPreParams =
         for (Clause(_, List(IAtom(p, args)), _) <- freshClauses)
         yield (p, args drop globalVarNum)
       val syncPostParams =
         for (Clause(IAtom(p, args), List(_), _) <- freshClauses)
         yield (p, args drop globalVarNum)

       val constraint =
         and(for (Clause(_, List(IAtom(_, args)), c) <- freshClauses)
             yield (c &&& (args take globalVarNum) === globalParams))

       val newBodyLit = invPred(globalParams, syncPreParams ::: otherParams)
       val newHeadLit = invPred(globalParams, syncPostParams ::: otherParams)

       (Clause(newHeadLit, List(newBodyLit),
               constraint &&& distinctIds(syncPreParams ::: otherParams)),
        (clauses, b))
     }).toList

  //////////////////////////////////////////////////////////////////////////////

  val timeElapseTransitions = timeSpec match {
    case NoTime => List() // no time
    case _ => {
      val index = timeSpec match {
        case DiscreteTime(index) => index
        case ContinuousTime(index, _) => index
        case _ => assert(false); 0
      }

      (for ((localPreds, globalPred) <- globalPredsSeq.iterator) yield {
         val preGlobalParams = freshGlobalParams
         val newTime = i(new ConstantTerm ("NewTime"))
         val postGlobalParams = preGlobalParams.updated(index, newTime)
         val localParams = freshParams(localPreds)
         
         val timeConstraints =
           and(for (c@Clause(_, List(IAtom(p, _)), _) <- timeInvariants.iterator;
                    (q, qParams) <- localParams.iterator;
                    if (p == q)) yield {
                 val (Clause(_, List(IAtom(_, params)), negInv), _) = c.refresh
                 ~negInv & (params === (postGlobalParams ++ qParams))
               })

         Clause(invPred(postGlobalParams, localParams),
                List(invPred(preGlobalParams, localParams)),
                (newTime >= preGlobalParams(index)) &&& timeConstraints &&&
                distinctIds(localParams) &&&
                allAxioms(preGlobalParams))
       }).toList
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  val assertionTransitions =
    (for (clause@Clause(_, body, constraint) <- assertions.iterator;
          groupedBodyPreds =
            (for (IAtom(p, _) <- body) yield p) groupBy processIndex;
          bodyPredNums = for (i <- 0 until processes.size) 
                         yield groupedBodyPreds.getOrElse(i, List()).size;
          consideredProcessNums =
            for (i <- 0 until processes.size) yield (
              (for (inv <- invariants.iterator) yield inv(i)).max max bodyPredNums(i));
          otherPreds <- genSubsequencesWithDups(localPreds,
                          for (i <- 0 until processes.size)
                          yield (consideredProcessNums(i) - bodyPredNums(i)))) yield {
       val globalParams = freshGlobalParams
       val otherParams = freshParams(otherPreds)
       val allLocalParams =
         (for (IAtom(p, a) <- body) yield (p, a drop globalVarNum)) ++ otherParams

       val globalParamConstraint =
         and(for (IAtom(p, a) <- body) yield (globalParams === (a take globalVarNum)))

       (Clause(HornClauses.FALSE(),
               allInvariants(globalParams, allLocalParams),
               globalParamConstraint &&& constraint &&& distinctIds(allLocalParams) &&&
               allAxioms(globalParams)),
        clause)
     }).toList

  //////////////////////////////////////////////////////////////////////////////

//  println(symmetryTransitions)
  println("Symmetry clauses:                                      " +
          symmetryTransitions.size)

//  println(initTransitions)
  println("Init clauses:                                          " +
          initTransitions.size)

//  println(timeElapseTransitions)
  println("Time elapse clauses:                                   " +
          timeElapseTransitions.size)

//  println(assertionTransitions)
  println("Assertion clauses:                                     " +
          assertionTransitions.size)

//  println(localTransitions)
  println("Local transition clauses:                              " +
          localTransitions.size)

//  println(nonInterferenceTransitions)
  println("Local non-interference clauses:                        " +
          nonInterferenceTransitions.size)

//  println(sendReceiveTransitions)
  println("Send/receive clauses:                                  " +
          sendReceiveTransitions.size)

//  println(sendNonInterTransitions)
  println("Send non-interference clauses:                         " +
          sendNonInterTransitions.size)

//  println(receiveNonInterTransitions)
  println("Receive non-interference clauses:                      " +
          receiveNonInterTransitions.size)

//  println(sendReceiveNonInterTransitions)
  println("Send/receive non-interference clauses:                 " +
          sendReceiveNonInterTransitions.size)

//  println(barrierTransitions)
  println("Barrier clauses:                                       " +
          barrierTransitions.size)

  //////////////////////////////////////////////////////////////////////////////

  val allClauses = symmetryTransitions ++
                   (initTransitions map (_._1)) ++
                   (localTransitions map (_._1)) ++
                   (nonInterferenceTransitions map (_._1)) ++
                   (sendReceiveTransitions map (_._1)) ++
                   (sendNonInterTransitions map (_._1)) ++
                   (receiveNonInterTransitions map (_._1)) ++
                   (sendReceiveNonInterTransitions map (_._1)) ++
                   (barrierTransitions map (_._1)) ++
                   timeElapseTransitions ++
                   (assertionTransitions map (_._1))

  //////////////////////////////////////////////////////////////////////////////

  private def compilePredicateHints(s : Seq[Predicate])
                                   : Seq[VerifHintElement] = {
    val res = new ArrayBuffer[VerifHintElement]
    var shift = 0
    for (lp <- s) {
      for (pred <- hints.predicateHints.getOrElse(lp, List()))
        res += pred.shiftArguments(globalVarNum, shift)
      shift = shift + lp.arity - globalVarNum
    }
    res.toList
  }

  val globalPredicateHints =
    (for ((s, p) <- globalPredsSeq.iterator;
          hs = compilePredicateHints(s);
          if (!hs.isEmpty))
     yield (p -> hs)).toMap

  val globalHints = VerificationHints(globalPredicateHints)

  val globalInitialPredicates =
    (for ((p, hs) <- globalPredicateHints.iterator;
          preds = for (VerifHintInitPred(p) <- hs) yield p;
          if (!preds.isEmpty))
     yield (p -> preds)).toMap

  val globalPredicateTemplates =
    (for ((p, hs) <- globalPredicateHints.iterator;
          hs2 = for (h <- hs; if (h.isInstanceOf[VerifHintTplElement])) yield h;
          if (!hs2.isEmpty))
     yield (p -> hs2)).toMap

}
