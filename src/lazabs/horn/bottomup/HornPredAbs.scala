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
import ap.{Signature, DialogUtil, SimpleAPI, PresburgerTools}
import ap.parser._
import ap.parameters.{PreprocessingSettings, GoalSettings, Param,
                      ReducerSettings}
import ap.terfor.{ConstantTerm, VariableTerm, TermOrder, TerForConvenience,
                  Term, Formula}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction, Quantifier,
                               SeqReducerPluginFactory}
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.substitutions.{ConstantSubst, VariableSubst, VariableShiftSubst}
import ap.proof.{ModelSearchProver, QuantifierElimProver}
import ap.proof.theoryPlugins.PluginSequence
import ap.proof.tree.SeededRandomDataSource
import ap.util.{Seqs, Timeout}
import ap.theories.{Theory, TheoryCollector}
import ap.types.{TypeTheory, Sort, MonoSortedPredicate, IntToTermTranslator}
import SimpleAPI.ProverStatus

import lazabs.prover.{Tree, Leaf}
import Util._
import DisjInterpolator._

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 LinkedHashSet, LinkedHashMap,
                                 ArrayBuffer, Queue, PriorityQueue,
                                 ArrayBuilder, ArrayStack}
import scala.util.{Random, Sorting}

object HornPredAbs {

  import HornClauses._
  import TerForConvenience._
  
  class SymbolFactory(theories : Seq[Theory]) {
    private val constantsToAdd = new ArrayBuffer[ConstantTerm]

    val functionalPreds =
      (for (t <- theories.iterator;
            p <- t.functionalPredicates.iterator) yield p).toSet

    val reducerSettings = {
      var rs = ReducerSettings.DEFAULT
      rs = Param.FUNCTIONAL_PREDICATES.set(
             rs, functionalPreds)
      rs = Param.REDUCER_PLUGIN.set(
             rs, SeqReducerPluginFactory(
                   for (t <- theories) yield t.reducerPlugin))
      rs
    }

    var orderVar : TermOrder = TermOrder.EMPTY
    val functionEnc =
      new FunctionEncoder(Param.TIGHT_FUNCTION_SCOPES(PreprocessingSettings.DEFAULT),
                          Param.GENERATE_TOTALITY_AXIOMS(PreprocessingSettings.DEFAULT))

    for (t <- theories) {
      orderVar = t extend orderVar
      functionEnc addTheory t
    }

    def order : TermOrder = {
      if (!constantsToAdd.isEmpty) {
        orderVar = orderVar extend constantsToAdd
        constantsToAdd.clear
      }
      orderVar
    }

    def genConstant(name : String) : ConstantTerm = {
      val res = new ConstantTerm(name)
      constantsToAdd += res
      res
    }

    private var skolemCounter = 0

    def genSkolemConstant : ConstantTerm = {
      val num = skolemCounter
      skolemCounter = skolemCounter + 1
      genConstant("sk" + num)
    }

    def addSymbol(c : ConstantTerm) : Unit =
      constantsToAdd += c
    def addSymbols(cs : Seq[ConstantTerm]) : Unit =
      constantsToAdd ++= cs
    
    def reducer(assumptions : Conjunction) =
      ReduceWithConjunction(assumptions, order, reducerSettings)
    def reduce(c : Conjunction) =
      reducer(Conjunction.TRUE)(c)
    
    def genConstants(prefix : String,
                     num : Int, suffix : String) : Seq[ConstantTerm] = {
      val res = for (i <- 0 until num)
                yield new ConstantTerm(prefix + "_" + i + "_" + suffix)
      addSymbols(res)
      res
    }

    def genConstants(prefix : String,
                     sorts : Seq[Sort],
                     suffix : String) : Seq[ConstantTerm] = {
      val res = (for ((s, i) <- sorts.iterator.zipWithIndex)
                 yield s.newConstant(prefix + "_" + i + "_" + suffix)).toList
      addSymbols(res)
      res
    }

    def duplicateConstants(cs : Seq[ConstantTerm]) = {
      val res = for (c <- cs) yield c.clone
      addSymbols(res)
      res
    }
      
    def signature =
      Signature(Set(), Set(), order.orderedConstants, Map(), order, theories)

    def toInternal(f : IFormula) : Conjunction =
      HornPredAbs.toInternal(f, signature, functionEnc,
                             normalPreprocSettings)

    def toInternalClausify(f : IFormula) : Conjunction =
      HornPredAbs.toInternal(f, signature, functionEnc,
                             clausifyPreprocSettings)
                             
    def preprocess(f : Conjunction) : Conjunction =
      if (theories.isEmpty) f else !Theory.preprocess(!f, theories, order)
  }

  def predArgumentSorts(pred : Predicate) : Seq[Sort] = pred match {
    // TODO: use function MonoSortedPredicate.argumentSorts for this
    case pred : MonoSortedPredicate => pred.argSorts
    case _ => for (_ <- 0 until pred.arity) yield Sort.Integer
  }

  val normalPreprocSettings = PreprocessingSettings.DEFAULT
  val clausifyPreprocSettings = Param.CLAUSIFIER.set(normalPreprocSettings,
                                                     Param.ClausifierOptions.Simple)

  def toInternal(f : IFormula, sig : Signature) : Conjunction =
    toInternal(f, sig, null, normalPreprocSettings)

  def toInternal(f : IFormula,
                 sig : Signature,
                 functionEnc : FunctionEncoder,
                 settings : PreprocessingSettings) : Conjunction = {
    implicit val order = sig.order
    val (fors, _, _) =
      if (functionEnc == null)
        Preprocessing(~f, List(), sig, settings)
      else
        Preprocessing(~f, List(), sig, settings, functionEnc)
    ReduceWithConjunction(Conjunction.TRUE, order)(conj(InputAbsy2Internal(
      IExpression.or(for (f <- fors) yield IExpression removePartName f), order)).negate)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  case class RelationSymbol(pred : Predicate)(implicit val sf : SymbolFactory) {
    def arity = pred.arity
    def name = pred.name
    val argumentSorts = predArgumentSorts(pred)
    val arguments = toStream {
      case i => sf.genConstants(name, argumentSorts, "" + i)
    }

    val argumentITerms = arguments map (_.map(IExpression.i(_)))
    override def toString = toString(0)
    def toString(occ : Int) = name + "(" + (arguments(occ) mkString ", ") + ")"
  }

  case class RelationSymbolPred(rawPred : Conjunction,
                                positive : Conjunction,
                                negative : Conjunction,
                                rs : RelationSymbol,
                                predIndex : Int) {
    private val sf = rs.sf
    private val argConsts = rs.arguments.head

    private def substMap(from : Seq[ConstantTerm],
                         to : Seq[ConstantTerm])
                       : Map[ConstantTerm, Term] =
      (for ((oriC, newC) <- from.iterator zip to.iterator)
       yield (oriC -> l(newC)(sf.order))).toMap

    private def instanceStream(
                  f : Conjunction) : Stream[Conjunction] =
      f #:: {
        for (cs <- rs.arguments.tail) yield {
          ConstantSubst(substMap(argConsts, cs), sf.order)(f)
        }
      }

    val posInstances = instanceStream(positive)
    val negInstances = instanceStream(negative)

    override def toString = DialogUtil.asString {
      PrincessLineariser.printExpression(
        (new Simplifier)(Internal2InputAbsy(rawPred,
                           rs.sf.functionEnc.predTranslation)))
 //     print(positive)
 //     print(" / ")
 //     print(negative)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  case class AbstractState(rs : RelationSymbol, preds : Seq[RelationSymbolPred]) {
    val instances = toStream {
      case i => for (p <- preds) yield (p negInstances i)
    }
    val predConjunction = toStream {
      case i => rs.sf.reduce(Conjunction.conj(instances(i), rs.sf.order))
    }
    val predSet = preds.toSet
    val predHashCodeSet = predSet map (_.hashCode)
    override val hashCode = rs.hashCode + 3 * preds.hashCode
    override def equals(that : Any) = that match {
      case that : AbstractState => this.hashCode == that.hashCode &&
                                   this.rs == that.rs &&
                                   this.preds == that.preds
      case _ => false
    }
    override def toString = "(" + rs.name + ", <" + (preds mkString ", ") + ">)"
  }

  //////////////////////////////////////////////////////////////////////////////

  trait StateQueue {
    type TimeType
    def isEmpty : Boolean
    def enqueue(states : Seq[AbstractState],
                clause : NormClause, assumptions : Conjunction) : Unit
    def enqueue(states : Seq[AbstractState],
                clause : NormClause, assumptions : Conjunction,
                time : TimeType) : Unit
    def dequeue : (Seq[AbstractState], NormClause, Conjunction, TimeType)
    def removeGarbage(reachableStates : scala.collection.Set[AbstractState])
    def incTime : Unit = {}
  }

  class ListStateQueue extends StateQueue {
    type TimeType = Unit
    private var states = List[(Seq[AbstractState], NormClause, Conjunction)]()
    def isEmpty : Boolean =
      states.isEmpty
    def enqueue(s : Seq[AbstractState],
                clause : NormClause, assumptions : Conjunction) : Unit = {
      states = (s, clause, assumptions) :: states
//      println("enqueuing ... " +  (s, clause, assumptions))
    }
    def enqueue(s : Seq[AbstractState],
                clause : NormClause, assumptions : Conjunction,
                time : TimeType) : Unit =
      enqueue(s, clause, assumptions)
    def dequeue : (Seq[AbstractState], NormClause, Conjunction, TimeType) = {
      val res = states.head
      states = states.tail
      (res._1, res._2, res._3, ())
    }
    def removeGarbage(reachableStates : scala.collection.Set[AbstractState]) = 
      states = states filter {
        case (s, _, _) => s forall (reachableStates contains _)
      }
  }
  
  class PriorityStateQueue extends StateQueue {
    type TimeType = Int

    private var time = 0

    private def priority(s : (Seq[AbstractState], NormClause, Conjunction, Int)) = {
      val (states, NormClause(_, _, (RelationSymbol(headSym), _)), _, birthTime) = s
      (headSym match {
        case HornClauses.FALSE => -10000
        case _ => 0
      }) + (for (AbstractState(_, preds) <- states.iterator) yield preds.size).sum + birthTime
    }

    private implicit val ord = new Ordering[(Seq[AbstractState], NormClause, Conjunction, Int)] {
      def compare(s : (Seq[AbstractState], NormClause, Conjunction, Int),
                  t : (Seq[AbstractState], NormClause, Conjunction, Int)) =
        priority(t) - priority(s)
    }

    private val states = new PriorityQueue[(Seq[AbstractState], NormClause, Conjunction, Int)]

    def isEmpty : Boolean =
      states.isEmpty
    def enqueue(s : Seq[AbstractState],
                clause : NormClause, assumptions : Conjunction) : Unit = {
      states += ((s, clause, assumptions, time))
    }
    def enqueue(s : Seq[AbstractState],
                clause : NormClause, assumptions : Conjunction,
                t : TimeType) : Unit = {
      states += ((s, clause, assumptions, t))
    }
    def dequeue : (Seq[AbstractState], NormClause, Conjunction, TimeType) =
      states.dequeue
    def removeGarbage(reachableStates : scala.collection.Set[AbstractState]) = {
      val remainingStates = (states.iterator filter {
        case (s, _, _, _) => s forall (reachableStates contains _)
      }).toArray
      states.dequeueAll
      states ++= remainingStates
    }
    override def incTime : Unit =
      time = time + 1
  }
  
  //////////////////////////////////////////////////////////////////////////////

  case class AbstractEdge(from : Seq[AbstractState], to : AbstractState,
                          clause : NormClause, assumptions : Conjunction) {
    override def toString = "<" + (from mkString ", ") + "> -> " + to + ", " + clause
  }
  
  //////////////////////////////////////////////////////////////////////////////

  object NormClause {
    def apply[CC](c : CC, predMap : Predicate => RelationSymbol)
             (implicit sf : SymbolFactory,
              conv : CC => ConstraintClause)
             : NormClause = {
      import IExpression._

      assert(c.localVariableNum == 0) // currently only this case is supported

      var rss = List[RelationSymbol]()
      
      val (lits, litSyms) = (for (lit <- c.body ++ List(c.head)) yield {
        val rs = predMap(lit.predicate)
        val occ = rss count (_ == rs)
        rss = rs :: rss
        ((rs, occ), rs.arguments(occ))
      }).unzip
      
      // use a local order to speed up the conversion in case of many symbols
//      val syms = (for ((rs, occ) <- lits.iterator;
//                       c <- rs.arguments(occ).iterator) yield c).toSet
//      val localOrder = sf.order restrict syms

      val constraint =
        sf.preprocess(
          c.instantiateConstraint(litSyms.last, litSyms.init, List(),
                                  sf.signature))

      val skConstraint =
        skolemise(constraint, false, List())
      val finalConstraint =
        if (skConstraint eq constraint)
          constraint
        else
          sf reduce skConstraint

      NormClause(finalConstraint, lits.init, lits.last)
    }
  }

  private def skolemise(c : Conjunction,
                        negated : Boolean,
                        substTerms : List[Term])
                       (implicit sf : SymbolFactory) : Conjunction = {
    val newSubstTerms = c.quans match {
      case Seq() =>
        substTerms
      case quans => {
        val N = quans.size
        Seqs.prepend(
          for ((q, n) <- quans.zipWithIndex) yield q match {
            case Quantifier.EX if !negated => sf.genSkolemConstant
            case Quantifier.ALL if negated => sf.genSkolemConstant
            case _ => v(n)
          },
          for (t <- substTerms) yield t match {
            case VariableTerm(ind) => VariableTerm(ind + N)
            case t => t
          })
      }
    }

    val newNegConjs =
      c.negatedConjs.update(
        for (d <- c.negatedConjs) yield skolemise(d, !negated, newSubstTerms),
        sf.order)

    if (newSubstTerms.isEmpty) {
      c.updateNegatedConjs(newNegConjs)(sf.order)
    } else {
      val subst = VariableSubst(0, newSubstTerms, sf.order)
      Conjunction(c.quans,
                  subst(c.arithConj),
                  subst(c.predConj),
                  newNegConjs,
                  sf.order)
    }
  }

  case class NormClause(constraint : Conjunction,
                        body : Seq[(RelationSymbol, Int)],
                        head : (RelationSymbol, Int))
                       (implicit sf : SymbolFactory) {
    val headSyms : Seq[ConstantTerm] =
      head._1.arguments(head._2)
    val bodySyms : Seq[Seq[ConstantTerm]] =
      for ((rs, occ) <- body) yield (rs arguments occ)
    val order = sf.order restrict (
      constraint.constants ++ headSyms ++ bodySyms.flatten)
    val localSymbols : Seq[ConstantTerm] =
      order.sort(constraint.constants -- headSyms -- bodySyms.flatten)
    val allSymbols =
      (localSymbols.iterator ++ headSyms.iterator ++ (
          for (cl <- bodySyms.iterator; c <- cl.iterator) yield c)).toSeq

    // indexes of the bodySyms constants that actually occur in the
    // constraint and are therefore relevant
    val relevantBodySyms : Seq[Seq[Int]] =
      for (syms <- bodySyms) yield
        (for ((c, i) <- syms.iterator.zipWithIndex;
              if (constraint.constants contains c)) yield i).toSeq

    def freshConstraint(implicit sf : SymbolFactory)
                       : (Conjunction, Seq[ConstantTerm], Seq[Seq[ConstantTerm]]) = {
      val newLocalSyms =
        sf duplicateConstants localSymbols
      val newHeadSyms = 
        sf duplicateConstants headSyms
      val newBodySyms =
        for (cs <- bodySyms) yield (sf duplicateConstants cs)
      
      val newSyms =
        newLocalSyms.iterator ++ newHeadSyms.iterator ++ (
          for (syms <- newBodySyms.iterator; c <- syms.iterator) yield c)
      val subst = ConstantSubst((allSymbols.iterator zip newSyms).toMap, sf.order)
      (subst(constraint), newHeadSyms, newBodySyms)
    }

    def substituteSyms(newLocalSyms : Seq[ConstantTerm],
                       newHeadSyms : Seq[ConstantTerm],
                       newBodySyms : Seq[Seq[ConstantTerm]])
                      (implicit order : TermOrder) : Conjunction = {
      val newSyms =
        newLocalSyms.iterator ++ newHeadSyms.iterator ++ (
          for (syms <- newBodySyms.iterator; c <- syms.iterator) yield c)
      val subst = ConstantSubst((allSymbols.iterator zip newSyms).toMap, order)
      subst(constraint)
    }

    def updateConstraint(newConstraint : Conjunction) =
      NormClause(newConstraint, body, head)

    override def toString =
      "" + head._1.toString(head._2) +
      " :- " + ((for ((rs, occ) <- body) yield rs.toString(occ)) mkString ", ") +
      " | " + constraint
  }
  
  //////////////////////////////////////////////////////////////////////////////

  implicit def normClause2ConstraintClause(nc : NormClause) = {
    val NormClause(_, bodyLits, (RelationSymbol(headPred), _)) = nc

    new ConstraintClause {
      def head : Literal = new Literal {
        val predicate = headPred
        val relevantArguments = (0 until predicate.arity).toSeq
      }
      def body : Seq[Literal] =
        (for (((RelationSymbol(pred), _), relSyms) <-
              bodyLits.iterator zip nc.relevantBodySyms.iterator)
         yield new Literal {
           val predicate = pred
           val relevantArguments = relSyms
         }).toSeq
      def localVariableNum : Int = nc.localSymbols.size
      def instantiateConstraint(headArguments : Seq[ConstantTerm],
                                bodyArguments: Seq[Seq[ConstantTerm]],
                                localVariables : Seq[ConstantTerm],
                                sig : Signature) : Conjunction =
        nc.substituteSyms(localVariables, headArguments, bodyArguments)(sig.order)
      override def collectTheories(coll : TheoryCollector) : Unit =
        coll(nc.constraint.order)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  object CounterexampleMethod extends Enumeration {
    val FirstBestShortest, RandomShortest, AllShortest,
        MaxNOrShortest = Value
  }

  val MaxNOr = 5

}

////////////////////////////////////////////////////////////////////////////////

class HornPredAbs[CC <% HornClauses.ConstraintClause]
                 (iClauses : Iterable[CC],
                  initialPredicates : Map[Predicate, Seq[IFormula]],
                  predicateGenerator : Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
                                       Either[Seq[(Predicate, Seq[Conjunction])],
                                              Dag[(IAtom, HornPredAbs.NormClause)]],
                  counterexampleMethod : HornPredAbs.CounterexampleMethod.Value =
                                           HornPredAbs.CounterexampleMethod.FirstBestShortest) {
  
  import HornPredAbs._

  lazabs.GlobalParameters.get.setupApUtilDebug
  
  val startTime = System.currentTimeMillis
  var predicateGeneratorTime : Long = 0
  var implicationChecks = 0
  var implicationChecksPos = 0
  var implicationChecksNeg = 0
  var implicationChecksPosTime : Long = 0
  var implicationChecksNegTime : Long = 0
  var implicationChecksSetup = 0
  var implicationChecksSetupTime : Long = 0

  var hasherChecksHit, hasherChecksMiss = 0
  var matchCount = 0
  var matchTime : Long = 0  

  val rand = new Random (98762521)

  // first find out which theories are relevant
  val theories = {
    val coll = new TheoryCollector
    coll addTheory TypeTheory
    for (c <- iClauses)
      c collectTheories coll
    coll.theories
  }

  if (!theories.isEmpty)
    println("Theories: " + (theories mkString ", "))

  val plugins =
    for (t <- theories; p <- t.plugin.toSeq) yield p

  val useHashing =
    (theories forall {
       case ap.types.TypeTheory                 => true
       case ap.theories.GroebnerMultiplication  => true
       case ap.theories.ModuloArithmetic        => true
       case _                                   => false
     }) &&
    (theories exists {
       case ap.theories.GroebnerMultiplication  => true
       case ap.theories.ModuloArithmetic        => true
       case _                                   => false
     })

  if (useHashing)
    println("State hashing enabled")

  implicit val sf = new SymbolFactory(theories)
  
  val relationSymbols =
    (for (c <- iClauses.iterator;
          lit <- (Iterator single c.head) ++ c.body.iterator;
          p = lit.predicate)
     yield (p -> RelationSymbol(p))).toMap

  // make sure that arguments constants have been instantiated
  for (c <- iClauses) {
    val preds = for (lit <- c.head :: c.body.toList) yield lit.predicate
    for (p <- preds.distinct) {
      val rs = relationSymbols(p)
      for (i <- 0 until (preds count (_ == p)))
        rs arguments i
    }
  }

  // translate clauses to internal form
  val (normClauses, relationSymbolBounds) = {
    val rawNormClauses = new LinkedHashMap[NormClause, CC]

    for (c <- iClauses) {
      lazabs.GlobalParameters.get.timeoutChecker()
      rawNormClauses.put(NormClause(c, (p) => relationSymbols(p)), c)
    }

    if (lazabs.GlobalParameters.get.intervals) {
      val res = new LinkedHashMap[NormClause, CC]

      val propagator =
        new IntervalPropagator (rawNormClauses.keys.toIndexedSeq,
                                sf.reducerSettings)

      for ((nc, oc) <- propagator.result)
        res.put(nc, rawNormClauses(oc))

      (res.toSeq, propagator.rsBounds)
    } else {
      val emptyBounds =
        (for (rs <- relationSymbols.valuesIterator)
         yield (rs -> Conjunction.TRUE)).toMap
      (rawNormClauses.toSeq, emptyBounds)
    }
  }

  val relationSymbolReducers =
    (for (rs <- relationSymbols.valuesIterator) yield {
      val bounds = relationSymbolBounds.getOrElse(rs, Conjunction.TRUE)
      (rs, sf reducer (if (bounds.isFalse) Conjunction.TRUE else bounds))
     }).toMap

  println("Unique satisfiable clauses: " + normClauses.size)

  for ((num, clauses) <-
        (normClauses groupBy { c => c._1.body.size }).toList sortBy (_._1))
    println("   " + clauses.size + " clauses with " + num + " body literals")

  val relationSymbolOccurrences = {
    val relationSymbolOccurrences =
      (for (rs <- relationSymbols.values)
         yield (rs -> new ArrayBuffer[(NormClause, Int, Int)])).toMap
    for ((c@NormClause(_, body, _), _) <- normClauses.iterator;
         ((rs, occ), i) <- body.iterator.zipWithIndex) {
      relationSymbolOccurrences(rs) += ((c, occ, i))
    }
    relationSymbolOccurrences mapValues (_.toVector)
  }

  val predicates =
    (for (rs <- relationSymbols.values)
       yield (rs -> new ArrayBuffer[RelationSymbolPred])).toMap
  
  //////////////////////////////////////////////////////////////////////////////

  val goalSettings = {
    var gs = GoalSettings.DEFAULT
//    gs = Param.CONSTRAINT_SIMPLIFIER.set(gs, determineSimplifier(settings))
//    gs = Param.SYMBOL_WEIGHTS.set(gs, SymbolWeights.normSymbolFrequencies(formulas, 1000))
//    gs = Param.PROOF_CONSTRUCTION.set(gs, constructProofs)
    gs = Param.GARBAGE_COLLECTED_FUNCTIONS.set(gs, sf.functionalPreds)
    gs = Param.FUNCTIONAL_PREDICATES.set(gs, sf.functionalPreds)
//    gs = Param.PREDICATE_MATCH_CONFIG.set(gs, signature.predicateMatchConfig)
    gs = Param.THEORY_PLUGIN.set(gs, PluginSequence(plugins))
    gs = Param.REDUCER_SETTINGS.set(gs, sf.reducerSettings)
    gs = Param.RANDOM_DATA_SOURCE.set(gs, new SeededRandomDataSource(12354))
    gs
  }

  val emptyProver = {
    val order = sf.order restrict Set()
    var prover = ModelSearchProver emptyIncProver goalSettings
    for (t <- theories)
      prover = prover.assert(Conjunction.conj(t.axioms, order), order)
    prover
  }

  var hardValidityCheckNum = 0
  var hardValidityCheckThreshold = 27
  var hardValidityCheckNumSqrt = 3

  def isValid(prover : ModelSearchProver.IncProver) : Boolean =
    prover.isObviouslyValid ||
    Timeout.withChecker(lazabs.GlobalParameters.get.timeoutChecker) {
      hardValidityCheckNum = hardValidityCheckNum + 1
      if (hardValidityCheckNum == hardValidityCheckThreshold) {
        hardValidityCheckNum = 0
        hardValidityCheckThreshold = hardValidityCheckThreshold + 2
        hardValidityCheckNumSqrt = hardValidityCheckNumSqrt + 1
      }

      if (hasher.acceptsModels && (rand nextInt hardValidityCheckNumSqrt) == 0)
        (prover checkValidity true) match {
          case Left(m) =>
            if (m.isFalse) {
              true
            } else {
              hasher addModel m
              false
            }
          case Right(_) =>
            throw new Exception("Unexpected prover result")
        }
      else
        !prover.isObviouslyUnprovable &&
         ((prover checkValidity false) match {
            case Left(m) if (m.isFalse) => true
            case Left(_) => false
            case Right(_) =>
              throw new Exception("Unexpected prover result")
          })
    }
  
  //////////////////////////////////////////////////////////////////////////////

  // Hashing/sampling to speed up implication checks

  val hasher =
    if (useHashing)
      new Hasher(sf.order, sf.reducerSettings)
    else
      InactiveHasher

  val predicateHashIndexes =
    (for (rs <- relationSymbols.values)
         yield (rs -> new ArrayBuffer[Stream[Int]])).toMap

  def addRelationSymbolPred(pred : RelationSymbolPred) : Unit = {
    assert(predicates(pred.rs).size == predicateHashIndexes(pred.rs).size &&
           pred.predIndex == predicates(pred.rs).size)

    predicates(pred.rs) +=
      pred
    predicateHashIndexes(pred.rs) +=
      (for (f <- pred.posInstances) yield (hasher addFormula f))
  }

  def addRelationSymbolPreds(preds : Seq[RelationSymbolPred]) : Unit =
    for (pred <- preds) addRelationSymbolPred(pred)

  def addHasherAssertions(clause : NormClause,
                          from : Seq[AbstractState]) = if (hasher.isActive) {
    hasher assertFormula clauseHashIndexes(clause)
    for ((state, (rs, occ)) <- from.iterator zip clause.body.iterator)
      for (pred <- state.preds) {
        val id = predicateHashIndexes(rs)(pred.predIndex)(occ)
        hasher assertFormula id
      }
  }

  // Add clause constraints to hasher

  val clauseHashIndexes =
    (for ((clause, _) <- normClauses.iterator)
     yield (clause, hasher addFormula clause.constraint)).toMap

  //////////////////////////////////////////////////////////////////////////////

  // Initialise with given initial predicates
  
  for ((p, preds) <- initialPredicates) {
    val rs = relationSymbols(p)
    for ((f, predIndex) <- preds.iterator.zipWithIndex) {
      val intF = IExpression.subst(f, rs.argumentITerms.head.toList, 0)
      val (rawF, posF, negF) = rsPredsToInternal(intF)
      val pred = RelationSymbolPred(rawF, posF, negF, rs, predIndex)
      addRelationSymbolPred(pred)
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  
  // Abstract states that are used for matching and instantiating clauses
  val activeAbstractStates = 
    (for (rs <- relationSymbols.values)
       yield (rs -> new LinkedHashSet[AbstractState])).toMap

  // Abstract states that are maximum (have a minimum number of
  // constraints in form of assumed predicates), and therefore not
  // subsumed by any other states
  val maxAbstractStates = 
    (for (rs <- relationSymbols.values)
       yield (rs -> new LinkedHashSet[AbstractState])).toMap

  // Subsumed abstract states, mapped to the subsuming (more general) state
  val forwardSubsumedStates, backwardSubsumedStates =
    new LinkedHashMap[AbstractState, AbstractState]

  val abstractEdges =
    new ArrayBuffer[AbstractEdge]

  //////////////////////////////////////////////////////////////////////////////

  val nextToProcess = new PriorityStateQueue

  // Expansions that have been postponed due to backwards subsumption
  val postponedExpansions =
    new ArrayBuffer[(Seq[AbstractState], NormClause, Conjunction, nextToProcess.TimeType)]

  // seed the ARG construction using the clauses with empty bodies (facts)
  for ((clause@NormClause(constraint, Seq(), _), _) <- normClauses)
    nextToProcess.enqueue(List(), clause, constraint)

  val endSetupTime = System.currentTimeMillis

  //////////////////////////////////////////////////////////////////////////////
    
  // the main loop

  private var inferenceAPIProver : SimpleAPI = null

  val rawResult : Either[Map[Predicate, Conjunction],
                         Dag[(IAtom, CC)]] = /* SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>

    inferenceAPIProver = p */ {

    if (lazabs.GlobalParameters.get.log) {
      println
      println("Starting CEGAR ...")
    }

    import TerForConvenience._
    var res : Either[Map[Predicate, Conjunction], Dag[(IAtom, CC)]] = null
    var iterationNum = 0

    while (!nextToProcess.isEmpty && res == null) {
      lazabs.GlobalParameters.get.timeoutChecker()

/*
      // The invariants supposed to be preserved by the subsumption mechanism
      assert(
        (maxAbstractStates forall {
          case (rs, preds) => (preds subsetOf activeAbstractStates(rs)) &&
                              (preds forall { s => activeAbstractStates(rs) forall {
                                                   t => s == t || !subsumes(t, s) } }) }) &&
        (backwardSubsumedStates forall {
          case (s, t) => s != t && subsumes(t, s) &&
                         (activeAbstractStates(s.rs) contains s) &&
                         !(maxAbstractStates(s.rs) contains s) &&
                         (activeAbstractStates(t.rs) contains t) }) &&
        (forwardSubsumedStates forall {
          case (s, t) => s != t && subsumes(t, s) &&
                         !(activeAbstractStates(s.rs) contains s) &&
                         (activeAbstractStates(t.rs) contains t) }) &&
        (activeAbstractStates forall {
          case (rs, preds) =>
                         preds forall { s => (maxAbstractStates(rs) contains s) ||
                         (backwardSubsumedStates contains s) } }) &&
        (postponedExpansions forall {
          case (from, _, _, _) => from exists (backwardSubsumedStates contains _) })
      )
*/

      val expansion@(states, clause, assumptions, _) = nextToProcess.dequeue

      if (states exists (backwardSubsumedStates contains _)) {
        postponedExpansions += expansion
      } else {
        try {
          for (e <- genEdge(clause, states, assumptions))
            addEdge(e)
        } catch {
          case Counterexample(from, clause) => {
            // we might have to process this case again, since
            // the extract counterexample might not be the only one
            // leading to this abstract state
            nextToProcess.enqueue(states, clause, assumptions)

            val clauseDag = extractCounterexample(from, clause)
            iterationNum = iterationNum + 1

            if (lazabs.GlobalParameters.get.log) {
    	      println
              print("Found counterexample #" + iterationNum + ", refining ... ")

              if (lazabs.GlobalParameters.get.logCEX) {
                println
                clauseDag.prettyPrint
              }
            }
        
            {
              val predStartTime = System.currentTimeMillis
              val preds = predicateGenerator(clauseDag)
              predicateGeneratorTime =
                predicateGeneratorTime + System.currentTimeMillis - predStartTime
              preds
            } match {
              case Right(trace) => {
                if (lazabs.GlobalParameters.get.log)
                  print(" ... failed, counterexample is genuine")
                val clauseMapping = normClauses.toMap
                res = Right(for (p <- trace) yield (p._1, clauseMapping(p._2)))
              }
              case Left(newPredicates) => {
                if (lazabs.GlobalParameters.get.log)
                  println(" ... adding predicates:")
                addPredicates(newPredicates)
              }
            }
          }
        }
      }
    }
  
    if (res == null) {
      assert(nextToProcess.isEmpty)

      implicit val order = sf.order
    
      res = Left((for ((rs, preds) <- maxAbstractStates.iterator;
                       if (rs.pred != HornClauses.FALSE)) yield {
        val rawFor = disj(for (AbstractState(_, fors) <- preds.iterator) yield {
          conj((for (f <- fors.iterator) yield f.rawPred) ++
               (Iterator single relationSymbolBounds(rs)))
        })
        val simplified = //!QuantifierElimProver(!rawFor, true, order)
                         PresburgerTools elimQuantifiersWithPreds rawFor

        val symMap =
          (rs.arguments.head.iterator zip (
             for (i <- 0 until rs.arity) yield v(i)).iterator).toMap
        val subst = ConstantSubst(symMap, order)
             
        rs.pred -> subst(simplified)
      }).toMap)
    }

    inferenceAPIProver = null

    val endTime = System.currentTimeMillis

    if (lazabs.GlobalParameters.get.log)
      println

    println
    println(
         "--------------------------------- Statistics -----------------------------------")
    println("CEGAR iterations:                                      " + iterationNum)
    println("Total CEGAR time (ms):                                 " + (endTime - startTime))
    println("Setup time (ms):                                       " + (endSetupTime - startTime))
    println("Final number of abstract states:                       " +
            (for ((_, s) <- maxAbstractStates.iterator) yield s.size).sum)
    println("Final number of matched abstract states:               " +
            (for ((_, s) <- activeAbstractStates.iterator) yield s.size).sum)
    println("Final number of abstract edges:                        " + abstractEdges.size)

    val predNum =
      (for ((_, s) <- predicates.iterator) yield s.size).sum
    val totalPredSize =
      (for ((_, s) <- predicates.iterator; p <- s.iterator)
       yield TreeInterpolator.nodeCount(p.rawPred)).sum
    val averagePredSize =
      if (predNum == 0) 0.0 else (totalPredSize.toFloat / predNum)
    println("Number of generated predicates:                        " + predNum)
    println(f"Average predicate size (# of sub-formulas):            $averagePredSize%.2f")
    println("Predicate generation time (ms):                        " + predicateGeneratorTime)

    println("Number of implication checks:                          " + implicationChecks)
    println
    println("Number of implication checks (setup):                  " + implicationChecksSetup)
    println("Number of implication checks (positive):               " + implicationChecksPos)
    println("Number of implication checks (negative):               " + implicationChecksNeg)
    println("Time for implication checks (setup, ms):               " + implicationChecksSetupTime)
    println("Time for implication checks (positive, ms):            " + implicationChecksPosTime)
    println("Time for implication checks (negative, ms):            " + implicationChecksNegTime)

    if (hasher.isActive) {
//      println
//      println("Number of state/clause matchings:                      " + matchCount)
//      println("Time for state/clause matchings (ms):                  " + matchTime)
      println
      hasher.printStatistics

      val hasherChecksNum = hasherChecksMiss + hasherChecksHit
      val hasherChecksRate =
        if (hasherChecksNum == 0)
          0
        else
          hasherChecksHit * 100 / hasherChecksNum
      println("Hasher hits/misses:                                    " +
              hasherChecksHit + "/" + hasherChecksMiss + " (" +
              hasherChecksRate + "%)")
    }

/*    println
    println("Number of subsumed abstract states:            " +
            (for ((_, s) <- activeAbstractStates.iterator;
                  t <- s.iterator;
                  if (s exists { r => r != t && subsumes(r, t) })) yield t).size) */
    println(
         "--------------------------------------------------------------------------------")
    println

    res
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * A set of predicates that is sufficient to solve the set of Horn clauses.
   */
  lazy val relevantRawPredicates : Map[Predicate, Seq[Conjunction]] = {
    import TerForConvenience._
    implicit val order = sf.order

    (for ((rs, preds) <- maxAbstractStates.iterator;
          if (rs.pred != HornClauses.FALSE)) yield {
      val symMap =
       (rs.arguments.head.iterator zip (
           for (i <- 0 until rs.arity) yield v(i)).iterator).toMap
      val subst = ConstantSubst(symMap, order)

      val allPreds =
        (for (AbstractState(_, fors) <- preds.iterator;
              f <- fors.iterator) yield subst(f.posInstances.head)).toList
             
      rs.pred -> allPreds.distinct
    }).toMap
  }

  /**
   * A set of predicates that is sufficient to solve the set of Horn clauses.
   */
  lazy val relevantPredicates : Map[Predicate, Seq[IFormula]] =
    for ((p, preds) <- relevantRawPredicates) yield {
      p -> convertToInputAbsy(p, preds)
    }

  //////////////////////////////////////////////////////////////////////////////

  lazy val relevantDisjuncts : Map[Predicate, Seq[Conjunction]] = {
    import TerForConvenience._
    implicit val order = sf.order

    (for ((rs, preds) <- maxAbstractStates.iterator;
          if (rs.pred != HornClauses.FALSE)) yield {
      val symMap =
       (rs.arguments.head.iterator zip (
           for (i <- 0 until rs.arity) yield v(i)).iterator).toMap
      val subst = ConstantSubst(symMap, order)

      val allPreds =
        (for (AbstractState(_, fors) <- preds.iterator;
              if (!fors.isEmpty)) yield {
          val g = conj(for (f <- fors.iterator) yield f.posInstances.head)
          subst(!QuantifierElimProver(!g, true, order))
        }).toList
             
      rs.pred -> allPreds.distinct
    }).toMap
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * The result of CEGAR: either a solution of the Horn clauses, or
   * a counterexample DAG containing the predicates and clauses.
   */
  lazy val result : Either[Map[Predicate, IFormula],
                           Dag[(IAtom, CC)]] = rawResult match {
    case Left(solution) =>
      Left(for ((p, c) <- solution)
           yield (p, convertToInputAbsy(p, List(c)).head))
    case Right(trace) =>
      Right(trace)
  }

  /**
   * Translate solution formulas back to input ASTs. This will
   * first replace the variables with sorted constants, to
  *  to enable theory-specific back-translation.
   */
  private def convertToInputAbsy(p : Predicate,
                                 cs : Seq[Conjunction]) : Seq[IFormula] =
    cs match {
      case Seq(c) if c.isTrue =>
        List(IBoolLit(true))
      case Seq(c) if c.isFalse =>
        List(IBoolLit(false))
      case cs => {
        val consts =
          for (s <- predArgumentSorts(p)) yield (s newConstant "X")
        val order =
          sf.order extend consts.reverse
        val subst =
          VariableSubst(0, consts, order)
        val backSubst =
          (for ((c, n) <- consts.iterator.zipWithIndex)
           yield (c -> IVariable(n))).toMap
        val simplifier =
          new Simplifier

        for (c <- cs) yield {
          val cWithConsts =
            TypeTheory.filterTypeConstraints(subst(c))
          implicit val context =
            new Theory.DefaultDecoderContext(cWithConsts)
          val internal =
            Internal2InputAbsy(cWithConsts, sf.functionEnc.predTranslation)
          val simp =
            IntToTermTranslator(simplifier(internal))
          ConstantSubstVisitor(simp, backSubst)
        }
      }
    }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def addEdge(newEdge : AbstractEdge) = {
    addState(newEdge.to)
    abstractEdges += newEdge
//    println("Adding edge: " + newEdge)
    if (lazabs.GlobalParameters.get.log)
      print(".")
  }
  
  def addState(state : AbstractState) = if (!(forwardSubsumedStates contains state)) {
    val rs = state.rs
    if (!(activeAbstractStates(rs) contains state)) {
      // check whether the new state is subsumed by an old state
      (maxAbstractStates(rs) find (subsumes(_, state))) match {
        case Some(subsumingState) =>
//          println("Subsumed: " + state + " by " + subsumingState)
          forwardSubsumedStates.put(state, subsumingState)

        case None => {

//          println("Adding state: " + state)

          // This state has to be added as a new state. Does it
          // (backward) subsume older states?
          val subsumedStates =
            maxAbstractStates(rs).iterator.filter(subsumes(state, _)).toArray

          if (!subsumedStates.isEmpty) {
//            println("Backward subsumed by " + state + ": " + (subsumedStates mkString ", "))
            maxAbstractStates(rs) --= subsumedStates
            for (s <- subsumedStates)
              backwardSubsumedStates.put(s, state)
          }

          nextToProcess.incTime
    
          findNewMatches(state)

          activeAbstractStates(rs) += state
          maxAbstractStates(rs) += state
        }
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  def findNewMatches(state : AbstractState) : Unit = {
    val startTime = System.currentTimeMillis

    val rs = state.rs

    import TerForConvenience._

    for ((clause, occ, index) <- relationSymbolOccurrences(rs)) {

      val byStates : Array[Seq[AbstractState]] =
        (for (((bodyRs, _), ind) <- clause.body.iterator.zipWithIndex)
         yield ind match {
           case `index` =>
             List(state)
           case ind if (ind < index && bodyRs == rs) =>
             activeAbstractStates(bodyRs).toSeq ++ List(state)
           case _ =>
             activeAbstractStates(bodyRs).toSeq
         }).toArray

      if (byStates exists (_.isEmpty)) {

        // nothing to do

      } else {

        implicit val _ = clause.order

        val initialAssumptions =
          sf.reduce(conj(List(clause.constraint) ++ (state instances occ)))
  
        if (!initialAssumptions.isFalse) {

          if ((byStates count (_.size > 1)) >= 2)
            matchClausePrereduce(state, initialAssumptions, clause,
                                 index, occ, byStates)
          else
            matchClauseSimple(state, initialAssumptions, clause,
                              index, occ, byStates)
        }
      }
    }

    matchCount = matchCount + 1
    matchTime = matchTime + (System.currentTimeMillis - startTime)
  }

  //////////////////////////////////////////////////////////////////////////////

  def matchClauseSimple(fixedState : AbstractState,
                        initialAssumptions : Conjunction,
                        clause : NormClause,
                        fixedIndex : Int, occ : Int,
                        byStates : Array[Seq[AbstractState]]) : Unit = {
    import TerForConvenience._
    implicit val _ = clause.order

    val NormClause(constraint, body, head) = clause

    def findPreStates(i : Int,
                      chosenStates : List[AbstractState],
                      assumptions : Conjunction) : Unit =
      if (i < 0) {
        nextToProcess.enqueue(chosenStates, clause, assumptions)
      } else if (i == fixedIndex) {
        findPreStates(i - 1, fixedState :: chosenStates, assumptions)
      } else {
        val (_, occ) = body(i)
        for (state <- byStates(i)) {
          val newAssumptions =
            sf.reduce(conj(List(assumptions) ++ (state instances occ)))
          if (!newAssumptions.isFalse)
            findPreStates(i - 1, state :: chosenStates, newAssumptions)
        }
      }

    findPreStates(body.size - 1, List(), initialAssumptions)
  }

  //////////////////////////////////////////////////////////////////////////////

  def matchClausePrereduce(state : AbstractState,
                           initialAssumptions : Conjunction,
                           clause : NormClause,
                           fixedIndex : Int, occ : Int,
                           byStates : Array[Seq[AbstractState]]) : Unit = {
    import TerForConvenience._
    implicit val _ = clause.order

    val NormClause(constraint, body, head) = clause

    val relevantRS =
      (for (p@(t, i) <- body.iterator.zipWithIndex;
            if (i != fixedIndex)) yield p).toSeq.sortBy {
        case (_, i) => byStates(i).size
      }

    var currentAssumptions = initialAssumptions
    var preReducer = sf reducer currentAssumptions

    var foundInconsistency = false
    val availableStates =
      (for (((rs, occ), i) <- relevantRS.iterator; if (!foundInconsistency)) yield {
         val states =
           (for (s <- byStates(i).iterator;
                 simp = preReducer(s predConjunction occ);
                 if (!simp.isFalse)) yield (s, simp)).toArray
         if (states.isEmpty) {
           foundInconsistency = true
         } else if (states.size == 1) {
           currentAssumptions = sf reduce conj(List(currentAssumptions, states(0)._2))
           if (currentAssumptions.isFalse)
             foundInconsistency = true
           else
             preReducer = sf reducer currentAssumptions
         }
         (states, i)
       }).toArray

    if (foundInconsistency)
      return

/*
    {
      val tableSize = body.size
      val statesTable =
        Array.ofDim[Array[(List[AbstractState], Conjunction)]](tableSize)
      statesTable(fixedIndex) = Array((List(state), Conjunction.TRUE))

      for ((x, i) <- availableStates)
        statesTable(i) = for ((s, simp) <- x) yield (List(s), simp)

      var stride = 1
      while (2 * stride < tableSize) {
        var index = 0
        while (index + stride < tableSize) {
          val states1 = statesTable(index)
          val states2 = statesTable(index + stride)
          statesTable(index) =
            (for ((s1, simp1) <- states1.iterator;
                  (s2, simp2) <- states2.iterator;
                  simp =
                    if (simp1.isTrue)
                      simp2
                    else if (simp2.isTrue)
                      simp1
                    else
                      preReducer(conj(List(simp1, simp2)));
                  if (!simp.isFalse))
             yield (s1 ++ s2, simp)).toArray
          index = index + 2 * stride
        }
        stride = stride * 2
      }

      for ((chosenStates1, simp1) <- statesTable(0);
           (chosenStates2, simp2) <- statesTable(stride)) {
        val allAssumptions =
          sf.reduce(conj(List(currentAssumptions, simp1, simp2)))
        if (!allAssumptions.isFalse) {
          val allChosenStates = chosenStates1 ++ chosenStates2
          nextToProcess.enqueue(allChosenStates, clause, allAssumptions)
        }
      }
    }
*/

    Sorting.stableSort(availableStates,
                       (x : (Array[(AbstractState, Conjunction)], Int)) => x._1.size)

    val chosenStates = Array.ofDim[AbstractState](clause.body.size)
    chosenStates(fixedIndex) = state

    val N = availableStates.size

    def findPreStates(i : Int,
                      assumptions : Conjunction) : Unit =
      if (i == N) {
        val cs = chosenStates.toList
        nextToProcess.enqueue(cs, clause, assumptions)
      } else {
        val (candidates, bodyNum) = availableStates(i)
        if (candidates.size == 1) {
          // the constraint has already been taken into account
          chosenStates(bodyNum) = candidates(0)._1
          findPreStates(i + 1, assumptions)
        } else {
          for ((state, simpStatePreds) <- candidates) {
            val newAssumptions =
              sf.reduce(conj(List(assumptions, simpStatePreds)))
            if (!newAssumptions.isFalse) {
              chosenStates(bodyNum) = state
              findPreStates(i + 1, newAssumptions)
            }
          }
        }
      }
    
    findPreStates(0, currentAssumptions)

  }

  //////////////////////////////////////////////////////////////////////////////

/*
  def matchClauseGlobal(state : AbstractState,
                        initialAssumptions : Conjunction,
                        clause : NormClause,
                        fixedIndex : Int, fixedOcc : Int,
                        combinationsDone : MHashSet[(Seq[AbstractState], NormClause)])
                       : Unit = inferenceAPIProver.scope {
    val p = inferenceAPIProver
    import p._
    import TerForConvenience._

    val rs = state.rs

    val NormClause(constraint, body, head) = clause

    addConstants(clause.order sort clause.order.orderedConstants)
    addAssertion(initialAssumptions)

    // add assertions for the possible matches
    val selectors =
      (for (((brs, occ), i) <- body.iterator.zipWithIndex)
       yield if (i == fixedIndex) {
         List()
       } else {
         val flags = createBooleanVariables(activeAbstractStates(brs).size)

         implicit val _ = order
         addAssertion(
           disj(for ((s, IAtom(p, _)) <-
                       activeAbstractStates(brs).iterator zip flags.iterator)
                  yield conj((s instances occ) ++ List(p(List())))))
         flags
       }).toIndexedSeq

     implicit val _ = order

     while (??? == ProverStatus.Sat) {
       val (chosenStates, assumptionSeq, sels) =
         (for (((brs, occ), i) <- body.iterator.zipWithIndex) yield
            if (i == fixedIndex) {
              (state, state instances occ, IExpression.i(true))
            } else {
              val selNum = selectors(i) indexWhere (evalPartial(_) == Some(true))
              val selState = activeAbstractStates(brs).iterator.drop(selNum).next
              (selState, selState instances occ, selectors(i)(selNum))
            }).toList.unzip3

       if (combinationsDone add (chosenStates, clause))
         nextToProcess.enqueue(chosenStates, clause,
           conj((for (l <- assumptionSeq.iterator; f <- l.iterator) yield f) ++ (
                  Iterator single constraint))
         )

       val blockingClause = !conj(for (IAtom(p, _) <- sels.iterator) yield p(List()))

       addAssertion(blockingClause)
     }
  }
*/

  //////////////////////////////////////////////////////////////////////////////

  def subsumes(a : AbstractState, b : AbstractState) : Boolean =
    a.rs == b.rs &&
    (a.preds.size <= b.preds.size) &&
    (a.predHashCodeSet subsetOf b.predHashCodeSet) &&
    (a.predSet subsetOf b.predSet)

  def strictlySubsumes(a : AbstractState, b : AbstractState) : Boolean =
    (a.predSet.size < b.predSet.size) && subsumes(a, b)

  //////////////////////////////////////////////////////////////////////////////

  def genEdge(clause : NormClause,
              from : Seq[AbstractState], assumptions : Conjunction) = {
    val startTime = System.currentTimeMillis
    lazy val prover = emptyProver.assert(assumptions, clause.order)

    hasher.scope {
      addHasherAssertions(clause, from)
      val hasherSat = hasher.isSat

      val valid =
        if (hasherSat) {
          hasherChecksHit = hasherChecksHit + 1
          false
        } else {
          val res = isValid(prover)
          if (!res)
            hasherChecksMiss = hasherChecksMiss + 1
          res
        }
    
      implicationChecks = implicationChecks + 1
      implicationChecksSetup = implicationChecksSetup + 1
      implicationChecksSetupTime =
        implicationChecksSetupTime + (System.currentTimeMillis - startTime)

      if (valid) {
        // assumptions are inconsistent, nothing to do
        None
      } else {
        // assumptions are consistent
        clause.head._1.pred match {
          case HornClauses.FALSE =>
            throw new Counterexample(from, clause)
          case _ => {
            val state = genAbstractState(assumptions,
                                         clause.head._1, clause.head._2,
                                         prover, clause.order)
            Some(AbstractEdge(from, state, clause, assumptions))
          }
        }
      }
    }
  }

  case class Counterexample(from : Seq[AbstractState], clause : NormClause)
             extends Exception("Predicate abstraction counterexample")
  
  def genAbstractState(assumptions : Conjunction,
                       rs : RelationSymbol, rsOcc : Int,
                       prover : => ModelSearchProver.IncProver,
                       order : TermOrder) : AbstractState = {
    val startTime = System.currentTimeMillis
    val reducer = sf reducer assumptions
    implicationChecksSetupTime =
      implicationChecksSetupTime + (System.currentTimeMillis - startTime)
    
    val predConsequences =
      (for (pred <- predicates(rs).iterator;
            if predIsConsequenceWithHasher(pred, rsOcc,
                                           reducer, prover, order))
       yield pred).toVector
    AbstractState(rs, predConsequences)
  }
  
  def predIsConsequenceWithHasher(pred : RelationSymbolPred, rsOcc : Int,
                                  reducer : ReduceWithConjunction,
                                  prover : => ModelSearchProver.IncProver,
                                  order : TermOrder) : Boolean = {
    val hasherId = predicateHashIndexes(pred.rs)(pred.predIndex)(rsOcc)

    if (hasher mightBeImplied hasherId) {
      val res = predIsConsequence(pred, rsOcc, reducer, prover, order)
      if (!res)
        hasherChecksMiss = hasherChecksMiss + 1
      res
    } else {
      hasherChecksHit = hasherChecksHit + 1
      false
    }
  }

  def predIsConsequence(pred : RelationSymbolPred, rsOcc : Int,
                        reducer : ReduceWithConjunction,
                        prover : => ModelSearchProver.IncProver,
                        order : TermOrder) : Boolean = {
    val startTime = System.currentTimeMillis
    implicationChecks = implicationChecks + 1
    val reducedInstance = reducer.tentativeReduce(pred posInstances rsOcc)

    val res =
      !reducedInstance.isFalse &&
      (reducedInstance.isTrue ||
       isValid(prover.conclude(reducedInstance, order)))

    if (res) {
      implicationChecksPos = implicationChecksPos + 1
      implicationChecksPosTime =
        implicationChecksPosTime + (System.currentTimeMillis - startTime)
    } else {
      implicationChecksNeg = implicationChecksNeg + 1
      implicationChecksNegTime =
        implicationChecksNegTime + (System.currentTimeMillis - startTime)
    }

    res
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def extractCounterexample(from : Seq[AbstractState], clause : NormClause)
                           : Dag[AndOrNode[NormClause, Unit]] = {
    // find minimal paths to reach the abstract states
    val distances = new MHashMap[AbstractState, Int]
    
    def maxDistance(states : Iterable[AbstractState]) =
      Seqs.max(states.iterator map (distances.getOrElse(_, Integer.MAX_VALUE / 2)))

    def maxDistancePlus1(states : Iterable[AbstractState]) =
      if (states.isEmpty) 0 else (maxDistance(states) + 1)
    
    var changed = true
    while (changed) {
      changed = false
      
      for (AbstractEdge(from, to, _, _) <- abstractEdges)
        if (from.isEmpty) {
          distances.put(to, 0)
        } else {
          val oldDist = distances.getOrElse(to, Integer.MAX_VALUE)
          val newDist = maxDistance(from) + 1
          if (newDist < oldDist) {
            distances.put(to, newDist)
            changed = true
          }
        }
    }

    val cex = counterexampleMethod match {

      //////////////////////////////////////////////////////////////////////////

      case CounterexampleMethod.FirstBestShortest => {
        var cex : Dag[AndOrNode[NormClause, Unit]] = DagEmpty
        val cexNodes = new MHashMap[AbstractState, Int]

        def addStateToDag(s : AbstractState) : Unit =
          if (!(cexNodes contains s)) {
            val AbstractEdge(from, _, clause, _) =
              Seqs.min(for (e@AbstractEdge(_, `s`, _, _) <- abstractEdges.iterator) yield e,
                       (e:AbstractEdge) => maxDistancePlus1(e.from))
            for (t <- from) addStateToDag(t)
            assert(!(cexNodes contains s))
            cexNodes.put(s, cex.size)
            cex = DagNode(AndNode(clause),
                          (for (t <- from.iterator) yield (cex.size - cexNodes(t))).toList,
                          cex)
        }

        for (t <- from) addStateToDag(t)
        cex = DagNode(AndNode(clause),
                      (for (t <- from.iterator) yield (cex.size - cexNodes(t))).toList,
                      cex)
        cex
      }

      //////////////////////////////////////////////////////////////////////////

      case CounterexampleMethod.AllShortest |
           CounterexampleMethod.RandomShortest |
           CounterexampleMethod.MaxNOrShortest => {
        var cex : Dag[AndOrNode[NormClause, Unit]] = DagEmpty
        var orNum = 0
        val cexNodes = new MHashMap[AbstractState, Int]

        def addStateToDag(s : AbstractState) : Unit =
          if (!(cexNodes contains s)) {
            val minDistance =
              (for (AbstractEdge(from, `s`, _, _) <- abstractEdges.iterator)
               yield maxDistancePlus1(from)).min
            val minEdges =
              for (e@AbstractEdge(from, `s`, _, _) <- abstractEdges;
                   if (maxDistancePlus1(from) == minDistance)) yield e

            val selectedEdges = counterexampleMethod match {
              case CounterexampleMethod.AllShortest |
                   CounterexampleMethod.MaxNOrShortest =>
                minEdges
              case CounterexampleMethod.RandomShortest =>
                List(minEdges(rand nextInt minEdges.size))
            }

            // recursively add all the children
            val definedEdges = 
              (for ((e@AbstractEdge(from, _, _, _), i) <-
                       selectedEdges.iterator.zipWithIndex;
                    if (i == 0 ||
                        counterexampleMethod != CounterexampleMethod.MaxNOrShortest ||
                        orNum < MaxNOr)) yield {
                 for (t <- from)
                   addStateToDag(t)
                 e
               }).toList

            val definedEdges2 = counterexampleMethod match {
              case CounterexampleMethod.MaxNOrShortest if (orNum >= MaxNOr) =>
                List(definedEdges.head)
              case _ =>
                definedEdges
            }

            for (AbstractEdge(from, _, clause, _) <- definedEdges2)
              cex = DagNode(AndNode(clause),
                            (for (t <- from.iterator) yield (cex.size - cexNodes(t))).toList,
                            cex)

            assert(!(cexNodes contains s))
            if (definedEdges2.size == 1) {
              cexNodes.put(s, cex.size - 1)
            } else {
              cexNodes.put(s, cex.size)
              cex = DagNode(OrNode(()), (1 to definedEdges2.size).toList, cex)
              orNum = orNum + 1
            }
        }

        for (t <- from) addStateToDag(t)
        cex = DagNode(AndNode(clause),
                      (for (t <- from.iterator) yield (cex.size - cexNodes(t))).toList,
                      cex)

        counterexampleMethod match {
          case CounterexampleMethod.MaxNOrShortest =>
            // then the counterexample might contain unconnected stuff
            cex.elimUnconnectedNodes
          case _ =>
            cex
        }
      }

      //////////////////////////////////////////////////////////////////////////
      
    }

//    println
//    cex.prettyPrint

    cex
  }
  
  //////////////////////////////////////////////////////////////////////////////

  def addPredicates(preds : Seq[(Predicate, Seq[Conjunction])]) = {
    val predsToAdd =
      new MHashMap[RelationSymbol, IndexedSeq[RelationSymbolPred]]

    for ((p, fors) <- preds) {
      val rs = relationSymbols(p)
      val subst = VariableSubst(0, rs.arguments.head, sf.order)
      val rsReducer = relationSymbolReducers(rs)

      val rsPreds =
        (for (f <- fors.iterator;
              substF2 = rsReducer(subst(f));
              substF <- splitPredicate(substF2);
              if (reallyAddPredicate(substF, rs));
              pred = genSymbolPred(substF, rs);
              if (!(predicates(rs) exists
                      (_.rawPred == pred.rawPred)))) yield {
           addRelationSymbolPred(pred)
           pred
         }).toVector

      if (!rsPreds.isEmpty) {
        if (lazabs.GlobalParameters.get.log) {
          print(p.name + ": ")
          println(rsPreds mkString ", ")
        }
        predsToAdd.put(rs, rsPreds)
      }
    }

    // update the edges of the reachability graph with the new predicates;
    // but only consider the edges that will still be reachable afterwards

    val edgesFromState =
      (for (n <- 0 until abstractEdges.size;
            AbstractEdge(from, _, _, _) = abstractEdges(n);
            s <- from)
       yield (s, n)) groupBy (_._1)

    val newStates = new ArrayBuffer[AbstractState]
    val reachable = new MHashSet[AbstractState]

    val edgesDone = new MHashSet[Int]
    val edgesTodo = new ArrayStack[Int]
    
    for (n <- 0 until abstractEdges.size)
      if (abstractEdges(n).from.isEmpty)
        edgesTodo += n

    while (!edgesTodo.isEmpty) {
      val n = edgesTodo.pop

      if (!(edgesDone contains n)) {
        val AbstractEdge(from, to, clause, assumptions) = abstractEdges(n)
        if (from forall reachable) {
          edgesDone += n

          for (rsPreds <- predsToAdd get to.rs) hasher.scope {
            addHasherAssertions(clause, from)
            lazy val prover = emptyProver.assert(assumptions, clause.order)
            val reducer = sf reducer assumptions
            
            val additionalPreds =
              for (pred <- rsPreds;
                   if predIsConsequenceWithHasher(pred, clause.head._2,
                                                  reducer, prover,
                                                  clause.order))
              yield pred
                
            if (!additionalPreds.isEmpty) {
              val newS = AbstractState(to.rs, to.preds ++ additionalPreds)
              newStates += newS
              abstractEdges(n) = AbstractEdge(from, newS, clause, assumptions)
//              print("/")
//              println("Updating edge: " + abstractEdges(n))
            }
          }
        
          val newTo = abstractEdges(n).to
          reachable += newTo

          for (outgoing <- edgesFromState get newTo)
            for ((_, nextN) <- outgoing)
              edgesTodo += nextN
        }
      }
    }

    // Garbage collection; determine whether previously subsumed
    // states have become unsubsumed

    val (forwardUnsubsumedStates,
         backwardUnsubsumedStates) = removeGarbage(reachable)

    for (s <- backwardUnsubsumedStates)
      (activeAbstractStates(s.rs) find { t => strictlySubsumes(t, s) }) match {
        case Some(subsumingState) =>
          backwardSubsumedStates.put(s, subsumingState)
        case None =>
          maxAbstractStates(s.rs) += s
      }

    for (s <- forwardUnsubsumedStates.toSeq sortBy (_.preds.size))
      addState(s)
    for (s <- newStates)
      if (reachable contains s)
        addState(s)

    // Postponed expansions might have to be reactivated

    val (remainingExp, reactivatedExp) =
      postponedExpansions partition (_._1 exists (backwardSubsumedStates contains _))
    postponedExpansions reduceToSize 0
    postponedExpansions ++= remainingExp

    for ((states, clause, assumptions, time) <- reactivatedExp)
      nextToProcess.enqueue(states, clause, assumptions, time)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Split a new predicate into conjuncts, which can be treated
   * then as separate predicates.
   */
  def splitPredicate(f : Conjunction) : Iterator[Conjunction] =
    if (f.quans.isEmpty)
      f.iterator
    else
      Iterator single f

  def reallyAddPredicate(f : Conjunction,
                         rs : RelationSymbol) : Boolean =
    !f.isFalse && !f.isTrue &&
    !(predicates(rs) exists (_.rawPred == f)) && {
      // check whether the predicate is subsumed by older predicates
      val reducer = sf reducer f
      val impliedPreds =
        for (p <- predicates(rs); if (reducer(p.rawPred).isTrue))
        yield p.positive

      impliedPreds.isEmpty || {
        import TerForConvenience._
        implicit val _ = sf.order
        val c = sf reduce conj(impliedPreds)
        !((sf reducer c)(f).isTrue)
      }
    }

  def elimQuansIfNecessary(c : Conjunction, positive : Boolean) : Conjunction =
    if (ap.terfor.conjunctions.IterativeClauseMatcher.isMatchableRec(
           if (positive) c else c.negate, Map())) {
      c
    } else {
      val newC = PresburgerTools.elimQuantifiersWithPreds(c)
      if (!ap.terfor.conjunctions.IterativeClauseMatcher.isMatchableRec(
              if (positive) newC else newC.negate, Map()))
        throw new Exception("Cannot handle general quantifiers in predicates at the moment")
      newC
    }

  def rsPredsToInternal(f : IFormula)
                     : (Conjunction, Conjunction, Conjunction) = {
    val rawF = sf.toInternalClausify(f)
    val posF = elimQuansIfNecessary(sf.preprocess(
                                      sf.toInternalClausify(~f)).negate, true)
    val negF = elimQuansIfNecessary(sf.preprocess(
                                      rawF), false)
    (rawF, posF, negF)
  }

  def genSymbolPred(f : Conjunction,
                    rs : RelationSymbol) : RelationSymbolPred =
    if (Seqs.disjoint(f.predicates, sf.functionalPreds)) {
      RelationSymbolPred(f, f, f, rs, predicates(rs).size)
    } else {
      // some simplification, to avoid quantifiers in predicates
      // as far as possible, or at least provide good triggers
/*      println(f)
      val prenex = PresburgerTools toPrenex f
      println(" -> " + prenex)
      val cnf = (PresburgerTools toDNF prenex.unquantify(prenex.quans.size).negate).negate
      val complete = sf reduce Conjunction.quantify(prenex.quans, cnf, f.order)
      println(" -> " + complete) */

      val iabsy =
        (new Simplifier)(Internal2InputAbsy(f, sf.functionEnc.predTranslation))

      val (rawF, posF, negF) = rsPredsToInternal(iabsy)

//      println(" -> pos: " + posF)
//      println(" -> neg: " + negF)

      RelationSymbolPred(rawF, posF, negF, rs, predicates(rs).size)
    }

  //////////////////////////////////////////////////////////////////////////////

  def removeGarbage(reachable : MHashSet[AbstractState])
                 : (Iterable[AbstractState], Iterable[AbstractState]) = {
    val remainingEdges = for (e@AbstractEdge(from, to, _, _) <- abstractEdges;
                              if (from forall reachable))
                         yield e
    abstractEdges reduceToSize 0
    abstractEdges ++= remainingEdges
    
    for ((_, preds) <- activeAbstractStates)
      preds retain reachable
    for ((_, preds) <- maxAbstractStates)
      preds retain reachable
    
    nextToProcess removeGarbage reachable

    // Remove garbage from postponed expansion steps

    val remainingPostponedExpansions =
      for (exp@(from, _, _, _) <- postponedExpansions;
           if (from forall reachable))
      yield exp
    postponedExpansions reduceToSize 0
    postponedExpansions ++= remainingPostponedExpansions

    // Previously subsumed states might become relevant again

    val forwardUnsubsumedStates, backwardUnsubsumedStates =
      new ArrayBuffer[AbstractState]
    val remainingSubsumedStates =
      new ArrayBuffer[(AbstractState, AbstractState)]

    for (p@(state, subsumingState) <- forwardSubsumedStates)
      if (reachable contains state) {
        if (reachable contains subsumingState)
          remainingSubsumedStates += p
        else
          forwardUnsubsumedStates += state
      }

    forwardSubsumedStates.clear
    forwardSubsumedStates ++= remainingSubsumedStates

    remainingSubsumedStates.clear

    for (p@(state, subsumingState) <- backwardSubsumedStates)
      if (reachable contains state) {
        if (reachable contains subsumingState)
          remainingSubsumedStates += p
        else
          backwardUnsubsumedStates += state
      }

    backwardSubsumedStates.clear
    backwardSubsumedStates ++= remainingSubsumedStates

    (forwardUnsubsumedStates, backwardUnsubsumedStates)
  }
  
}

