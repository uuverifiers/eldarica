/**
 * Copyright (c) 2026 Zafer Esen, Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.symex

import ap.basetypes.IdealInt
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.TerForConvenience._
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.linearcombination.LinearCombination.{SingleTerm,
                                                     TwoTermsWithOffset}
import ap.terfor.preds.{Atom, Predicate}
import ap.terfor.substitutions.ConstantSubst
import ap.util.{Debug, Seqs}
import lazabs.horn.bottomup.RelationSymbol

import java.util.Arrays

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap,
                                 HashSet => MHashSet}

/**
 * How a symbol in a [[DefinitionKey]] is given: an argument by its index,
 * a local by its definition or, without one, by its rank, and the local
 * defined by the key as SelfToken.
 */
sealed trait SymToken
case class ArgToken(index : Int) extends SymToken
case class DefinedToken(id : DefinitionId) extends SymToken
case class RankedToken(rank : Int) extends SymToken
case object SelfToken extends SymToken

// a linear combination with its symbols given by their tokens
case class TokenTerm(terms : Seq[(SymToken, IdealInt)], constant : IdealInt)

object DefinitionKind extends Enumeration {
  val Result, Equation, Operand = Value
}

/**
 * A literal or equation by which a local is defined, with its symbols by
 * their tokens: a literal whose result the local is, an equation, or a
 * literal with the local among its operands.
 * E.g., c is defined by (Result, bv_extract, (3, 0, x)) in
 * bv_extract(3, 0, x, c), by (Equation, (2 self - x)) in 2c - x = 0, and by
 * (Operand, bv_extract, (31, 0, self, x)) in bv_extract(31, 0, c, x).
 */
case class DefinitionKey(kind : DefinitionKind.Value,
                         pred : Option[Predicate],
                         args : Seq[TokenTerm])

/**
 * A key and how many locals of the same constraint it defined before,
 * since a literal need not determine its operands.
 * E.g., c and d in bv_extract(31, 0, c, x) & bv_extract(31, 0, d, x) get
 * the instances 0 and 1 of one key.
 */
case class DefinitionId(key : DefinitionKey, instance : Int)

/**
 * Normalizes constraints so that they can be checked for structural
 * equivalence. For instance for cheap hash lookups, subsumption checks etc.
 * E.g., bv_extract(0,0,a,b) and bv_extract(0,0,a,c), after
 * normalization b and c get the same symbol.
 * - A local defined by a literal or equation gets the symbol of that
 *   [[DefinitionId]], the same in every constraint, so that it keeps its
 *   symbol in a constraint with more conjuncts. In every other literal or
 *   equation by which it can be defined, it gets that one's symbol, equated
 *   to its own.
 * - The other locals are ranked by the structure of the constraint and get
 *   symbols by rank, e.g., p_c_0_0, p_c_0_1 etc.
 */
object ConstraintNormalizer {

  private object AC extends Debug.ASSERTION_CATEGORY

  /**
   * Normalizes a constraint with theory literals using its structure.
   * @param args       The arguments of the atoms, which keep their symbols.
   * @param constraint The constraint to be normalized.
   * @param newSyms    newSyms(n) gives n new symbols and the term order with
   *                   them; the locals get them in the order in which they
   *                   are placed.
   * @param definedSym The symbol of a definition id. Without it, every
   *                   local gets a symbol from newSyms.
   * @return           The normalized constraint.
   */
  def normalize(args       : Seq[ConstantTerm],
                constraint : Conjunction,
                newSyms    : Int => (Seq[ConstantTerm], TermOrder),
                definedSym : Option[DefinitionId => ConstantTerm] = None)
  : Conjunction =
    if (constraint.constants subsetOf args.toSet) {
      ConstantSubst(Map(), newSyms(0)._2)(constraint)
    } else {
      val placement = new LocalPlacement(args, constraint)
      definedSym match {
        case None =>
          renameByPositions(constraint, placement, newSyms)
        case Some(symOfId) =>
          renameByDefinitions(args, constraint, placement, newSyms, symOfId)
      }
    }

  private def renameByPositions(
      constraint : Conjunction,
      placement  : LocalPlacement,
      newSyms    : Int => (Seq[ConstantTerm], TermOrder)) : Conjunction = {
    val (syms, order) = newSyms(placement.placedLocals.size)
    // the last placed local gets the first symbol
    ConstantSubst((placement.placedLocals.reverse zip syms).toMap, order)(
      constraint)
  }

  private def renameByDefinitions(
      args       : Seq[ConstantTerm],
      constraint : Conjunction,
      placement  : LocalPlacement,
      newSyms    : Int => (Seq[ConstantTerm], TermOrder),
      symOfId    : DefinitionId => ConstantTerm) : Conjunction = {
    val definedSyms =
      for ((local, DefinedToken(id)) <- placement.localTokens)
        yield (local, symOfId(id))
    val furtherDefinitionSyms =
      for (further <- placement.furtherDefinitions)
        yield (further, symOfId(further.id))
    // taken after the defined symbols are made, so that it has them
    val (rankedSyms, order) = newSyms(placement.rankedCount)
    val symOf = definedSyms.toMap ++
      (for ((local, RankedToken(rank)) <- placement.localTokens)
         yield (local, rankedSyms(placement.rankedCount - 1 - rank)))
    Debug.assertInt(AC, {
      val syms = symOf.values.toSeq ++ furtherDefinitionSyms.map(_._2)
      syms.distinct.size == syms.size && !(syms exists args.contains)
    })
    if (furtherDefinitionSyms.isEmpty) {
      ConstantSubst(symOf, order)(constraint)
    } else {
      implicit val o : TermOrder = order
      val furtherSymOf =
        (for ((further, sym) <- furtherDefinitionSyms)
           yield (further.conjunct, (further.local, sym))).toMap
      def definingConjunctOf(conjunct : Conjunction)
      : Option[DefiningConjunct] =
        if (!conjunct.isLiteral) None
        else if (conjunct.predConj.positiveLits.size == 1)
          Some(DefiningLiteral(conjunct.predConj.positiveLits.head))
        else if (conjunct.arithConj.positiveEqs.size == 1)
          Some(DefiningEquation(conjunct.arithConj.positiveEqs.head))
        else None
      val renamedConjuncts =
        for (conjunct <- constraint.iterator.toList) yield {
          val renaming =
            definingConjunctOf(conjunct) flatMap furtherSymOf.get match {
              case Some((local, sym)) => symOf + (local -> sym)
              case None               => symOf
            }
          ConstantSubst(renaming, order)(conjunct)
        }
      val equations =
        for ((further, sym) <- furtherDefinitionSyms)
          yield l(sym) === l(symOf(further.local))
      // reduced by its equations, as the stored constraints are, so that the
      // reducer can use it as an assumption
      ReduceWithConjunction(Conjunction.TRUE, order)(
        Conjunction.conj(renamedConjuncts ++ equations, order))
    }
  }

  /**
   * Normalizes a goal. Goals that differ only in the order and occurrences
   * of their atoms and in the symbols of their locals get one normal form.
   * E.g. with xi the argument of P at occurrence i both
   *   false :- P(x1), P(x0), x0 = 1 & x1 = 2
   *   false :- P(x0), P(x1), x1 = 1 & x0 = 2
   * become false :- P(x0), P(x1), x0 = 1 & x1 = 2
   * because in the ConstraintGraph the atom whose argument is 1 gets the
   * smaller colour and so occurrence 0.
   */
  def normalizeGoal(goal    : GoalClause,
                    newSyms : Int => (Seq[ConstantTerm], TermOrder))
  : GoalClause = {
    Debug.assertPre(AC, goal.atoms.distinct.size == goal.atoms.size)
    val orderedAtoms = canonicalAtomOrder(goal)
    val nextOccurrence = new MHashMap[RelationSymbol, Int]
    val renumberedAtoms = for ((rs, _) <- orderedAtoms) yield {
      val occ = nextOccurrence.getOrElse(rs, 0)
      nextOccurrence(rs) = occ + 1
      (rs, occ)
    }
    def argsOf(atoms : Seq[(RelationSymbol, Int)]) : Seq[ConstantTerm] =
      for ((rs, occ) <- atoms; arg <- rs.arguments(occ)) yield arg
    val oldArgs = argsOf(orderedAtoms)
    // forced before the order is taken from newSyms, so that it has them
    val newArgs = argsOf(renumberedAtoms)
    val locals = goal.constraint.constants -- oldArgs
    val (pool, order) = newSyms(locals.size)
    // the locals are moved onto the pool too, so that none of them is
    // captured by the renumbering
    val renumberedConstraint = ConstantSubst(
      ((oldArgs zip newArgs) ++ (order.sort(locals) zip pool)).toMap,
      order)(goal.constraint)
    GoalClause(renumberedAtoms,
               normalize(newArgs, renumberedConstraint, newSyms))
  }

  private def canonicalAtomOrder(goal : GoalClause)
  : Seq[(RelationSymbol, Int)] = {
    val atoms = goal.atoms.toIndexedSeq
    val predicateRepeats = atoms.map(_._1).distinct.size < atoms.size
    if (predicateRepeats) {
      val colouring = new GraphColouring(new ConstraintGraph(
        goal.constraint,
        for ((rs, occ) <- atoms) yield (rs.pred, rs.arguments(occ))))
      colouring.refine()
      val byPredicateColourOccurrence = Ordering.Tuple3(
        ConstraintGraph.predicateOrdering, Ordering.Int, Ordering.Int)
      val unplacedAtoms = ArrayBuffer(atoms.indices : _*)
      val placedAtoms = new ArrayBuffer[Int]
      while (unplacedAtoms.nonEmpty) {
        // ties are broken by occurrence: deterministic, but canonical only if
        // the tied atoms are interchangeable
        val atom = unplacedAtoms.minBy { i =>
          val (rs, occ) = atoms(i)
          (rs.pred, colouring.colourOfAtom(i), occ)
        }(byPredicateColourOccurrence)
        unplacedAtoms -= atom
        placedAtoms += atom
        // like a tied symbol, a tied atom is individualised, so that the
        // rest are ordered relative to it
        val colour = colouring.colourOfAtom(atom)
        if (unplacedAtoms exists (colouring.colourOfAtom(_) == colour)) {
          colouring.individualiseAtom(atom)
          colouring.refine()
        }
      }
      placedAtoms map atoms
    } else {
      atoms.sortBy(_._1.pred)(ConstraintGraph.predicateOrdering)
    }
  }

  // A positive literal or an equation with locals, by which the last of its
  // symbols to be placed is defined. Difference equations are not defining
  // conjuncts: their members are defined through their classes.
  private sealed trait DefiningConjunct {
    val syms : Set[ConstantTerm]
  }
  private case class DefiningLiteral(atom : Atom) extends DefiningConjunct {
    val syms = atom.constants
  }
  private case class DefiningEquation(lhs : LinearCombination)
      extends DefiningConjunct {
    val syms = lhs.constants
  }

  private case class FurtherDefinition(conjunct : DefiningConjunct,
                                       local    : ConstantTerm,
                                       id       : DefinitionId)

  /**
   * The placement of the locals of a constraint, one at a time: of the
   * defining conjuncts whose other symbols are placed, the one with the
   * smallest key defines its local; without one, the next local is chosen
   * by colour refinement and ranked. A local with further defining conjuncts
   * gets the id of each further definition in its conjunct.
   * E.g., in bv_extract(3, 0, x, c) & bv_extract(7, 4, y, c), c is defined
   * by (Result, bv_extract, (3, 0, x)), and in the second literal by
   * (Result, bv_extract, (7, 4, y)).
   */
  private class LocalPlacement(args       : Seq[ConstantTerm],
                               constraint : Conjunction) {
    import DefinitionKind._
    import ConstraintGraph.DifferenceEquation

    private val tokenOf = new MHashMap[ConstantTerm, SymToken]
    for ((sym, index) <- args.zipWithIndex)
      tokenOf(sym) = ArgToken(index)

    val placedLocals = new ArrayBuffer[ConstantTerm]
    var rankedCount = 0

    def localTokens : Seq[(ConstantTerm, SymToken)] =
      for (local <- placedLocals) yield (local, tokenOf(local))

    private val instanceCounts = new MHashMap[DefinitionKey, Int]
    private def nextId(key : DefinitionKey) : DefinitionId = {
      val instance = instanceCounts.getOrElse(key, 0)
      instanceCounts(key) = instance + 1
      DefinitionId(key, instance)
    }

    private def canDefineLocal(conjunct : DefiningConjunct) : Boolean =
      conjunct.syms.size > 1 && !(conjunct.syms subsetOf tokenOf.keySet)

    // Equations are stored row-reduced along the term order: an equality
    // class of difference equations as a star of members around a pivot, at
    // offsets above it. Which member is the pivot depends on the term order,
    // so once a member is placed, the others are defined relative to it.
    // E.g., with x an argument, c - x = 0 and d - x - 1 = 0 define c and d by
    // (Equation, (self - x)) and (Equation, (self - x - 1)).
    private val classOf : Map[ConstantTerm, (ConstantTerm, IdealInt)] = {
      val members =
        for (DifferenceEquation(member, pivot, offset) <-
               constraint.arithConj.positiveEqs.toList)
          yield (member, (pivot, offset))
      val pivots =
        for ((_, (pivot, _)) <- members) yield (pivot, (pivot, IdealInt.ZERO))
      (pivots ++ members).toMap
    }
    private val membersOfClass : Map[ConstantTerm, Seq[ConstantTerm]] =
      classOf.keys.toSeq.groupBy(classOf(_)._1)
    private val classesWithPlacedMember = new MHashSet[ConstantTerm]

    // the members of the class of sym, defined relative to sym
    private def classMembersDefinedBy(sym : ConstantTerm)
    : Seq[(DefinitionKey, ConstantTerm, Option[DefiningConjunct])] =
      classOf get sym match {
        case Some((pivot, offset)) if classesWithPlacedMember add pivot =>
          for (member <- membersOfClass(pivot) if !(tokenOf contains member))
            yield (DefinitionKey(Equation, None, List(TokenTerm(
                     List((tokenOf(sym), IdealInt.MINUS_ONE),
                          (SelfToken, IdealInt.ONE))
                       .sorted(tokenCoeffOrdering),
                     offset - classOf(member)._2))),
                   member, None)
        case _ =>
          Nil
      }

    private def keyOf(conjunct : DefiningConjunct,
                      local    : ConstantTerm) : DefinitionKey = {
      def tokenTerm(lc : LinearCombination) = TokenTerm(
        (for ((coeff, sym : ConstantTerm) <- lc.toList)
           yield (if (sym == local) SelfToken else tokenOf(sym), coeff))
          .sorted(tokenCoeffOrdering),
        lc.constant)
      conjunct match {
        case DefiningLiteral(atom) =>
          if (resultSym(atom) == Some(local) &&
              !(atom.init exists (_.constants contains local)))
            DefinitionKey(Result, Some(atom.pred), atom.init map tokenTerm)
          else
            DefinitionKey(Operand, Some(atom.pred), atom map tokenTerm)
        case DefiningEquation(lhs) =>
          DefinitionKey(Equation, None,
                        List(tokenTerm(if (lhs.get(local).signum < 0) -lhs
                                       else lhs)))
      }
    }

    // used only when no definition is ready, and for ties
    private lazy val colouring = {
      val colouring = new GraphColouring(new ConstraintGraph(constraint))
      args foreach colouring.individualise
      colouring
    }
    private var individualisedLocalCount = 0

    private def pickByColour(candidates : Seq[ConstantTerm]) : ConstantTerm = {
      // the colouring of the previous pick is reused: with the syms
      // placed since then individualised, it is refined to the same
      // colour classes as a colouring started afresh
      for (sym <- placedLocals drop individualisedLocalCount)
        colouring.individualise(sym)
      individualisedLocalCount = placedLocals.size
      colouring.refine()
      // remaining ties are broken by the term order: deterministic,
      // but canonical only if the tied syms are interchangeable and
      // their conjuncts do not depend on how equations are reduced
      val colourThenTermOrdering = Ordering.Tuple2(
        Ordering.Int, constraint.order.constOrdering)
      candidates.minBy(sym => (colouring.colourOf(sym), sym))(
        colourThenTermOrdering)
    }

    private val readyDefinitions =
      new ArrayBuffer[(DefinitionKey, ConstantTerm, Option[DefiningConjunct])]

    private def place(local : ConstantTerm, token : SymToken) : Unit = {
      tokenOf(local) = token
      placedLocals += local
      readyDefinitions ++= classMembersDefinedBy(local)
    }

    // the arguments are placed first, by their index
    for (sym <- args) readyDefinitions ++= classMembersDefinedBy(sym)

    private val pendingFurtherDefinitions =
      new ArrayBuffer[(DefinitionKey, ConstantTerm, DefiningConjunct)]

    // only without quantifiers, as keys do not express bound variables
    private var waitingConjuncts : Seq[DefiningConjunct] =
      if (constraint.quans.isEmpty)
        (constraint.predConj.positiveLits.map(DefiningLiteral) ++
         (for (lhs <- constraint.arithConj.positiveEqs
               if DifferenceEquation.unapply(lhs).isEmpty)
            yield DefiningEquation(lhs))) filter canDefineLocal
      else
        Nil
    private val locals = constraint.constants -- args
    private val definableSyms =
      constraint.predConj.positiveLits.flatMap(resultSym).toSet

    private def unplacedSymsOf(conjunct : DefiningConjunct)
    : Set[ConstantTerm] =
      conjunct.syms filterNot tokenOf.contains

    var done = false
    while (!done) {
      val (nowReady, stillWaiting) =
        waitingConjuncts partition (unplacedSymsOf(_).size == 1)
      waitingConjuncts = stillWaiting
      for (conjunct <- nowReady) {
        val local = unplacedSymsOf(conjunct).head
        readyDefinitions += ((keyOf(conjunct, local), local, Some(conjunct)))
      }
      if (readyDefinitions.nonEmpty) {
        val smallestKey =
          readyDefinitions.map(_._1).min(definitionKeyOrdering)
        val tiedLocals =
          readyDefinitions.filter(_._1 == smallestKey).map(_._2).distinct
        val local =
          if (tiedLocals.size == 1) tiedLocals.head
          else pickByColour(tiedLocals)
        val definingConjunct = readyDefinitions.find(
          r => r._1 == smallestKey && r._2 == local).get._3
        val (definitionsOfLocal, otherDefinitions) =
          readyDefinitions partition (_._2 == local)
        readyDefinitions.clear()
        readyDefinitions ++= otherDefinitions
        place(local, DefinedToken(nextId(smallestKey)))
        // the members of a class are defined through it only once, so it
        // yields no further definitions
        pendingFurtherDefinitions ++=
          (for ((key, _, Some(conjunct)) <- definitionsOfLocal
                if !(definingConjunct exists (_ eq conjunct)))
             yield (key, local, conjunct))
      } else {
        val unplacedSyms = locals filterNot tokenOf.contains
        if (unplacedSyms.isEmpty) {
          done = true
        } else {
          // symbols that are no literal's result are never defined, so
          // they are ranked first
          val undefinableSyms = unplacedSyms filterNot definableSyms
          val candidates = // e.g., f(a,b) and g(b,a).
            if (undefinableSyms.nonEmpty) undefinableSyms else unplacedSyms
          val local =
            if (candidates.size == 1) candidates.head
            else pickByColour(candidates.toSeq)
          place(local, RankedToken(rankedCount))
          rankedCount += 1
        }
      }
    }
    Debug.assertPost(AC, constraint.constants forall tokenOf.contains)

    private val byKeyThenLocal =
      Ordering.Tuple2(definitionKeyOrdering, symTokenOrdering)
    val furtherDefinitions : Seq[FurtherDefinition] =
      for ((key, local, conjunct) <- pendingFurtherDefinitions.sortBy(
             r => (r._1, tokenOf(r._2)))(byKeyThenLocal))
        yield FurtherDefinition(conjunct, local, nextId(key))
  }

  private[symex]
  def resultSym(a : Atom) : Option[ConstantTerm] = {
    a.last match {
      case SingleTerm(c : ConstantTerm) => Some(c)
      case _ => None
    }
  }

  // ORDERINGS
  private val idealIntOrdering : Ordering[IdealInt] =
    Ordering.fromLessThan(_ < _)

  private lazy val symTokenOrdering : Ordering[SymToken] =
    new Ordering[SymToken] {
      private def kindRank(token : SymToken) : Int = token match {
        case _ : ArgToken     => 0
        case _ : DefinedToken => 1
        case _ : RankedToken  => 2
        case SelfToken        => 3
      }
      def compare(a : SymToken, b : SymToken) : Int = (a, b) match {
        case (ArgToken(i), ArgToken(j))         => i compare j
        case (DefinedToken(m), DefinedToken(n)) =>
          definitionIdOrdering.compare(m, n)
        case (RankedToken(i), RankedToken(j))   => i compare j
        case _ => kindRank(a) compare kindRank(b)
      }
    }

  private lazy val tokenCoeffOrdering : Ordering[(SymToken, IdealInt)] =
    Ordering.Tuple2(symTokenOrdering, idealIntOrdering)

  // terms first, constant last
  private lazy val tokenTermOrdering : Ordering[TokenTerm] =
    new Ordering[TokenTerm] {
      def compare(a : TokenTerm, b : TokenTerm) : Int = Seqs.lexCombineInts(
        Seqs.lexCompare(a.terms.iterator, b.terms.iterator)(tokenCoeffOrdering),
        a.constant compare b.constant)
    }

  // kind, predicate, arguments
  private lazy val definitionKeyOrdering : Ordering[DefinitionKey] =
    new Ordering[DefinitionKey] {
      private val predOrdering =
        Ordering.Option(ConstraintGraph.predicateOrdering)
      def compare(a : DefinitionKey, b : DefinitionKey) : Int =
        Seqs.lexCombineInts(
          a.kind compare b.kind,
          predOrdering.compare(a.pred, b.pred),
          Seqs.lexCompare(a.args.iterator, b.args.iterator)(tokenTermOrdering))
    }

  private lazy val definitionIdOrdering : Ordering[DefinitionId] =
    Ordering.by((id : DefinitionId) => (id.key, id.instance))(
      Ordering.Tuple2(definitionKeyOrdering, Ordering.Int))

}

// The constraint as a graph for colour refinement, by which the symbols that
// no literal defines are ordered. The vertices are the symbols, the
// conjuncts, the equality classes and the negated conjunctions; each
// conjunct is joined by an edge to each vertex in it, labelled with the role
// of the vertex there. The atoms of a goal, ordered by their colours too,
// are vertices joined to their arguments, labelled with the argument index.
// E.g., for undefinable symbols a and b in
//   mod_cast(0, 255, a, c), mod_cast(0, 255, b, d), c <= 10, d <= 20
// the casts of a and b look alike, but c is in c <= 10 and d in d <= 20,
// 10 < 20, so a is given the smaller colour and placed first.
private class ConstraintGraph(
    constraint : Conjunction,
    atoms      : Seq[(Predicate, Seq[ConstantTerm])] = Nil) {
  import ConstraintGraph._
  import VertexKind._

  val vertexOfSym : Map[ConstantTerm, Int] =
    (constraint.constants ++ atoms.flatMap(_._2)).toSeq.zipWithIndex.toMap

  private val vertexLabels =
    ArrayBuffer.fill(vertexOfSym.size)(VertexLabel(Symbol, None, Nil))
  private val edgesOfVertex =
    ArrayBuffer.fill(vertexOfSym.size)(new ArrayBuffer[Edge])
  addConjunction(constraint, enclosingConjunction = None)
  val vertexOfAtom : IndexedSeq[Int] =
    for ((pred, args) <- atoms.toIndexedSeq) yield {
      val atom = addVertex(VertexLabel(BodyAtom, Some(pred), Nil))
      for ((arg, argIndex) <- args.zipWithIndex)
        addEdge(atom, vertexOfSym(arg), ArgumentTerm(argIndex, IdealInt.ONE))
      atom
    }

  val vertexCount : Int = vertexLabels.size
  val vertexLabelRank : Array[Int] = ranksOf(vertexLabels)
  // the edges of vertex v are edgeStart(v) until edgeStart(v + 1)
  val edgeStart : Array[Int] = edgesOfVertex.scanLeft(0)(_ + _.size).toArray
  val edgeNeighbour : Array[Int] =
    edgesOfVertex.flatten.map(_.neighbour).toArray
  val edgeLabelRank : Array[Int] = ranksOf(edgesOfVertex.flatten.map(_.label))

  private def addVertex(label : VertexLabel) : Int = {
    vertexLabels += label
    edgesOfVertex += new ArrayBuffer[Edge]
    vertexLabels.size - 1
  }

  private def addEdge(conjunct : Int, vertex : Int,
                      label    : EdgeLabel) : Unit = {
    edgesOfVertex(conjunct) += Edge(vertex, label)
    edgesOfVertex(vertex) += Edge(conjunct, label)
  }

  // the ends are labelled differently, so that a negated conjunction is told
  // apart from the one it is nested in
  private def addNestingLink(vertex : Int, conjunction : Int) : Unit = {
    edgesOfVertex(vertex) += Edge(conjunction, EnclosingConjunction)
    edgesOfVertex(conjunction) += Edge(vertex, NestedVertex)
  }

  private def addConjunction(conj                 : Conjunction,
                             enclosingConjunction : Option[Int]) : Unit = {
    def nest(vertex : Int) : Unit =
      for (conjunction <- enclosingConjunction)
        addNestingLink(vertex, conjunction)
    for (lit <- conj.predConj.positiveLits)
      nest(addConjunct(PositiveLiteral, Some(lit.pred), lit))
    for (lit <- conj.predConj.negativeLits)
      nest(addConjunct(NegativeLiteral, Some(lit.pred), lit))
    addEquations(conj.arithConj.positiveEqs) foreach nest
    // the stored sign depends on the term order, so both signs are given
    for (lhs <- conj.arithConj.negativeEqs; signedLhs <- Seq(lhs, -lhs))
      nest(addConjunct(Disequation, None, List(signedLhs)))
    for (inEq <- conj.arithConj.inEqs)
      nest(addConjunct(Inequality, None, List(inEq)))
    for (negatedConj <- conj.negatedConjs) {
      val conjunction = addVertex(VertexLabel(NegatedConjunction, None, Nil))
      nest(conjunction)
      addConjunction(negatedConj, Some(conjunction))
    }
  }

  // Equations are stored row-reduced along the term order: an equality
  // class of difference equations as a star around its member that is
  // smallest in the term order, the only member left in the other
  // equations. So each class is a vertex joined to its members at their
  // offsets, and the other equations are joined to the classes instead of
  // these members. The stored sign depends on the term order too, so both
  // signs are given.
  private def addEquations(equations : Seq[LinearCombination]) : Seq[Int] = {
    val (differences, otherEquations) =
      equations partition (DifferenceEquation.unapply(_).isDefined)
    val stars = (for (DifferenceEquation(member, pivot, offset) <- differences)
                   yield (pivot, (member, offset))).groupBy(_._1)
    val classMembership = new MHashMap[ConstantTerm, ClassMembership]
    val classVertices = for ((pivot, star) <- stars.toList) yield {
      val classVertex = addVertex(VertexLabel(EqualityClass, None, Nil))
      val offsetsAbovePivot = (pivot, IdealInt.ZERO) +: star.map(_._2)
      val smallestOffset = offsetsAbovePivot.map(_._2).min
      for ((member, offsetAbovePivot) <- offsetsAbovePivot) {
        val offset = offsetAbovePivot - smallestOffset
        addEdge(classVertex, vertexOfSym(member), ClassOffset(offset))
        classMembership(member) = ClassMembership(classVertex, offset)
      }
      classVertex
    }
    classVertices ++
      (for (lhs <- otherEquations; signedLhs <- Seq(lhs, -lhs))
         yield addConjunct(Equation, None, List(signedLhs), classMembership))
  }

  // a member of one of the given classes is replaced by its class, with the
  // constant shifted by the offset of the member
  private def addConjunct(
      kind            : VertexKind.Value,
      pred            : Option[Predicate],
      args            : Seq[LinearCombination],
      classMembership : collection.Map[ConstantTerm, ClassMembership] = Map())
  : Int = {
    def offsetOf(sym : ConstantTerm) =
      classMembership.get(sym).fold(IdealInt.ZERO)(_.offset)
    val conjunct = addVertex(VertexLabel(
      kind, pred,
      for (arg <- args) yield arg.constant + IdealInt.sum(
        for ((coeff, sym : ConstantTerm) <- arg)
          yield coeff * offsetOf(sym))))
    for ((arg, argIndex) <- args.zipWithIndex;
         (coeff, sym : ConstantTerm) <- arg)
      addEdge(conjunct,
              classMembership.get(sym).fold(vertexOfSym(sym))(_.classVertex),
              ArgumentTerm(argIndex, coeff))
    conjunct
  }

}

private object ConstraintGraph {

  // The label of a vertex is its kind and, for a conjunct, everything about
  // the conjunct except its symbols: the predicate of a literal and the
  // constant of each argument. E.g., mod_cast(0, 255, 2*a + 1, c) has the
  // label (PositiveLiteral, mod_cast, (0, 255, 1, 0)), and x - y + 3 >= 0
  // the label (Inequality, none, (3)).
  case class VertexLabel(kind      : VertexKind.Value,
                         pred      : Option[Predicate],
                         constants : Seq[IdealInt])

  object VertexKind extends Enumeration {
    val Symbol, EqualityClass, NegatedConjunction, PositiveLiteral,
        NegativeLiteral, Equation, Disequation, Inequality, BodyAtom = Value
  }

  sealed trait EdgeLabel
  case class ArgumentTerm(argIndex : Int, coeff : IdealInt) extends EdgeLabel
  case class ClassOffset(offset : IdealInt) extends EdgeLabel
  case object EnclosingConjunction extends EdgeLabel
  case object NestedVertex extends EdgeLabel

  case class Edge(neighbour : Int, label : EdgeLabel)

  case class ClassMembership(classVertex : Int, offset : IdealInt)

  // member - pivot - offset = 0, with the member above the pivot in the term
  // order
  object DifferenceEquation {
    def unapply(lhs : LinearCombination)
    : Option[(ConstantTerm, ConstantTerm, IdealInt)] = lhs match {
      case TwoTermsWithOffset(IdealInt.ONE, member : ConstantTerm,
                              IdealInt.MINUS_ONE, pivot : ConstantTerm,
                              constant) => Some((member, pivot, -constant))
      case _ => None
    }
  }

  // the number of smaller values for each value, counting equal ones once
  def ranksOf[A](values : IndexedSeq[A])(implicit ordering : Ordering[A])
  : Array[Int] = {
    val sortedIndices = values.indices sortBy values
    val ranks = new Array[Int](values.size)
    for (i <- 1 until sortedIndices.size) {
      val (previous, next) = (sortedIndices(i - 1), sortedIndices(i))
      ranks(next) = ranks(previous) +
        (if (ordering.lt(values(previous), values(next))) 1 else 0)
    }
    ranks
  }

  val predicateOrdering : Ordering[Predicate] =
    Ordering.by((pred : Predicate) => (pred.name, pred.arity))

  implicit val vertexLabelOrdering : Ordering[VertexLabel] =
    new Ordering[VertexLabel] {
      private val predOrdering = Ordering.Option(predicateOrdering)
      def compare(a : VertexLabel, b : VertexLabel) : Int =
        Seqs.lexCombineInts(
          a.kind compare b.kind,
          predOrdering.compare(a.pred, b.pred),
          Seqs.lexCompare(a.constants.iterator, b.constants.iterator))
    }

  implicit val edgeLabelOrdering : Ordering[EdgeLabel] =
    Ordering.by[EdgeLabel, (Int, Int, IdealInt)] {
      case ArgumentTerm(argIndex, coeff) => (0, argIndex, coeff)
      case ClassOffset(offset)           => (1, 0, offset)
      case EnclosingConjunction          => (2, 0, IdealInt.ZERO)
      case NestedVertex                  => (3, 0, IdealInt.ZERO)
    }

}

// The colour of a vertex is the number of vertices with a smaller colour, so
// in verticesByColour each colour class starts at the index of its colour.
private class GraphColouring(graph : ConstraintGraph) {
  import graph._

  private val colour = new Array[Int](vertexCount)
  private val verticesByColour : Array[Integer] =
    Array.tabulate(vertexCount)(Int.box)
  // the sorted (edge label, neighbour colour) pairs of a vertex, at the
  // indices of its edges
  private val signature = new Array[Long](edgeNeighbour.length)

  sortAndColour(0, vertexCount,
                Ordering.by((vertex : Integer) => vertexLabelRank(vertex)))

  def colourOf(sym : ConstantTerm) : Int = colour(vertexOfSym(sym))

  def colourOfAtom(atomIndex : Int) : Int = colour(vertexOfAtom(atomIndex))

  def individualise(sym : ConstantTerm) : Unit =
    vertexOfSym get sym foreach individualiseVertex

  def individualiseAtom(atomIndex : Int) : Unit =
    individualiseVertex(vertexOfAtom(atomIndex))

  // the vertex is given the first colour of its colour class, the rest of the
  // class the next colour
  private def individualiseVertex(vertex : Int) : Unit = {
    val start = colour(vertex)
    val end = colourClassEnd(start)
    if (end - start > 1) {
      val index =
        (start until end).find(verticesByColour(_).intValue == vertex).get
      val boxedVertex = verticesByColour(index)
      verticesByColour(index) = verticesByColour(start)
      verticesByColour(start) = boxedVertex
      for (i <- start + 1 until end)
        colour(verticesByColour(i)) = start + 1
    }
  }

  def refine() : Unit = {
    var split = true
    while (split) {
      forEachSharedColour { (start, end) =>
        for (i <- start until end) computeSignature(verticesByColour(i))
      }
      split = false
      forEachSharedColour { (start, end) =>
        if (sortAndColour(start, end, bySignature)) split = true
      }
    }
  }

  private def colourClassEnd(start : Int) : Int = {
    var end = start + 1
    while (end < vertexCount && colour(verticesByColour(end)) == start)
      end += 1
    end
  }

  private def forEachSharedColour(f : (Int, Int) => Unit) : Unit = {
    var start = 0
    while (start < vertexCount) {
      val end = colourClassEnd(start)
      if (end - start > 1)
        f(start, end)
      start = end
    }
  }

  private def computeSignature(vertex : Int) : Unit = {
    for (edge <- edgeStart(vertex) until edgeStart(vertex + 1))
      signature(edge) =
        (edgeLabelRank(edge).toLong << 32) | colour(edgeNeighbour(edge))
    Arrays.sort(signature, edgeStart(vertex), edgeStart(vertex + 1))
  }

  private val bySignature : Ordering[Integer] = new Ordering[Integer] {
    def compare(a : Integer, b : Integer) : Int = compareSignatures(a, b)
  }

  private def compareSignatures(a : Int, b : Int) : Int = {
    val aEnd = edgeStart(a + 1)
    val bEnd = edgeStart(b + 1)
    var i = edgeStart(a)
    var j = edgeStart(b)
    while (i < aEnd && j < bEnd && signature(i) == signature(j)) {
      i += 1
      j += 1
    }
    if (i < aEnd && j < bEnd) signature(i) compare signature(j)
    else (aEnd - i) compare (bEnd - j)
  }

  // verticesByColour(start until end) is sorted, and each vertex is given
  // the index of the first one equal to it; true if not all are equal
  private def sortAndColour(start    : Int,
                            end      : Int,
                            ordering : Ordering[Integer]) : Boolean = {
    Arrays.sort(verticesByColour, start, end, ordering)
    colour(verticesByColour(start)) = start
    for (i <- start + 1 until end)
      colour(verticesByColour(i)) =
        if (ordering.equiv(verticesByColour(i - 1), verticesByColour(i)))
          colour(verticesByColour(i - 1))
        else
          i
    colour(verticesByColour(end - 1)) != start
  }

}
