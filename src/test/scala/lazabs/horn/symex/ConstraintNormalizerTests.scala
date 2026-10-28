package lazabs.horn.symex

import ap.api.SimpleAPI
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.{Atom, Predicate}
import ap.terfor.substitutions.ConstantSubst
import ap.theories.bitvectors.ModuloArithmetic
import lazabs.horn.bottomup.RelationSymbol
import org.scalatest.freespec.AnyFreeSpec

import scala.collection.mutable.{HashMap => MHashMap}

class ConstraintNormalizerTests extends AnyFreeSpec {

  ap.util.Debug.enableAllAssertions(true)

  import ap.terfor.TerForConvenience._

  private def normalize(args       : Seq[ConstantTerm],
                        constraint : Conjunction,
                        pool       : Seq[ConstantTerm])
                       (implicit sf : SymexSymbolFactory) : Conjunction =
    ConstraintNormalizer.normalize(args, constraint,
                                   n => (pool take n, sf.order))

  // a definition gets its symbol when first used, as in the symbol factory
  private def definedSyms(implicit sf : SymexSymbolFactory)
  : DefinitionId => ConstantTerm = {
    val syms = new MHashMap[DefinitionId, ConstantTerm]
    id => syms.getOrElseUpdate(id, sf.genConstant("d" + syms.size))
  }

  private def normalizeWithDefinitions(
      args       : Seq[ConstantTerm],
      constraint : Conjunction,
      pool       : Seq[ConstantTerm],
      definedSym : DefinitionId => ConstantTerm)
     (implicit sf : SymexSymbolFactory) : Conjunction =
    ConstraintNormalizer.normalize(args, constraint,
                                   n => (pool take n, sf.order),
                                   Some(definedSym))

  // whether the normal form of smaller is part of that of larger
  private def keepsSyms(args    : Seq[ConstantTerm],
                        smaller : Conjunction,
                        larger  : Conjunction,
                        pool    : Seq[ConstantTerm])
                       (implicit sf : SymexSymbolFactory) : Boolean = {
    val definedSym = definedSyms
    val Seq(smallerForm, largerForm) =
      for (constraint <- Seq(smaller, larger))
        yield normalizeWithDefinitions(args, constraint, pool, definedSym)
    smallerForm.iterator.toSet subsetOf largerForm.iterator.toSet
  }

  private def normalizeGoal(goal : GoalClause,
                            pool : Seq[ConstantTerm])
                           (implicit sf : SymexSymbolFactory) : GoalClause =
    ConstraintNormalizer.normalizeGoal(goal, n => (pool take n, sf.order))

  "Locals with swapped coefficients get the same normal form" in {
    SimpleAPI.withProver { p =>
      implicit val sf = new SymexSymbolFactory(Nil, p)
      val h    = sf.genConstant("h")
      val a    = sf.genConstant("a")
      val b    = sf.genConstant("b")
      val pool = for (i <- 0 until 2) yield sf.genConstant("n" + i)
      implicit val order = sf.order

      // both give h one of 0, 2, 3, 5
      val bounds  = conj(l(a) >= 0, l(a) <= 1, l(b) >= 0, l(b) <= 1)
      val first   = conj(bounds, l(h) === l(a) * 2 + l(b) * 3)
      val swapped = conj(bounds, l(h) === l(b) * 2 + l(a) * 3)
      assert(normalize(Seq(h), first, pool) == normalize(Seq(h), swapped, pool))
    }
  }

  "Normal forms do not depend on the symbols of the locals" in {
    SimpleAPI.withProver { p =>
      val theories = List(ModuloArithmetic)
      p.addTheories(theories)
      implicit val sf = new SymexSymbolFactory(theories, p)
      val h       = sf.genConstant("h")
      val locals  =
        for (name <- Seq("a", "b", "c", "d")) yield sf.genConstant(name)
      val Seq(a, b, c, d) = locals
      val pool    = for (i <- 0 until locals.size) yield sf.genConstant("n" + i)
      implicit val order = sf.order

      val linear = conj(l(h) === l(a) * 2 + l(b) * 3 + l(c) * 5,
                        l(a) >= 0, l(b) >= 0, l(c) >= 0)
      val castAndExtract =
        conj(Atom(ModuloArithmetic._mod_cast,
                  List(l(0), l(255), l(a) * 2 + l(b) * 3, l(c)), order),
             Atom(ModuloArithmetic._bv_extract,
                  List(l(3), l(0), l(c), l(h)), order))
      // a and b occur only inside the disjunction
      val disjunction = conj(l(c) >= l(h),
                             disj(l(a) === l(c) + 1, l(b) === l(h) * 2))
      // a and b differ only through their partners c and d
      val partners =
        conj(Atom(ModuloArithmetic._mod_cast,
                  List(l(0), l(255), l(a), l(c)), order),
             Atom(ModuloArithmetic._mod_cast,
                  List(l(0), l(255), l(b), l(d)), order),
             l(c) >= 0, l(d) >= 1)
      // the equations of a, b and c are stored as differences to the one
      // that is smallest in the term order
      val equalityClass =
        conj(l(a) === l(b), l(b) === l(c),
             Atom(ModuloArithmetic._mod_cast,
                  List(l(0), l(255), l(a), l(d)), order),
             l(c) >= 1)
      // b and c differ only through the disjuncts they share with h
      val disjuncts = conj(disj(l(b) > 0, l(h) > 0), disj(l(c) > 0, l(h) > 1))

      for (constraint <- Seq(linear, castAndExtract, disjunction, partners,
                             equalityClass, disjuncts);
           definedSym <- Seq(None, Some(definedSyms))) {
        val normalForms = for (permutation <- locals.permutations) yield {
          // symbols created in the order of the permutation follow it in the
          // term order
          val renaming = (for (sym <- permutation)
            yield sym -> sf.genConstant(sym.name + "'")).toMap
          ConstraintNormalizer.normalize(
            Seq(h), ConstantSubst(renaming, sf.order)(constraint),
            n => (pool take n, sf.order), definedSym)
        }
        assert(normalForms.toSet.size == 1, constraint)
      }
    }
  }

  "Goal normal forms do not depend on the order and occurrences of atoms" in {
    SimpleAPI.withProver { p =>
      val theories = List(ModuloArithmetic)
      p.addTheories(theories)
      implicit val sf = new SymexSymbolFactory(theories, p)
      val P = RelationSymbol(new Predicate("P", 1))
      val Q = RelationSymbol(new Predicate("Q", 1))
      val Seq(x0, x1) = for (occ <- 0 to 1) yield P.arguments(occ).head
      val y = Q.arguments(0).head
      val Seq(a, b, c) = for (name <- Seq("a", "b", "c"))
        yield sf.genConstant(name)
      val pool = for (i <- 0 until 3) yield sf.genConstant("n" + i)
      implicit val order = sf.order

      val example = GoalClause(Seq((P, 0), (P, 1)),
                               conj(l(x0) === 1, l(x1) === 2))
      // the atoms of P differ only through the locals b and c
      val theoryLocals = GoalClause(
        Seq((P, 0), (P, 1), (Q, 0)),
        conj(Atom(ModuloArithmetic._mod_cast,
                  List(l(0), l(255), l(x0) + l(a), l(b)), order),
             Atom(ModuloArithmetic._mod_cast,
                  List(l(0), l(255), l(x1) + l(a), l(c)), order),
             l(b) <= 10, l(c) <= 20, l(y) >= l(a)))
      val distinctPredicates = GoalClause(Seq((P, 0), (Q, 0)),
                                          conj(l(x0) + l(a) >= l(y)))

      def normalForms(goal : GoalClause, locals : Seq[ConstantTerm]) =
        for (occsOfP     <- (0 to 2).combinations(2).flatMap(_.permutations);
             atomOrder   <- goal.atoms.indices.permutations;
             localsOrder <- locals.permutations) yield {
          // symbols created in the order of the permutation follow it in the
          // term order
          val occRenaming = for (occ <- 0 to 1)
            yield P.arguments(occ).head -> P.arguments(occsOfP(occ)).head
          val localRenaming = for (sym <- localsOrder)
            yield sym -> sf.genConstant(sym.name + "'")
          val atoms = for ((rs, occ) <- goal.atoms)
            yield if (rs == P) (rs, occsOfP(occ)) else (rs, occ)
          val constraint = ConstantSubst((occRenaming ++ localRenaming).toMap,
                                         sf.order)(goal.constraint)
          normalizeGoal(GoalClause(atomOrder map atoms, constraint), pool)
        }

      assert(normalForms(example, Nil).toSet == Set(example))
      assert(normalForms(theoryLocals, Seq(a, b, c)).toSet.size == 1)
      assert(normalForms(distinctPredicates, Seq(a)).toSet.size == 1)
    }
  }

  "Goals whose atoms form a cycle get one normal form" in {
    SimpleAPI.withProver { p =>
      implicit val sf = new SymexSymbolFactory(Nil, p)
      val P = RelationSymbol(new Predicate("P", 1))
      val xs = for (occ <- 0 to 3) yield P.arguments(occ).head
      implicit val order = sf.order

      // all four atoms look alike until one of them is placed
      val cycle =
        conj(for (i <- 0 to 3) yield l(xs(i)) + l(xs((i + 1) % 4)) <= 10)
      val normalForms = for (occs <- (0 to 3).permutations) yield {
        val renaming = for (i <- 0 to 3) yield xs(i) -> xs(occs(i))
        val constraint = ConstantSubst(renaming.toMap, sf.order)(cycle)
        normalizeGoal(GoalClause(for (occ <- occs) yield (P, occ), constraint),
                      Nil)
      }
      assert(normalForms.toSet.size == 1)
    }
  }

  "Renumbered atoms do not capture locals" in {
    SimpleAPI.withProver { p =>
      implicit val sf = new SymexSymbolFactory(Nil, p)
      val P = RelationSymbol(new Predicate("P", 1))
      val Seq(x0, x1) = for (occ <- 0 to 1) yield P.arguments(occ).head
      val a = sf.genConstant("a")
      val pool = Seq(sf.genConstant("n0"))
      implicit val order = sf.order

      // x0 is a local that P(x1) is renumbered onto
      val argAsLocal = GoalClause(Seq((P, 1)), conj(l(x0) > l(x1)))
      val freshLocal = GoalClause(Seq((P, 1)), conj(l(a) > l(x1)))
      assert(normalizeGoal(argAsLocal, pool) ==
               normalizeGoal(freshLocal, pool))
    }
  }

  "Goals that constrain one atom or two get different normal forms" in {
    SimpleAPI.withProver { p =>
      implicit val sf = new SymexSymbolFactory(Nil, p)
      val P = RelationSymbol(new Predicate("P", 2))
      val Seq(Seq(x0, y0), Seq(x1, y1)) =
        for (occ <- 0 to 1) yield P.arguments(occ)
      implicit val order = sf.order

      val atoms = Seq((P, 0), (P, 1))
      val oneAtom = GoalClause(atoms, conj(l(x0) === 1, l(y0) === 2))
      val twoAtoms = GoalClause(atoms, conj(l(x0) === 1, l(y1) === 2))
      assert(normalizeGoal(oneAtom, Nil) != normalizeGoal(twoAtoms, Nil))
    }
  }

  "Locals defined by equations keep their symbols when locals are added" in {
    SimpleAPI.withProver { p =>
      implicit val sf = new SymexSymbolFactory(Nil, p)
      val Seq(x, y, c, d) =
        for (name <- Seq("x", "y", "c", "d")) yield sf.genConstant(name)
      val pool = for (i <- 0 until 2) yield sf.genConstant("n" + i)
      implicit val order = sf.order

      val smaller = conj(l(c) * 2 === l(x), l(c) >= l(y))
      val larger  = conj(smaller, l(d) * 3 === l(y) + 1, l(d) >= l(x))
      assert(keepsSyms(Seq(x, y), smaller, larger, pool))
    }
  }

  "Locals that are operands keep their symbols when locals are added" in {
    SimpleAPI.withProver { p =>
      val theories = List(ModuloArithmetic)
      p.addTheories(theories)
      implicit val sf = new SymexSymbolFactory(theories, p)
      val Seq(x, y, c, d) =
        for (name <- Seq("x", "y", "c", "d")) yield sf.genConstant(name)
      val pool = for (i <- 0 until 2) yield sf.genConstant("n" + i)
      implicit val order = sf.order

      def lowByte(sym : ConstantTerm, byte : ConstantTerm) =
        Atom(ModuloArithmetic._bv_extract,
             List(l(7), l(0), l(sym), l(byte)), order)
      val smaller = conj(lowByte(c, x), l(c) <= 1000)
      val larger  = conj(smaller, lowByte(d, y), l(d) <= 500)
      assert(keepsSyms(Seq(x, y), smaller, larger, pool))
    }
  }

  "Locals with equal definitions keep distinct symbols" in {
    SimpleAPI.withProver { p =>
      val theories = List(ModuloArithmetic)
      p.addTheories(theories)
      implicit val sf = new SymexSymbolFactory(theories, p)
      val Seq(x, c, d) =
        for (name <- Seq("x", "c", "d")) yield sf.genConstant(name)
      val pool = for (i <- 0 until 2) yield sf.genConstant("n" + i)
      implicit val order = sf.order

      def lowByte(sym : ConstantTerm) =
        Atom(ModuloArithmetic._bv_extract,
             List(l(7), l(0), l(sym), l(x)), order)
      val constraint =
        conj(lowByte(c), lowByte(d), l(c) <= 100, l(d) >= 300)
      val normalForm =
        normalizeWithDefinitions(Seq(x), constraint, pool, definedSyms)
      assert(normalForm.constants.size == constraint.constants.size)
    }
  }

}
