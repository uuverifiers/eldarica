package lazabs.horn.symex

import ap.api.SimpleAPI
import ap.terfor.ConstantTerm
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.terfor.substitutions.ConstantSubst
import ap.theories.bitvectors.ModuloArithmetic
import org.scalatest.freespec.AnyFreeSpec

class ConstraintNormalizerTests extends AnyFreeSpec {

  ap.util.Debug.enableAllAssertions(true)

  import ap.terfor.TerForConvenience._

  private def normalize(fixedSyms  : Seq[ConstantTerm],
                        constraint : Conjunction,
                        pool       : Seq[ConstantTerm])
                       (implicit sf : SymexSymbolFactory) : Conjunction =
    ConstraintNormalizer.normalize(fixedSyms, constraint,
                                   n => (pool take n, sf.order)).constraint

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

  "Normal forms do not depend on the names of the locals" in {
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
                             equalityClass, disjuncts)) {
        val normalForms = for (permutation <- locals.permutations) yield {
          // symbols created in the order of the permutation follow it in the
          // term order
          val renaming = (for (sym <- permutation)
            yield sym -> sf.genConstant(sym.name + "'")).toMap
          normalize(Seq(h), ConstantSubst(renaming, sf.order)(constraint), pool)
        }
        assert(normalForms.toSet.size == 1, constraint)
      }
    }
  }

}
