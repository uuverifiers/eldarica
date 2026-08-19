package lazabs.horn.symex

import ap.api.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
import ap.terfor.preds.Atom
import ap.theories.bitvectors.ModuloArithmetic
import org.scalatest.freespec.AnyFreeSpec

class ConstraintSimplifierTests
    extends AnyFreeSpec
    with ConstraintSimplifierUsingConjunctEliminator {

  ap.util.Debug.enableAllAssertions(true)

  import ap.terfor.TerForConvenience._

  "Eliminating a symbol from inequalities keeps the divisibility condition" in {
    SimpleAPI.withProver { p =>
      implicit val sf = new SymexSymbolFactory(Nil, p)
      val a = sf.genConstant("a")
      val b = sf.genConstant("b")
      implicit val order = sf.order

      // EX b. a <= 3*b <= a+1 holds iff a is not congruent 1 mod 3
      val constraint = conj(l(b) * 3 >= l(a), l(b) * 3 <= l(a) + 1)
      val res = simplifyConstraint(constraint,
                                   Set(b : ap.terfor.Term),
                                   reduceBeforeSimplification = false)

      def statusForA(value : Int) : ProverStatus.Value = p.scope {
        p.addAssertion(res)
        p.addAssertion(l(a) === value)
        p.???
      }
      assert(statusForA(0) == ProverStatus.Sat)
      assert(statusForA(1) == ProverStatus.Unsat)
    }
  }

  "Eliminating a symbol must not weaken a negated divisibility" in {
    SimpleAPI.withProver { p =>
      implicit val sf = new SymexSymbolFactory(Nil, p)
      val a  = sf.genConstant("a")
      val a1 = sf.genConstant("a1")
      implicit val order = sf.order

      // (not EX q. 3q = a - 1) & a1 = a + 3: eliminating a must give
      // "a1 is not congruent 1 mod 3"
      val constraint = conj(exists(l(v(0)) * 3 === l(a) - 1).negate,
                            l(a1) === l(a) + 3)
      val res = simplifyConstraint(constraint,
                                   Set(a : ap.terfor.Term),
                                   reduceBeforeSimplification = true)

      def statusForA1(value : Int) : ProverStatus.Value = p.scope {
        p.addAssertion(res)
        p.addAssertion(l(a1) === value)
        p.???
      }
      assert(statusForA1(3) == ProverStatus.Sat)
      assert(statusForA1(4) == ProverStatus.Unsat)
    }
  }

  "Equations defining local symbols are inlined" in {
    SimpleAPI.withProver { p =>
      implicit val sf = new SymexSymbolFactory(Nil, p)
      val x = sf.genConstant("x")
      val c = sf.genConstant("c")
      implicit val order = sf.order

      // c = x - 1 & 0 <= c <= 10: eliminating c must give 1 <= x <= 11
      val constraint = conj(l(c) === l(x) - 1, l(c) >= 0, l(c) <= 10)
      val res = simplifyConstraint(constraint,
                                   Set(c : ap.terfor.Term),
                                   reduceBeforeSimplification = false)

      assert(!(res.constants contains c))

      def statusForX(value : Int) : ProverStatus.Value = p.scope {
        p.addAssertion(res)
        p.addAssertion(l(x) === value)
        p.???
      }
      assert(statusForX(1) == ProverStatus.Sat)
      assert(statusForX(11) == ProverStatus.Sat)
      assert(statusForX(0) == ProverStatus.Unsat)
      assert(statusForX(12) == ProverStatus.Unsat)
    }
  }

  "Inlined equations rewrite the arguments of theory atoms" in {
    SimpleAPI.withProver { p =>
      val theories = List(ModuloArithmetic)
      p.addTheories(theories)
      implicit val sf = new SymexSymbolFactory(theories, p)
      val x = sf.genConstant("x")
      val y = sf.genConstant("y")
      val c = sf.genConstant("c")
      implicit val order = sf.order

      // c = x - 1 & mod_cast(0, 255, c + 1, y): inlining c must leave
      // mod_cast(0, 255, x, y)
      val constraint = conj(l(c) === l(x) - 1,
                            Atom(ModuloArithmetic._mod_cast,
                                 List(l(0), l(255), l(c) + 1, l(y)),
                                 order))
      val res = simplifyConstraint(constraint,
                                   Set(c : ap.terfor.Term),
                                   reduceBeforeSimplification = false)

      assert(!(res.constants contains c))
      assert(res.predConj.positiveLits.size == 1)
      assert(res.predConj.positiveLits.head(2) == l(x))
    }
  }
}
