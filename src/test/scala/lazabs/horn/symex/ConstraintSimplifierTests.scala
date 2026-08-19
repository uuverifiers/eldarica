package lazabs.horn.symex

import ap.api.SimpleAPI
import ap.api.SimpleAPI.ProverStatus
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
}
