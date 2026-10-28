package lazabs.horn.symex

import ap.api.SimpleAPI
import ap.terfor.preds.Predicate
import lazabs.horn.bottomup.{HornClauses, RelationSymbol}
import org.scalatest.freespec.AnyFreeSpec

class GoalSubsumptionTests extends AnyFreeSpec {

  ap.util.Debug.enableAllAssertions(true)

  import ap.terfor.TerForConvenience._

  // P with two occurrences and Q with one and both of arity 1
  private def goalSymbols(p : SimpleAPI)
  : (SymexSymbolFactory, RelationSymbol, RelationSymbol) = {
    val sf = new SymexSymbolFactory(Nil, p)
    val Seq(pPred, qPred) =
      for (name <- Seq("P", "Q")) yield new Predicate(name, 1)
    sf.initialize(Set((HornClauses.FALSE, 0), (pPred, 1), (qPred, 0)))
    (sf, RelationSymbol(pPred)(sf), RelationSymbol(qPred)(sf))
  }

  // the goals in normal form, with the local symbols of SLDSymex
  private def subsumes(stored : GoalClause, goal : GoalClause)
                      (implicit sf : SymexSymbolFactory) : Boolean = {
    def normalized(g : GoalClause) = ConstraintNormalizer.normalizeGoal(
      g,
      n => (sf.localSymbolsForPred(HornClauses.FALSE, n, 0), sf.order),
      Some(sf.definedSymbolForPred(HornClauses.FALSE, _)))._1
    val subsumesGoal = GoalSubsumption.subsumptionTestFor(normalized(goal))
    subsumesGoal(normalized(stored))
  }

  "A goal with fewer atoms subsumes under a map of its atoms" in {
    SimpleAPI.withProver { p =>
      val (sf, pRs, qRs) = goalSymbols(p)
      implicit val symbolFactory = sf
      val Seq(x0) = pRs.arguments(0)
      val Seq(y0) = qRs.arguments(0)
      implicit val order = sf.order

      val goal = GoalClause(Seq((pRs, 0), (qRs, 0)),
                            conj(l(y0) < l(-1), l(x0) === l(1)))
      assert(subsumes(GoalClause(Seq((qRs, 0)), conj(l(y0) < l(0))), goal))
      assert(!subsumes(GoalClause(Seq((qRs, 0)), conj(l(y0) < l(-5))), goal))
    }
  }

  "Locals with definitions are renamed with the atoms" in {
    // y0 is even by the same definition in both goals but it is argument 0
    // in stored and argument 1 in goal
    SimpleAPI.withProver { p =>
      val (sf, pRs, qRs) = goalSymbols(p)
      implicit val symbolFactory = sf
      val Seq(x0) = pRs.arguments(0)
      val Seq(y0) = qRs.arguments(0)
      val c = sf.genConstant("c")
      implicit val order = sf.order

      val stored = GoalClause(Seq((qRs, 0)),
                              conj(l(c) * 2 === l(y0), l(y0) < l(0)))
      val goal = GoalClause(Seq((pRs, 0), (qRs, 0)),
                            conj(l(c) * 2 === l(y0), l(y0) < l(0),
                                 l(x0) === l(1)))
      assert(subsumes(stored, goal))
    }
  }

  "Two atoms are not mapped to one" in {
    SimpleAPI.withProver { p =>
      val (sf, pRs, _) = goalSymbols(p)
      implicit val symbolFactory = sf
      val Seq(x0) = pRs.arguments(0)
      val Seq(x1) = pRs.arguments(1)
      implicit val order = sf.order

      val stored = GoalClause(Seq((pRs, 0), (pRs, 1)),
                              conj(l(x0) === l(1), l(x1) === l(1)))
      val goal = GoalClause(Seq((pRs, 0)), conj(l(x0) === l(1)))
      assert(!subsumes(stored, goal))
    }
  }
}
