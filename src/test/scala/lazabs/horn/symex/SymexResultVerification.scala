package lazabs.horn.symex

import ap.parser.IAtom
import lazabs.GlobalParameters
import lazabs.horn.HornWrapper
import lazabs.horn.Util.Dag
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.preprocessor.HornPreprocessor.Solution

trait SymexResultVerification {
  def solveAndVerify(symex : Symex[Clause])
  : Either[() => Solution, () => Dag[(IAtom, Clause)]] = {
    val result  = symex.solve()
    val clauses = symex.normClauses.map(_._2)
    val params  = GlobalParameters.get.clone
    params.verifySolCEX = true
    GlobalParameters.withValue(params) {
      result match {
        case Left(solution) =>
          HornWrapper.verifySolution(solution(), clauses)
        case Right(counterexample) =>
          HornWrapper.verifyCEX(counterexample(), clauses)
      }
    }
    result
  }
}
