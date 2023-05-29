package lazabs.horn

import lazabs.horn.bottomup.HornWrapper
import ap.api.SimpleAPI.ProverStatus
import lazabs.horn.preprocessor.HornPreprocessor.{CounterExample, Solution}
import org.scalatest.matchers.{MatchResult, Matcher}
import org.scalatest.matchers.should.Matchers

// Blend in to have assertions like "result should beSat"
trait CHCResultMatchers extends Matchers {
  type Result = Either[Solution, CounterExample]
  def be(status: ProverStatus.Value) = StatusChecker(status)
  def beSat   = StatusChecker(ProverStatus.Sat)
  def beUnsat = StatusChecker(ProverStatus.Unsat)

  case class StatusChecker(status: ProverStatus.Value) extends Matcher[Result] {
    override def apply(result: Result): MatchResult = {
      val resultStatus =
        if (result.isLeft) ProverStatus.Sat else ProverStatus.Unsat
      MatchResult(resultStatus == status,
                  "Error: expected " + status + ", got " + resultStatus,
                  "")
    }
  }

  def hideOutput[A](comp : => A) : A =
    Console.withOut(HornWrapper.NullStream) {
      Console.withErr(HornWrapper.NullStream) {
        comp
      }
    }
}
