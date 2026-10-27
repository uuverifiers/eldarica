package lazabs.horn

import lazabs.horn.Util._
import ap.api.SimpleAPI.ProverStatus
import org.scalatest.matchers.{MatchResult, Matcher}
import org.scalatest.matchers.should.Matchers

// Blend in to have assertions like "result should beSat"
trait CHCResultMatchers extends Matchers {
  def be(status: ProverStatus.Value) = StatusChecker(status)
  def beSat   = StatusChecker(ProverStatus.Sat)
  def beUnsat = StatusChecker(ProverStatus.Unsat)

  case class StatusChecker(status: ProverStatus.Value)
      extends Matcher[Either[Any, Any]] {
    override def apply(result: Either[Any, Any]): MatchResult = {
      val resultStatus =
        if (result.isLeft) ProverStatus.Sat else ProverStatus.Unsat
      MatchResult(resultStatus == status,
                  "Error: expected " + status + ", got " + resultStatus,
                  "")
    }
  }

  def hideOutput[A](comp : => A) : A =
    Console.withOut(NullStream) {
      Console.withErr(NullStream) {
        comp
      }
    }
}
