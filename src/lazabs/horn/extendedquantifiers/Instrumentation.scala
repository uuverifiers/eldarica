package lazabs.horn.extendedquantifiers

import ap.parser.{IFormula, ITerm}

// An instrumentation consists of a new constraint and a map from head argument
// indices (for the ghost variables) to ghost terms used in the constraint
case class Instrumentation (constraint : IFormula,
                            headTerms  : Map[Int, ITerm]) {
  // Two instrumentations are composed by conjoining the constraints,
  // and taking the union of the head terms. (head term map should be disjoint.)
  def + (that : Instrumentation): Instrumentation = {
    assert((headTerms.keys.toSet intersect that.headTerms.keys.toSet).isEmpty) // todo: use eldarica assertions

    Instrumentation(constraint &&& that.constraint, headTerms ++ that.headTerms)
  }
}

object Instrumentation {
  // the product of two sequences of instrumentations
  def product(instrs1 : Seq[Instrumentation],
              instrs2 : Seq[Instrumentation]) : Seq[Instrumentation] =
    for(instr1 <- instrs1; instr2 <- instrs2) yield instr1 + instr2
}
