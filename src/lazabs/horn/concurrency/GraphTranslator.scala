package lazabs.horn.concurrency

import ap.parser._
import lazabs.horn.bottomup.HornClauses

class GraphTranslator(hornClauses : Seq[HornClauses.Clause]) {

  import HornClauses.Clause

  // println(hornClauses)

  println("digraph dag {")

  val predicates =
    (HornClauses allPredicates hornClauses).toList sortBy (_.name)
  val predIndex =
    (for ((p, n) <- predicates.iterator.zipWithIndex) yield (p -> n)).toMap

  for (p <- predicates)
    println("" + predIndex(p) + " [label=\"" + p.name + "\"];")

  for (Clause(IAtom(phead, _), body, _) <- hornClauses;
       if phead != HornClauses.FALSE;
       IAtom(pbody, _) <- body) {
    println(predIndex(pbody) + " -> " + predIndex(phead))
  }

  println("}")

}
