package lazabs.horn.concurrency

import java.io.{File, PrintWriter}
import java.nio.file.Path

import ap.parser._
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.preprocessor.HornPreprocessor.VerificationHints

class GraphTranslator(hornClauses : Seq[HornClauses.Clause],file:String,hints:VerificationHints) {

  import HornClauses.Clause

  println(file.substring(file.lastIndexOf("/")+1))
  val fileName=file.substring(file.lastIndexOf("/")+1)
  println(fileName)
  val writer = new PrintWriter(new File("graphs/"+fileName+".gv"))

  // println(hornClauses)

  println("digraph dag {")
  writer.write("digraph dag {"+"\n")

  val predicates =
    (HornClauses allPredicates hornClauses).toList sortBy (_.name)
  val predIndex =
    (for ((p, n) <- predicates.iterator.zipWithIndex) yield (p -> n)).toMap

  for (p <- predicates){
    println("" + predIndex(p) + " [label=\"" + p.name + "\"];")
    writer.write("" + predIndex(p) + " [label=\"" + p.name + "\"];"+"\n")
  }

  for (Clause(IAtom(phead, _), body, _) <- hornClauses;
       if phead != HornClauses.FALSE;
       IAtom(pbody, _) <- body) {
    println(predIndex(pbody) + " -> " + predIndex(phead))
    writer.write(predIndex(pbody) + " -> " + predIndex(phead)+"\n")
  }

  println("}")
  writer.write("}"+"\n")
  writer.close()
}
