package lazabs.horn.concurrency
import java.io.{File, PrintWriter,FileWriter}
import java.nio.file.Path
import ap.parser._
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.preprocessor.HornPreprocessor.VerificationHints

class GraphTranslator(hornClauses : Seq[HornClauses.Clause],file:String) {

  import HornClauses.Clause

  println(file.substring(file.lastIndexOf("/")+1))
  val fileName=file.substring(file.lastIndexOf("/")+1)
  //println(fileName)
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


class GraphTranslator_hint(hornClauses : Seq[HornClauses.Clause],file:String,hints:VerificationHints) {

  println("---debug---")

  for((head,templateList)<-hints.getPredicateHints()) { //loop for head
    println(head)
    for(oneHint <- templateList){ //loop for every template in the head
      println(oneHint)
      //parse the hint expression to binary tree
      //build graphviz form from that tree



      //write graphviz form to .gv file
      val fileName=file.substring(file.lastIndexOf("/")+1)
      val pathName= "graphs/"+fileName+".hints.graphs"+"/"
      val hintFileName=head.toString().take(head.toString().indexOf("/"))+":"+oneHint.toString()+".gv"
      val hintFile = new File(pathName)
      hintFile.mkdir() //create fileName.hints.graphs directory
      val writer = new PrintWriter(new FileWriter(pathName+hintFileName)) //create location:template.gv file
      writer.write("digraph dag {"+"\n") //write some dummy content
      writer.write("0 [label=\"inv_main15\"];"+"\n")
      writer.write("1 [label=\"inv_main6\"];"+"\n")
      writer.write("1->0"+"\n")
      writer.write("0->1"+"\n")
      writer.write("}"+"\n")


      writer.close()
    }
  }


}

