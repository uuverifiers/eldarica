package lazabs.horn.concurrency
import java.io.{File, FileWriter, PrintWriter}

import ap.parser._
import lazabs.horn.abstractions.VerificationHints._
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.preprocessor.HornPreprocessor.VerificationHints

class GraphTranslator(hornClauses : Seq[HornClauses.Clause],file:String) {

  import HornClauses.Clause

  println(file.substring(file.lastIndexOf("/")+1))
  val fileName=file.substring(file.lastIndexOf("/")+1)
  //println(fileName)
  //val writer = new PrintWriter(new File("graphs/"+fileName+".gv"))
  val writer = new PrintWriter(new File("../graphs/"+fileName+".gv")) //python path

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
  var nodeCount:Int=0
  var root=new TreeNode
  var logString:String="" //store node information
  println("---debug---")
  for((head,templateList)<-hints.getPredicateHints()) { //loop for head
    println(head)
    for(oneHint <- templateList){ //loop for every template in the head

      println(oneHint)
      val category=oneHint.toString.take(oneHint.toString.indexOf("("))



      //write graphviz form to .gv file
      val fileName=file.substring(file.lastIndexOf("/")+1)
      //val pathName= "graphs/"+fileName+".hints.graphs"+"/"
      val pathName= "../graphs/"+fileName+".hints.graphs"+"/" //python path
      val hintFileName=head.toString().take(head.toString().indexOf("/"))+":"+oneHint.toString()+".gv"
      val hintFile = new File(pathName)
      hintFile.mkdir() //create fileName.hints.graphs directory


      val writer = new PrintWriter(new FileWriter(pathName+hintFileName)) //create location:template.gv file
      writer.write("digraph dag {"+"\n")


      //root=new TreeNode
      var rootMark=root

      root.data=Map(nodeCount ->head.toString()) //first node is template head
      println(nodeCount + " [label=\""+ head.toString() +"\"];")
      logString=logString+(nodeCount + " [label=\""+ head.toString() +"\"];"+"\n")
      nodeCount=nodeCount+1
      root.lchild = new TreeNode(Map(nodeCount->category.toString())) //second node is template category
      println(nodeCount + " [label=\""+ category.toString() +"\"];")
      logString=logString+(nodeCount + " [label=\""+ category.toString() +"\"];"+"\n")
      nodeCount=nodeCount+1
      root=root.lchild






//      writer.write("digraph dag {"+"\n") //write some dummy content
//      writer.write("0 [label=\""+head+"\"];"+"\n") //root node is locaton/head
//      writer.write("1 [label=\""+category+"\"];"+"\n")//second node is hint's category
//      writer.write("0->1"+"\n")
//      writer.write("}"+"\n")
      translateHint(oneHint)
      nodeCount=0
      root=new TreeNode






      println("Tree:")
      BinarySearchTree.preOrder(rootMark)
      logString=logString+BinarySearchTree.relationString
      BinarySearchTree.relationString=""

      writer.write(logString)
      writer.write("}"+"\n")
      logString=""

      writer.close()


    }
  }

  def translateHint(h:VerifHintElement):Unit= h match{
    case VerifHintInitPred(p) => translateExpr(p)
    case VerifHintTplPred(p,_) => translateExpr(p)
    case VerifHintTplPredPosNeg(p,_) => translateExpr(p)
    case VerifHintTplEqTerm(t,_) => translateExpr(t)
    case VerifHintTplInEqTerm(t,_) => translateExpr(t)
    case VerifHintTplInEqTermPosNeg(t,_) => translateExpr(t)

  }

  def translateExpr(e:IExpression):Unit= {
    //println(e)

    e match{
      case IPlus(t1,t2)=> {

        root.lchild = new TreeNode(Map(nodeCount->"+"))
        root=root.lchild
        println(nodeCount + " [label=\""+ "+" +"\"];")
        logString=logString+(nodeCount + " [label=\""+ "+" +"\"];"+"\n")
        nodeCount=nodeCount+1



      }
      case ITimes(coeff,t)=> {

        root.lchild = new TreeNode(Map(nodeCount->"*"))
        root=root.lchild
        println(nodeCount + " [label=\""+ "*" +"\"];")
        logString=logString+(nodeCount + " [label=\""+ "*" +"\"];"+"\n")
        nodeCount=nodeCount+1
        root.rchild = new TreeNode(Map(nodeCount->coeff.toString()))
        println(nodeCount + " [label=\""+ coeff +"\"];")
        logString=logString+(nodeCount + " [label=\""+ coeff +"\"];"+"\n")
        nodeCount=nodeCount+1
      }

      case IIntFormula(rel,t)=> {
        if(rel.toString=="EqZero"){
          root.lchild = new TreeNode(Map(nodeCount->"="))
          root=root.lchild
          println(nodeCount + " [label=\""+ "=" +"\"];")
          logString=logString+(nodeCount + " [label=\""+ "=" +"\"];"+"\n")
          nodeCount=nodeCount+1
          root.rchild = new TreeNode(Map(nodeCount->"0"))
          println(nodeCount + " [label=\""+ "0" +"\"];")
          logString=logString+(nodeCount + " [label=\""+ "0" +"\"];"+"\n")
          nodeCount=nodeCount+1
        }
        if(rel.toString=="GeqZero"){
          root.lchild = new TreeNode(Map(nodeCount->">="))
          root=root.lchild
          println(nodeCount + " [label=\""+ ">=" +"\"];")
          logString=logString+(nodeCount + " [label=\""+ ">=" +"\"];"+"\n")
          nodeCount=nodeCount+1
          root.rchild = new TreeNode(Map(nodeCount->"0"))
          println(nodeCount + " [label=\""+ "0" +"\"];")
          logString=logString+(nodeCount + " [label=\""+ "0" +"\"];"+"\n")
          nodeCount=nodeCount+1
        }

      }
      case IVariable(index)=> {
        if(root.rchild==null){
          root.rchild = new TreeNode(Map(nodeCount->("_"+index.toString)))
          //root=root.lchild
        }else if(root.lchild==null){
          root.lchild = new TreeNode(Map(nodeCount->("_"+index.toString)))
          //root=root.rchild
        }

        println(nodeCount + " [label=\""+ "_"+index +"\"];")
        logString=logString+(nodeCount + " [label=\""+ "_"+index +"\"];"+"\n")
        nodeCount=nodeCount+1
      }
      case IBoolLit(value)=>println("IBoolLit")
      case IBinFormula(j,f1,f2)=>println("IBinFormula")
      case IFormulaITE(cond,left,right)=>println("IFormulaITE")
      case IConstant(c)=> print("constant");

      case IEpsilon(cond)=> println("IEpsilon");
      case IAtom(pred,args)=> println("IAtom");
      case IFunApp(fun,args)=>println("IFunApp");
      case ITrigger(patterns,subformula)=>println("ITrigger");
      case ITermITE(cond,left,right)=>println("ITermITE")
      case INamedPart(name,subformula)=>println("INamedPart")
      case IIntLit(value)=>println("IIntLit")
      case _=>println("?")
    }
    for (subExpr <- e.subExpressions) {



      translateExpr(subExpr)

    }



  }
}

class TreeNode{
  var data:Map[Int,String]=Map(0->"0")
  var lchild:TreeNode = null
  var rchild:TreeNode = null
  var parent:TreeNode = null

  def this(data:Map[Int,String]){
    this()
    this.data = data
  }
}

object BinarySearchTree {

  var relationString:String="" //store node relation information
  def preOrder(root: TreeNode): Unit = {
    if (root != null) {

      //println(root.data)
      val (k,v) = root.data.head

      if(root.lchild!=null){
        val (l_key,l_value)=root.lchild.data.head
        println(k+"->"+l_key)
        relationString=relationString+(k+"->"+l_key+"\n")
      }
      if(root.rchild!=null){
        val (r_key,r_value)=root.rchild.data.head
        println(k+"->"+r_key)
        relationString=relationString+(k+"->"+r_key+"\n")
      }




      preOrder(root.lchild)
      //print(root.data.keys + "\n")
      preOrder(root.rchild)
      //print(root.data.keys + "\n")

    }

  }

  def inOrder(root: TreeNode): Unit = {
    if (root != null) {
      inOrder(root.lchild)
      println(root.data)
      inOrder(root.rchild)
    }
  }


}