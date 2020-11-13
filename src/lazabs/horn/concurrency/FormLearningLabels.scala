package lazabs.horn.concurrency
import java.io.{File, PrintWriter}

import ap.terfor.preds.Predicate
import ap.parser.IAtom
import lazabs.GlobalParameters
import lazabs.horn.concurrency.DrawHornGraph.addQuotes
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}


class FormLearningLabels (clauseCollection: ClauseInfo){
  val simpClauses=clauseCollection.simplifiedClause
  val clausesInCE=clauseCollection.clausesInCounterExample
  //hints: VerificationHints
  class predicateNodeInfo(nodeName:String,index:Int){
    val name=nodeName
    var nodeIndex= index
    var predecessorNameList:List[String]=List()
    var successorNameList:List[String]=List()
    var successorIndexList:List[Int]=List()
    def prettyPrint(): Unit ={
      println(nodeIndex+":"+name)
      print("predecessors:")
      for (p<-predecessorNameList) print(p+",")
      println
      print("successors:")
      for (s<-successorNameList) print(s+",")
      println
    }
  }

  def getStrongConnectedComponentPredicateList(): Map[String,Int] ={
    var nodeCounter=0
    var predicateNameSet:Set[String]=Set()
    var predicateName2NodeMap:Map[String,predicateNodeInfo]=Map()
    for (clause<-simpClauses;p<-clause.predicates){
      if (!predicateNameSet.contains(p.name))
        {
          predicateName2NodeMap=predicateName2NodeMap.updated(p.name,new predicateNodeInfo(p.name,nodeCounter))
          nodeCounter+=1
          predicateNameSet+=p.name
        }

    }
    //build and visualize graph
    val writerPredicateGraph = new PrintWriter(new File(GlobalParameters.get.fileName + "." + "circles" + ".gv"))
    writerPredicateGraph.write("digraph dag {" + "\n")
    for(clause<-simpClauses) {
      //create head node
      val headName=clause.head.pred.name
      writerPredicateGraph.write(addQuotes(headName) +
        " [label=" + addQuotes(headName)  + " shape=" + "box" + "];" + "\n")
      for (body<-clause.body){
        //create body node
        val bodyName=body.pred.name
        writerPredicateGraph.write(addQuotes(bodyName) +
          " [label=" + addQuotes(bodyName)  + " shape=" + "box" + "];" + "\n")
        //add edge
        writerPredicateGraph.write(addQuotes(bodyName) + " -> " + addQuotes(headName) + "\n")
        predicateName2NodeMap(headName).predecessorNameList:+=bodyName
        predicateName2NodeMap(bodyName).successorNameList:+=headName
        predicateName2NodeMap(bodyName).successorIndexList:+=predicateName2NodeMap(headName).nodeIndex
      }
    }
    writerPredicateGraph.write("}" + "\n")
    writerPredicateGraph.close()

    //form g: Map[Int, List[Int]]
    val g = for (node<-predicateName2NodeMap.values) yield (node.nodeIndex-> node.successorIndexList)
    //find out strong connected graph
    val x=new TarjanRecursive
    val cir=x.apply(g.toMap)
    val predicateIndex2NodeMap = (for (node<-predicateName2NodeMap.values) yield node.nodeIndex->node).toMap
    val circles = for (c<-cir if (c.size>1)) yield for(i<-c) yield predicateIndex2NodeMap(i).name
    //for (c<-circles) println(c.toString())

      //dfs visits
//    for (ps<-predicateName2NodeMap.values) ps.prettyPrint()
//    println("---------------")
//    dfs(predicateName2NodeMap)


    //form predicate node occurrence in strong connected graph
    var predicateOccurrenceMap:Map[String,Int]=(for(clause<-simpClauses;p<-clause.predicates if (p.name!="FALSE") ) yield (p.name->0)).toMap
    for (c<-circles;p<-c) if (predicateOccurrenceMap.keySet.contains(p)){
      //predicateOccurrenceMap=predicateOccurrenceMap.updated(p,predicateOccurrenceMap(p)+1)
      predicateOccurrenceMap=predicateOccurrenceMap.updated(p,1)
    }
    //mark self-cycle node to 1
    for(p<-predicateOccurrenceMap.keys) if(predicateName2NodeMap(p).successorNameList.contains(p))
      predicateOccurrenceMap=predicateOccurrenceMap.updated(p,1)

    //println(predicateOccurrenceMap)
    predicateOccurrenceMap
  }

  def traversal(node:predicateNodeInfo,nodeMap:Map[String,predicateNodeInfo]): Unit ={
    for (nextNode<-node.successorNameList) if (!node.successorNameList.isEmpty){
      node.successorNameList=node.successorNameList.diff(List(nextNode))
      println(node.name+" -> ",nextNode)
      traversal(nodeMap(nextNode),nodeMap)
    }
  }

  def dfs(nodeList:Map[String,predicateNodeInfo]): Unit ={
    for (node<-nodeList.values){
      traversal(node,nodeList)
    }

  }

  def getPredicateOccurenceInClauses(): Map[Predicate,Int] ={
    //form predicate head occurrence in clauses
    var predicateOccurrenceMap:Map[Predicate,Int]=(for(clause<-simpClauses;p<-clause.predicates if (p.name!="FALSE") ) yield (p->0)).toMap
    for(clause<-simpClauses){
      for (p<-clause.predicates) if (predicateOccurrenceMap.keySet.contains(p)){
        predicateOccurrenceMap=predicateOccurrenceMap.updated(p,predicateOccurrenceMap(p)+1)
        //new Predicate("Initial",0)
      }
    }
    predicateOccurrenceMap
  }


}

class TarjanRecursive {

  /**
   * The algorithm takes a directed graph as input, a
   * nd produces a partition of the graph's vertices into the graph's strongly connected components.
   * @param g the graph
   * @return the strongly connected components of g
   */
  def apply(g: Map[Int, List[Int]]): scala.collection.mutable.Buffer[scala.collection.mutable.Buffer[Int]] = {
    val s = scala.collection.mutable.Buffer.empty[Int]
    val s_set = scala.collection.mutable.Set.empty[Int]
    val index = scala.collection.mutable.Map.empty[Int, Int]
    val lowlink = scala.collection.mutable.Map.empty[Int, Int]
    val ret = scala.collection.mutable.Buffer.empty[scala.collection.mutable.Buffer[Int]]
    def visit(v: Int): Unit = {
      index(v) = index.size
      lowlink(v) = index(v)
      s += v
      s_set += v
      for (w <- g(v)) {
        if (!index.contains(w)) {
          visit(w)
          lowlink(v) = math.min(lowlink(w), lowlink(v))
        } else if (s_set(w)) {
          lowlink(v) = math.min(lowlink(v), index(w))
        }
      }
      if (lowlink(v) == index(v)) {
        val scc = scala.collection.mutable.Buffer.empty[Int]
        var w = -1
        while(v != w) {
          w = s.remove(s.size - 1)
          scc += w
          s_set -= w
        }
        ret += scc
      }
    }
    for (v <- g.keys) if (!index.contains(v)) visit(v)
    ret
  }

}