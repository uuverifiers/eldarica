package lazabs.horn.concurrency
import java.io.{File, PrintWriter}
import ap.terfor.preds.Predicate
import ap.parser.IAtom
import lazabs.GlobalParameters
import lazabs.horn.concurrency.DrawHornGraph.{HornGraphType, addQuotes}
import lazabs.horn.concurrency.HintsSelection.replaceMultiSamePredicateInBody
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}

import scala.:+


class FormLearningLabels (simpClauses:Clauses,clausesInCE:Clauses){
//  val simpClauses=clauseCollection.simplifiedClause
//  val clausesInCE=clauseCollection.clausesInCounterExample
  //hints: VerificationHints
  class predicateNodeInfo(nodeName:String,index:Int){
    val name=nodeName
    var nodeIndex= index
    var predecessorNameList:List[String]=List()
    var successorNameList:List[String]=List()
    var successorIndexList:List[Int]=List()
    var transitiveNameList:List[String]=List()
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

  def getStrongConnectedComponentPredicateList(): (Map[String,Int],List[(String,String)]) ={
    var transitiveEdgeList:List[(String,String)]=List()
    var nodeCounter=0
    var predicateNameSet:Set[String]=Set()
    var predicateName2NodeMap:Map[String,predicateNodeInfo]=Map()//Map("Initial"->new predicateNodeInfo("Initial",nodeCounter))
    for (clause<-simpClauses;p<-clause.allAtoms){
      if (!predicateNameSet.contains(p.pred.name))
        {
          predicateName2NodeMap=predicateName2NodeMap.updated(p.pred.name,new predicateNodeInfo(p.pred.name,nodeCounter))
          nodeCounter+=1
          predicateNameSet+=p.pred.name
        }

    }
    //build and visualize graph
    val writerPredicateGraph = new PrintWriter(new File(GlobalParameters.get.fileName + "." + "circles" + ".gv"))
    var predicateNameMap=Set[String]()
    var edgeSet:Set[Tuple2[String,String]]=Set()
    val controlPrefix="CONTROL_"
    writerPredicateGraph.write("digraph dag {" + "\n")
    for(clause<-simpClauses) {
      //create head node
      val headName=clause.head.pred.name
      if (!predicateNameMap.contains(headName))
        addNodeForCircleGraph(headName)

      for (body<-clause.body){
        //create body node
        val bodyName = body.pred.name
        if (!predicateNameMap.contains(bodyName))
          addNodeForCircleGraph(bodyName)
        //add edge
        if (!edgeSet.contains(Tuple2(headName,bodyName))) {
          addAEdgeForCircleGraph(headName,bodyName)
          edgeSet=edgeSet+Tuple2(headName,bodyName)
        }
      }
    }

    //todo:add transitive edge
    //initialize transitiveNameList to include its next hop neighbor and itself
//    for(p<-predicateName2NodeMap) {
//      p._2.transitiveNameList=p._2.successorNameList:+p._1
//    }
    //draw transitive edge
    for (p<-predicateName2NodeMap;successorName<-p._2.successorNameList){
      transitiveEdge(p._2,predicateName2NodeMap(successorName))
    }
    def transitiveEdge(initialNode: predicateNodeInfo, nextNode: predicateNodeInfo): Unit = {
      for (pName <- nextNode.successorNameList) {
        if (!initialNode.transitiveNameList.contains(pName)) {
          initialNode.transitiveNameList :+= pName
          writerPredicateGraph.write(addQuotes(initialNode.name) + " -> " + addQuotes(pName) + " [label=" + "t" + "]" + "\n")
          //if (!transitiveEdgeList.contains((initialNode.name,pName)))
          transitiveEdgeList:+=(initialNode.name,pName)
          transitiveEdge(initialNode, predicateName2NodeMap(pName))
        }
      }
    }
    writerPredicateGraph.write("}" + "\n")
    writerPredicateGraph.close()
    def addNodeForCircleGraph(nodeName:String): Unit ={
      writerPredicateGraph.write(addQuotes(nodeName) +
        " [label=" + addQuotes(nodeName) + " shape=" + "box" + "];" + "\n")
      predicateNameMap+=nodeName
    }
    def addAEdgeForCircleGraph(headName:String,bodyName:String): Unit ={
      writerPredicateGraph.write(addQuotes(bodyName) + " -> " + addQuotes(headName) + " [label=" + "scc" + "]" +"\n")
      predicateName2NodeMap(headName).predecessorNameList:+=bodyName
      predicateName2NodeMap(bodyName).successorNameList:+=headName
      predicateName2NodeMap(bodyName).successorIndexList:+=predicateName2NodeMap(headName).nodeIndex
    }

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
    //var predicateOccurrenceMap:Map[String,Int]=(for(clause<-simpClauses;p<-clause.predicates if (p.name!="FALSE") ) yield (p.name->0)).toMap
    var predicateOccurrenceMap:Map[String,Int]=(for(clause<-simpClauses;p<-clause.allAtoms ) yield (p.pred.name->0)).toMap
    //predicateOccurrenceMap+=("Initial"->0)
    for (c<-circles;p<-c) if (predicateOccurrenceMap.keySet.contains(p)){
      //predicateOccurrenceMap=predicateOccurrenceMap.updated(p,predicateOccurrenceMap(p)+1)
      predicateOccurrenceMap=predicateOccurrenceMap.updated(p,1)
    }
    //mark self-cycle node to 1
    for(p<-predicateOccurrenceMap.keys) if(predicateName2NodeMap(p).successorNameList.contains(p))
      predicateOccurrenceMap=predicateOccurrenceMap.updated(p,1)

    //println(predicateOccurrenceMap)
    (predicateOccurrenceMap,transitiveEdgeList)
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

  def getPredicateOccurenceInClauses(): Map[String,Int] ={
    //form predicate head occurrence in clauses
    //var predicateOccurrenceMap:Map[String,Int]=(for(clause<-simpClauses;p<-clause.allAtoms if (p.pred.name!="FALSE") ) yield (p.pred.name->0)).toMap
    var predicateOccurrenceMap:Map[String,Int]=(for(clause<-simpClauses;p<-clause.allAtoms ) yield (p.pred.name->0)).toMap
    predicateOccurrenceMap+=("Initial"->0)
    for(clause<-simpClauses){
      if (clause.body.isEmpty){
        if (predicateOccurrenceMap.keySet.contains(clause.head.pred.name))
          predicateOccurrenceMap=predicateOccurrenceMap.updated(clause.head.pred.name,predicateOccurrenceMap(clause.head.pred.name)+1)
        predicateOccurrenceMap=predicateOccurrenceMap.updated("Initial",predicateOccurrenceMap("Initial")+1)
      } else{
        for (a<-clause.allAtoms){
          if (predicateOccurrenceMap.keySet.contains(a.pred.name))
            predicateOccurrenceMap=predicateOccurrenceMap.updated(a.pred.name,predicateOccurrenceMap(a.pred.name)+1)
        }
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