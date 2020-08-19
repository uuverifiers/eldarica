package lazabs.horn.concurrency

import java.io.{File, PrintWriter}

import ap.basetypes.IdealInt
import ap.parser.IExpression._
import ap.parser.{IExpression, _}
import lazabs.GlobalParameters
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}
import lazabs.horn.concurrency.Digraph
import play.api.libs.json._
import lazabs.horn.concurrency.BinarySearchTreeForGraphClass

import scala.collection.mutable.{ListBuffer, HashMap => MHashMap,Map => MuMap}


object DrawHornGraph {

  //todo:draw only hint graph without data flow
  def writeHornClausesGraphWithHintsToFile(file: String, simpClauses: Clauses,hints:VerificationHints): Unit = {

  }

  def genereateGNNInputs(file: String, simpClauses: Clauses): Unit ={
    val nodeIds=List(0,1,2,3,4,5)
    val binaryAdjacentcy=List(List(1,2),List(2,3))
    val tenaryAdjacency=List(List(1,2,3),List(2,3,1))
    val controlLocationIndices=List(1,2)
    val argumentIndices=List(4,5)
    val oneGraphGNNInput=Json.obj("nodeIds" -> nodeIds,
      "binaryAdjacentList" -> binaryAdjacentcy,"tenaryAdjacencyList" -> tenaryAdjacency,
      "controlLocationIndices"->controlLocationIndices,"argumentIndices"->argumentIndices)
    println(oneGraphGNNInput)


    println("Write GNNInput to file")
    val fileName = file.substring(file.lastIndexOf("/") + 1)
    val writer = new PrintWriter(new File("../trainData/" + fileName + ".JSON")) //python path
    writer.write(oneGraphGNNInput.toString())
    writer.close()

  }

  def writeGNNInputsToJSON(file: String,nodeIds:ListBuffer[Int],binaryAdjacentcy:ListBuffer[ListBuffer[Int]],
                           tenaryAdjacency:ListBuffer[ListBuffer[Int]],
                           controlLocationIndices:ListBuffer[Int],argumentIndices:ListBuffer[Int]): Unit ={
    val oneGraphGNNInput=Json.obj("nodeIds" -> nodeIds,
      "binaryAdjacentList" -> binaryAdjacentcy,"tenaryAdjacencyList" -> tenaryAdjacency,
      "controlLocationIndices"->controlLocationIndices,"argumentIndices"->argumentIndices)
    //println(oneGraphGNNInput)


    println("Write GNNInput to file")
    val writer = new PrintWriter(new File("../trainData/" + file + ".JSON")) //python path
    writer.write(oneGraphGNNInput.toString())
    writer.close()

  }

  def buildHornGraphInMemory(file: String, simpClauses: Clauses,hints:VerificationHints): Unit ={
    import scala.collection.mutable.Map
    val fileName = file.substring(file.lastIndexOf("/") + 1)
    val dot = new Digraph(comment = "Horn Graph")

    dot.node("A", "King Arthur",attrs = Map("constraint" -> "false","shape"->"\"diamond\""))
    dot.node("B", "Sir Bedevere the Wise")
    dot.node("L", "Sir Lancelot the Brave")


    dot.edges(Array(("A", "B"), ("A", "L")))
    dot.edge("B", "L", attrs = Map("constraint" -> "false","shape"->"\"diamond\""))
    println(dot.source())
    //dot.render(fileName = fileName+"-1.gv", directory = "../trainData/", view = true)


  }

  class GNNInput(){
    var GNNNodeID=0
    var hyperEdgeNodeID=0
    var TotalNodeID=0

    var nodeIds=new ListBuffer[Int]()
    var binaryAdjacentcy=new ListBuffer[ListBuffer[Int]]()
    var tenaryAdjacency=new ListBuffer[ListBuffer[Int]]()
    var controlLocationIndices=new ListBuffer[Int]()
    var argumentIndices=new ListBuffer[Int]()

    var nodeNameToIDMap =   MuMap[String, Int]()
    var controlFLowTenaryAdjacency=new ListBuffer[ListBuffer[Int]]()

    def incrementNodeIds(nodeName:String): Unit ={
      nodeIds+=GNNNodeID
      nodeNameToIDMap(nodeName)=GNNNodeID
      GNNNodeID+=1
    }
    def incrementArgumentIndicesAndNodeIds(nodeName:String): Unit ={
      argumentIndices+=GNNNodeID
      incrementNodeIds(nodeName)
    }
    def incrementControlLocationIndicesAndNodeIds(nodeName:String): Unit ={
      controlLocationIndices+=GNNNodeID
      incrementNodeIds(nodeName)
    }
  }

  def writeHornClausesGraphToFile(file: String, simpClauses: Clauses,hints:VerificationHints): Unit = {
    val dot = new Digraph(comment = "Horn Graph")
    val gnn_input=new GNNInput()

    println("Write horn to file")
    var edgeNameMap: Map[String, String] = Map()
    edgeNameMap += ("controlFlowIn" -> "control flow in")
    edgeNameMap += ("controlFlowOut" -> "control flow out")
    edgeNameMap += ("dataFlowIn" -> "data flow in")
    edgeNameMap += ("dataFlowOut" -> "data flow out")
    edgeNameMap += ("argument" -> "argument")
    edgeNameMap += ("dataFlowIn" -> "data flow in")
    edgeNameMap += ("dataFlowOut" -> "data flow out")
    edgeNameMap += ("astAnd" -> "AST &")
    edgeNameMap += ("condition" -> "condition")
    edgeNameMap += ("constantDataFlow" -> "constant data flow")
    edgeNameMap += ("dataFlow" -> "data flow")
    edgeNameMap += ("predicateAST" -> "predicateAST")
    edgeNameMap += ("dataFlowAST" -> "dataFlowAST")
    edgeNameMap += ("predicate" -> "prdicate")



    //turn on/off edge's label
    var edgeNameSwitch = true
    if (edgeNameSwitch == false) {
      for (key <- edgeNameMap.keys) {
        edgeNameMap += (key -> "")
        //edgeNameMap updated (key, " ")
      }
    }
    //println(file.substring(file.lastIndexOf("/")+1))
    val fileName = file.substring(file.lastIndexOf("/") + 1)
    //val writer = new PrintWriter(new File("trainData/"+fileName+".horn"))
    val writer = new PrintWriter(new File("../trainData/" + fileName + ".HornGraph")) //python path



    //write dataflow
    import IExpression._

    var controlFLowNodeList = ListBuffer[ControlFlowNode]()
    var clauseList = ListBuffer[ClauseTransitionInformation]()
    var clauseID = 0

    for (clause <- simpClauses) {
      writer.write("-------------" + "\n")
      writer.write(clause.toPrologString + "\n")

      //args in head
      var argsInHead = ListBuffer[Pair[String,ITerm]]()
      if (!clause.head.args.isEmpty) {
        for (arg <- clause.head.args) {
          argsInHead += Pair(arg.toString,arg)
        }
      }

      //args in body
      var argsInBody = ListBuffer[Pair[String,ITerm]]()
      if (!clause.body.isEmpty) {
        for (arg <- clause.body.head.args) {
          argsInBody += Pair(arg.toString,arg)
        }
      }


      //store head and body to controlFLowNodeList data structure
      var bodyName = "Initial"
      var currentControlFlowNodeArgumentListBody = new ListBuffer[ArgumentNode]()
      if (!clause.body.isEmpty) {
        bodyName = clause.body.head.pred.name
        for ((arg, index) <- clause.body.head.args.zipWithIndex) {
          currentControlFlowNodeArgumentListBody += new ArgumentNode(clause.head.pred.name,
            clause.body.head.pred.name, clause.body.head.pred.name, clauseID, arg, index)
        }
      }

      val currentControlFlowNodeBody = new ControlFlowNode(bodyName, currentControlFlowNodeArgumentListBody)
      if (!controlFLowNodeList.exists(_.name == bodyName)) { //if body is not in controlFLowNodeList
        controlFLowNodeList += currentControlFlowNodeBody
      }

      var currentControlFlowNodeArgumentListHead = new ListBuffer[ArgumentNode]()
      if (!clause.head.args.isEmpty) {
        for ((arg, index) <- clause.head.args.zipWithIndex) {
          currentControlFlowNodeArgumentListHead += new ArgumentNode(clause.head.pred.name,
            bodyName, clause.head.pred.name, clauseID, arg, index)
          //ArgumentNode(headName:String,bodyName:String,location:String,clauseID:Int,arg:String,argIndex:Int)
        }
      }
      val currentControlFlowNodeHead = new ControlFlowNode(clause.head.pred.name, currentControlFlowNodeArgumentListHead)
      if (!controlFLowNodeList.exists(_.name == clause.head.pred.name)) { //if head is not in controlFLowNodeList
        controlFLowNodeList += currentControlFlowNodeHead
      }

      val currentClause = new ClauseTransitionInformation(currentControlFlowNodeHead, currentControlFlowNodeBody, clauseID)
      clauseID = clauseID + 1

      //add head argument to node list
      for(arg<-currentClause.head.argumentList if !currentClause.head.argumentList.isEmpty){
        if(!currentClause.nodeList.exists(x=>x._1==arg.name)){
          currentClause.nodeList+=Pair(arg.name,arg.originalContent)
          if (!gnn_input.nodeNameToIDMap.contains(arg.name))
            gnn_input.incrementArgumentIndicesAndNodeIds(arg.name)
        }
      }
      //add body argument to node list
      for(arg<-currentClause.body.argumentList if !currentClause.body.argumentList.isEmpty){
        if(!currentClause.nodeList.exists(x=>x._1==arg.name)){
          currentClause.nodeList+=Pair(arg.name,arg.originalContent)
          if (!gnn_input.nodeNameToIDMap.contains(arg.name))
            gnn_input.incrementArgumentIndicesAndNodeIds(arg.name)
        }
      }



      writer.write("Head arguments: " + argsInHead.toString() + "\n")
      writer.write("Body arguments: " + argsInBody.toString() + "\n")
      val commonArg = argsInHead.filter(arg => argsInBody.contains(arg))
      currentClause.commonArg=commonArg
      //val x =argsInHead.toList.filterNot(arg=>argsInBody.toString().contains(arg.toString))
      writer.write("Common Arguments:" + commonArg.toString() + "\n")


      //head argument -common argument
      val relativeComplimentOfHeadArg = argsInHead.filterNot(arg => commonArg.contains(arg))
      // store relativeComplimentOfHeadArg to clause
      currentClause.relativeComplimentOfHeadArg=relativeComplimentOfHeadArg
      writer.write("relativeComplimentOfHeadArg:" + relativeComplimentOfHeadArg.toString() + "\n")


      //separate guard and data flow conjunct
      //if the expression is not a equation, then it is a guard
      //if the expression is a equation and head's argument -common argument not in the formula,then it is a guard
      //if the expression is a equation and there are element in the head's argument - common argument set, then it is a data flow
      var guardConjunct=ListBuffer[IFormula]()
      var dataFlowConjunct=ListBuffer[IFormula]()
      for (conjunct <- LineariseVisitor(
        clause.constraint, IBinJunctor.And)) conjunct match {
        case Eq(t1,t2)=>{
          if (!relativeComplimentOfHeadArg.exists(a => ContainsSymbol.apply(conjunct,a._2))) { //if the conjunct has no head arguments -common argument set
            guardConjunct+=conjunct
          }else{// if the equation has one or more head argument -common argument elements
            dataFlowConjunct+=conjunct
          }
        }
        case _=>{guardConjunct+=conjunct} //not a equation
      }


      def getElementsFromIFomula(e: IExpression, elementList: ListBuffer[String]): Unit = {

        e match {
          case IAtom(pred, args) => {
            elementList += pred.toString();
            for (a <- args if !args.isEmpty) {
              getElementsFromIFomula(a, elementList);
            }
          }
          case IBinFormula(j, f1, f2) => {
            getElementsFromIFomula(f1, elementList)
            getElementsFromIFomula(f2, elementList)
          }
          case IBoolLit(v) => {
            elementList += v.toString();
          }
          case IFormulaITE(cond, left, right) => {
            getElementsFromIFomula(cond, elementList)
            getElementsFromIFomula(left, elementList)
            getElementsFromIFomula(right, elementList)
          }
          case IIntFormula(rel, term) => {
            //elementList+=rel.toString();
            getElementsFromIFomula(term, elementList)
          }
          case INamedPart(pname, subformula) => {
            elementList += pname.toString;
            getElementsFromIFomula(subformula, elementList)
          }
          case INot(subformula) => {
            getElementsFromIFomula(subformula, elementList)
          }
          case IQuantified(quan, subformula) => {
            getElementsFromIFomula(subformula, elementList)
          }
          case ITrigger(patterns, subformula) => {
            for (p <- patterns if !patterns.isEmpty) {
              getElementsFromIFomula(p, elementList);
            }
            getElementsFromIFomula(subformula, elementList)
          }
          case IConstant(c) => {
            elementList += c.toString();
          }
          case IEpsilon(cond) => {
            getElementsFromIFomula(cond, elementList)
          }
          case IFunApp(fun, args) => {
            elementList += fun.toString();
            for (a <- args if !args.isEmpty) {
              getElementsFromIFomula(a, elementList);
            }
          }
          case IIntLit(v) => {
            elementList += v.toString();
          }
          case IPlus(t1, t2) => {
            getElementsFromIFomula(t1, elementList);
            getElementsFromIFomula(t2, elementList);
          }
          case ITermITE(cond, left, right) => {
            getElementsFromIFomula(cond, elementList);
            getElementsFromIFomula(left, elementList);
            getElementsFromIFomula(right, elementList);
          }
          case ITimes(coeff, subterm) => {
            elementList += coeff.toString();
            getElementsFromIFomula(subterm, elementList);
          }
          case IVariable(index) => {
            elementList += index.toString();
          }
          case _ => {}
        }
        //IFormula:IAtom, IBinFormula, IBoolLit, IFormulaITE, IIntFormula, INamedPart, INot, IQuantified, ITrigger
        //ITerm:IConstant, IEpsilon, IFunApp, IIntLit, IPlus, ITermITE, ITimes, IVariable
      }
      //extract all variable from guard
      var elementsInGuard=ListBuffer[String]()
      for(conjunct<-guardConjunct){
        getElementsFromIFomula(conjunct,elementsInGuard)
      }
      elementsInGuard=elementsInGuard.distinct //delete reapeatative element
      for(e<-elementsInGuard){ //delete integers
        try {
          e.toInt
          elementsInGuard-=e
        } catch {
          case e: Exception => {}
        }
      }
      writer.write("variables in guard: " + elementsInGuard.toString() + "\n")
      //todo:identify free variable
//      var freeVariables=ListBuffer[String]()
//      for(e<-elementsInGuard;headArg<-currentClause.head.argumentList if e==headArg.originalContent){
//        freeVariables+=e
//      }
//      writer.write("free variables: " + freeVariables.toString() + "\n")



      //preprocessing: parse conjuncts onece to replace guard or data flow with new guard and data flow
      def replaceArgument(args:ListBuffer[Pair[String,ITerm]],targetConjunct:IFormula,
                          guardConjunct:ListBuffer[IFormula],daraFlowConjunct:ListBuffer[IFormula],flowType:String) ={
        var tempGuardConjunct=for (gc<-guardConjunct) yield gc
        var tempDataFlowConjunct=for (gc<-daraFlowConjunct) yield gc
        var modifiedConjunct=targetConjunct
        val sp=new Simplifier()
        for((arg,argITerm)<-args if !args.isEmpty){
          if(ContainsSymbol(targetConjunct,argITerm)){
            //println("targetConjunct:"+targetConjunct)
            //println("args:"+args)
            var oldArg=new ConstantTerm("_")
            argITerm match{
              case IConstant(c)=>{
                //println("IConstant:"+argITerm)
                oldArg=c
              }
              case _=>{}
            }
            val newArg=new IConstant(new ConstantTerm(("_"+arg)))
            modifiedConjunct= sp(SimplifyingConstantSubstVisitor(modifiedConjunct,Map(oldArg->newArg)))  //replace arg to _arg
            //println("arg:"+arg)
            //println("modifiedConjunct:"+modifiedConjunct)
            if(!tempDataFlowConjunct.iterator.exists(p=>p.toString==sp(Eq(argITerm,newArg)).toString)){
              tempDataFlowConjunct+=sp(Eq(argITerm,newArg))
            }
            //println("new data flow conjunct:"+sp(Eq(argITerm,newArg)))
            //val Eq(a,b) = sp(Eq(argITerm,newArg))
          }
        }
        if(flowType=="guard"){
          tempGuardConjunct-=targetConjunct
          tempGuardConjunct+=modifiedConjunct //update guard
          //tempDataFlowConjunct+=sp(Eq(argITerm,newArg))
          //println("new data flow conjunct:"+sp(Eq(argITerm,newArg)))
        }else{
          tempGuardConjunct+=modifiedConjunct
          tempDataFlowConjunct-=targetConjunct
          //tempDataFlowConjunct+=sp(Eq(argITerm,newArg))
        }
        (tempGuardConjunct,tempDataFlowConjunct)
      }

      //preprocessing:if guard has headArgument-BodyArgument elements, replace element in the conjunct, add data flow
      for(gc<-guardConjunct){
        val (guardConjunctTemp,dataFlowConjunctTemp)=replaceArgument(currentClause.relativeComplimentOfHeadArg,
          gc,guardConjunct,dataFlowConjunct,"guard")
        guardConjunct=guardConjunctTemp
        dataFlowConjunct=dataFlowConjunctTemp
      }

      //preprocessing:if data flow has more than one head elements, replace element in conjunct to be a guard, add data flow
      writer.write("Data flow:\n")
      var dataFlowMap = Map[String, IExpression]() //argument->dataflow
      for (conjunct <- dataFlowConjunct) conjunct match {
        case Eq(lhs,rhs)=>{
          var dataFlowInfo=new EqConjunctInfo(conjunct,lhs,rhs,currentClause.relativeComplimentOfHeadArg)
          if(dataFlowInfo.moreThanOneHeadElement()){

            val (guardConjunctTemp,dataFlowConjunctTemp)=replaceArgument(currentClause.relativeComplimentOfHeadArg,
              conjunct,guardConjunct,dataFlowConjunct,"dataFlow")
            guardConjunct=guardConjunctTemp
            dataFlowConjunct=dataFlowConjunctTemp

            //writer.write("debug:"+lhs + "<-" + rhs+ "\n")
          }
        }
        case _=>{}
      }
//      //After preprocessing, the left dataflow conjuncts only has one head argument
//      for(conjunct<-dataFlowConjunct){
//        //val Eq(a,b)=conjunct
//        //writer.write(a+"="+b + "\n")
//        PrincessLineariser.printExpression(conjunct)
//      }

      // parse preprocessed data flow (move head to lhs and store it in dataFlowMap)
      for (headArg <- currentClause.relativeComplimentOfHeadArg) {
        //val Iconstant = IConstant(constant)
        val SumExtract = SymbolSum(headArg._2)
        for (conjunct <- dataFlowConjunct) conjunct match {
          case Eq(SumExtract(IdealInt.ONE | IdealInt.MINUS_ONE,
          otherTerms),
          rhs) => {
            if (!relativeComplimentOfHeadArg.exists(arg => rhs.toString.concat(otherTerms.toString).contains(arg))) {
              writer.write(headArg._2 + " <- " + (rhs --- otherTerms).toString + "\n")
              // eq: c = rhs - otherTerms
              val df = rhs --- otherTerms //record data flow IExpression
              dataFlowMap = dataFlowMap ++ Map(currentClause.head.getArgNameByContent(headArg._1) -> df)
            }
            //writer.write(headArg+"="+rhs+"-"+otherTerms+"\n")// eq: c = rhs - otherTerms
          }
          // data flow: rhs - otherTerms -> c
          case Eq(lhs,
          SumExtract(IdealInt.ONE | IdealInt.MINUS_ONE,
          otherTerms)) => {
            if (!relativeComplimentOfHeadArg.exists(arg => lhs.toString.contains(arg))) {
              writer.write(headArg._2 + " <- " + (lhs --- otherTerms).toString + "\n")
              // eq: c = rhs - otherTerms
              val df = lhs --- otherTerms
              //val sp=new ap.parser.Simplifier
              //sp.apply(lhs)
              dataFlowMap = dataFlowMap ++ Map(currentClause.head.getArgNameByContent(headArg._1) -> df)
            }
            //writer.write(headArg+"="+lhs+"-"+otherTerms+"\n")// data flow: lhs - otherTerms -> c
          }
          //          case EqLit(lhs,rhs)=>{writer.write(conjunct.getClass.getName+":"+conjunct+"\n")}
          //          case GeqZ(lhs)=>{writer.write(conjunct.getClass.getName+":"+conjunct+"\n")}
          //          case Geq(lhs,rhs)=>{writer.write(conjunct.getClass.getName+":"+conjunct+"\n")}
          case _ => {} //writer.write(conjunct.getClass.getName+":"+conjunct+"\n")
        }

      }

      var dataFlowList = ListBuffer[IExpression]()
      for ((arg, df) <- dataFlowMap) {
        dataFlowList += df
      }
      var dataFlowElementList = ListBuffer[String]() //get elements from data flow formula
      for (dataFlow <- dataFlowList) { //get dataflow's element list
        getElementsFromIFomula(dataFlow, dataFlowElementList)
      }

      //parse normal dataflow
      val (dataFLowAST,dataFlowNodeHashMap) = drawAST(currentClause, "dataFlow", dataFlowMap,
        MHashMap.empty[String,ITerm],edgeNameMap,gnn_input,dot)
      currentClause.dataFlowASTGraph=dataFLowAST
      //draw simple data flow
      for (comArg <- commonArg) {
        if (!dataFlowElementList.contains(comArg._1)) {
          writer.write(comArg._1 + "<-" + comArg._1 + "\n")

          for (bodyArg <- currentClause.body.argumentList; headArg <- currentClause.head.argumentList
               if headArg.originalContent == comArg._1 && bodyArg.originalContent == comArg._1) {
//                println("---debug---")
//                println(bodyArg.name)
//                println(headArg.dataFLowHyperEdge.name)
                currentClause.simpleDataFlowConnection = currentClause.simpleDataFlowConnection ++
                  Map(bodyArg ->headArg)
//                    ("\"" + bodyArg.name + "\"" + " -> " + "\"" + headArg.dataFLowHyperEdge.name+ "\"" +
//                      "[label=\"" + edgeNameMap("dataFlowIn") + "\"]" + "\n"))
                //                  + //data flow hyper edge already been drew when create this hyperedge
                //                  headArg.dataFLowHyperEdge.name + " -> " + headArg.name +
                //                  "[label=\""+edgeNameMap("dataFlowOut")+"\"]"+"\n"))
          }
        }
      }

      //draw constant data flow
      //if arguments in head are constant, add data flow constant ->arguments
      //head constan dataflow
      if (!argsInHead.isEmpty) {
        for ((arg, i) <- argsInHead.zipWithIndex) {
          try {
            arg._1.toInt
            //determine if argument is a constant number
            for (argument <- currentControlFlowNodeHead.argumentList)
              if (argument.originalContent == arg._1) {
                writer.write(argument.name + " <- " + arg._1 + "\n")
                //add constant data flow in to clause data structure
                argument.constantFlowInNode = "xxx"+currentClause.name + "_" + currentClause.clauseID +  "xxx" +
                  argument.name + "_constant_" + "\""+arg._1
                //println(argument.constantFlowInNode)
              }
          }
          catch {
            case ex: Exception => {}
          }
        }
      }

      //if arguments in body are constant, add guard constant == arguments
      //body constant dataflow
      if (!argsInBody.isEmpty) {
        for ((arg, i) <- argsInBody.zipWithIndex) {
          try {
            arg._1.toInt
            //determine if argument is a constant number
            for (argument <- currentControlFlowNodeBody.argumentList)
              if (argument.originalContent == arg._1) {
                writer.write(argument.name + "<-" + arg._1 + "\n")
                //add constant data flow in to clause data structure
                argument.constantFlowInNode = "xxx"+currentClause.name + "_" + currentClause.clauseID  + "xxx" +
                  argument.name + "_constant_" +arg._1
                //println(argument.constantFlowInNode)
              }
          }catch {
            case ex: Exception => {}
          }
        }
      }


      //guard
      writer.write("Guard:\n")
      var guardMap = Map[String, IFormula]()
      //naming guard with index
      for ((conjunct, i) <- guardConjunct.zipWithIndex) {
        //PrincessLineariser.printExpression(conjunct)
        //println()
        writer.write(conjunct + "\n")
        guardMap=guardMap++Map(("guard_" + i.toString) -> conjunct)
      }
      //draw guard
      val (guardASTList,guardNodeHashMap) = drawAST(currentClause, "guard", guardMap,dataFlowNodeHashMap,
        edgeNameMap,gnn_input,dot)
      for (ast <- guardASTList if !guardASTList.isEmpty) {
        currentClause.guardASTGraph = currentClause.guardASTGraph ++ Map(ast.astRootName -> ast.graphText)
      }
      //add currentClause to ClauseTransitionInformationList
      clauseList += currentClause
      writer.write("dataflow number:"+dataFlowMap.size+"\nguard number:"+guardMap.size+"\n")
    }

    //hints
    writer.write("Hints:\n")
    //store hints to control flow node
    for((head,hintList)<-hints.getPredicateHints();cn<-controlFLowNodeList){
      for(oneHint<-hintList){
        if(head.name==cn.name){
          cn.predicateList+=oneHint
        }
      }
    }
    //parse hint
    for(cfn<-controlFLowNodeList){
      cfn.getHintsList()
      val (hintsASTList,hintsNodeHashMap)=drawAST(cfn,cfn.argumentList,cfn.hintList,MHashMap.empty[String,ITerm],edgeNameMap)
      cfn.predicateGraphList=hintsASTList
    }



    writer.write("-----------\n")

    val predicates =
      (HornClauses allPredicates simpClauses).toList sortBy (_.name)
    val predIndex =
      (for ((p, n) <- predicates.iterator.zipWithIndex) yield (p -> n)).toMap


    writer.close()


    ///////////////////////////////////////////////////////////////


    println("Write horn to graph")
    val writerGraph = new PrintWriter(new File("../trainData/" + fileName + ".gv")) //python path


    writerGraph.write("digraph dag {" + "\n")
    //control flow node
    for (p <- predicates) {
      //println("" + predIndex(p) + " [label=\"" + p.name + "\"];")
      writerGraph.write("" + addQuotes(p.name)+ " [label=" + addQuotes(p.name) +" nodeName="+ addQuotes(p.name) +" class=cfn "+ " shape=\"rect\"" + "];" + "\n")
      dot.node(addQuotes(p.name), addQuotes(p.name),attrs = MuMap("nodeName"->addQuotes(p.name),
        "shape"->addQuotes("rect"),"class"->"cfn","GNNNodeID"->gnn_input.GNNNodeID.toString))
      gnn_input.incrementControlLocationIndicesAndNodeIds(p.name)
    }
    writerGraph.write("FALSE" + " [label=\"" + "FALSE" + "\""+" nodeName=FALSE"+" class=cfn " + " shape=\"rect\"" + "];" + "\n") //false node
    dot.node("FALSE","False",
      attrs = MuMap("nodeName"->"False","shape"->addQuotes("rect"),"class"->"cfn","GNNNodeID"->gnn_input.GNNNodeID.toString))
    gnn_input.incrementControlLocationIndicesAndNodeIds("FALSE")

    writerGraph.write("Initial" + " [label=\"" + "Initial" + "\"" +" nodeName=Initial"+" class=cfn "+ " shape=\"rect\"" + "];" + "\n") //initial node
    dot.node("Initial","Initial",
      attrs = MuMap("nodeName"->"Initial","shape"->addQuotes("rect"),"class"->"cfn","GNNNodeID"->gnn_input.GNNNodeID.toString))
    gnn_input.incrementControlLocationIndicesAndNodeIds("Initial")



    var ControlFowHyperEdgeList = new ListBuffer[ControlFowHyperEdge]() //build control flow hyper edge list


    //create control flow hyper edges, connections to control flow nodes, catch unique control flow node list
    var uniqueControlFLowNodeList = ListBuffer[ControlFlowNode]()
    for (clauseInfo <- clauseList) {
      //create control flow hyper edges and connections to control flow nodes
      //create control flow hyper edge nodes
      val cfheName=clauseInfo.controlFlowHyperEdge.name
      writerGraph.write(cfheName + " [label=\"Control flow hyperedge\""+" nodeName="+cfheName +" class=controlFlowHyperEdge"+ " shape=\"diamond\"" + "];" + "\n")
      dot.node(cfheName,addQuotes("Control flow hyperedge"),attrs = MuMap("nodeName"->cfheName,
        "shape"->addQuotes("diamond"),"class"->"controlFlowHyperEdge","hyperEdgeNodeID"->gnn_input.hyperEdgeNodeID.toString))
      gnn_input.hyperEdgeNodeID+=1
      //create edges of control flow hyper edge
      writerGraph.write(addQuotes(clauseInfo.body.name)+ " -> " + cfheName + " [label=\"" + edgeNameMap("controlFlowIn") + "\"]" + "\n")
      writerGraph.write(cfheName + " -> " + addQuotes(clauseInfo.head.name) + " [label=\"" + edgeNameMap("controlFlowOut") + "\"]" + "\n")
      dot.edge(addQuotes(clauseInfo.body.name),cfheName,attrs=MuMap("label"->addQuotes(edgeNameMap("controlFlowIn"))))
      dot.edge(addQuotes(cfheName),addQuotes(clauseInfo.head.name),attrs=MuMap("label"->addQuotes(edgeNameMap("controlFlowOut"))))
      //get unique control flow nodes
      if (!uniqueControlFLowNodeList.exists(_.name == clauseInfo.head.name)) {
        uniqueControlFLowNodeList += clauseInfo.head
      }
      if (!uniqueControlFLowNodeList.exists(_.name == clauseInfo.body.name)) {
        uniqueControlFLowNodeList += clauseInfo.body
      }
    }


    //create and connect to argument nodes
    for (controlFLowNode <- uniqueControlFLowNodeList; arg <- controlFLowNode.argumentList) {
      //create argument nodes
      writerGraph.write(addQuotes(arg.name) + " [label=\"" + arg.name + "\"" +" nodeName=argument"+arg.index+" class=argument "+ " head="+"\""+controlFLowNode.name+"\"" +" shape=\"oval\"" + "];" + "\n")
      dot.node(addQuotes(arg.name),addQuotes(arg.name),
        attrs = MuMap("nodeName"->("argument"+arg.index),"class"->"argument","head"->addQuotes(controlFLowNode.name),
          "GNNNodeID"->gnn_input.GNNNodeID.toString,"shape"->"oval"))

      //connect arguments to location
      writerGraph.write(addQuotes(arg.name) + " -> " + addQuotes(controlFLowNode.name) + "[label=" + addQuotes(edgeNameMap("argument")) +
        " style=\"dashed\"" + "]" + "\n")
      dot.edge(addQuotes(arg.name),addQuotes(controlFLowNode.name),attrs = MuMap("label"->addQuotes(edgeNameMap("argument")),
      "style"->"dashed"))
      gnn_input.binaryAdjacentcy+=ListBuffer(gnn_input.nodeNameToIDMap(arg.name),gnn_input.nodeNameToIDMap(controlFLowNode.name))
    }



    //    for (Clause(IAtom(phead, headArgs), body, _) <- simpClauses;
    //         //if phead != HornClauses.FALSE;
    //         IAtom(pbody, _) <- body) {  //non-initial control flow iteration
    //
    //    }


    //create guarded data flow node for this clause
    writerGraph.write("\n")

    for (clauseInfo <- clauseList) {
      var andName = ""
      if (clauseInfo.guardNumber > 1) { //create & node to connect constraints
        andName = "xxx" + clauseInfo.name + "_" + clauseInfo.clauseID + "xxx" + "_and"
        writerGraph.write(addQuotes(andName) + " [label=\"" + "&" + "\"" +" nodeName="+ "\"" +andName+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
        dot.node(andName,addQuotes("&"),attrs = MuMap("andName"->addQuotes(andName),"class"->"Operator","shape"->"rect"))
        gnn_input.incrementNodeIds(andName)
        clauseInfo.guardASTRootName = andName //store this node to clauses's guardASTRootName
      }
      //draw guard ast
      for ((rootName, ast) <- clauseInfo.guardASTGraph) { //create & node to connect constraints
        writerGraph.write(ast + "\n")
        if (clauseInfo.guardNumber > 1) { //connect constraints by &
          //writerGraph.write(clauseInfo.name + "_and"+"->"+rootName//ast.substring(0,ast.indexOf("[label")-1)
          writerGraph.write(addQuotes(rootName) + " -> " + addQuotes(andName)//ast.substring(0,ast.indexOf("[label")-1)
            + " [label=\"" + edgeNameMap("astAnd") + "\"" + "];" + "\n")
          dot.edge(addQuotes(rootName),addQuotes(andName),attrs = MuMap("label"->addQuotes( edgeNameMap("astAnd"))))
          gnn_input.binaryAdjacentcy+=ListBuffer(gnn_input.nodeNameToIDMap(rootName),gnn_input.nodeNameToIDMap(andName))
        } else {
          clauseInfo.guardASTRootName = rootName
        }
      }

      //guard AST root point to control flow hyperedge
      if (!clauseInfo.guardASTRootName.isEmpty) {
        writerGraph.write(addQuotes(clauseInfo.guardASTRootName) + " -> " + addQuotes(clauseInfo.controlFlowHyperEdge.name)
          + " [label=\"" + edgeNameMap("condition") + "\"" + "];" + "\n")
        dot.edge(addQuotes(clauseInfo.guardASTRootName),addQuotes(clauseInfo.controlFlowHyperEdge.name),
          attrs = MuMap("label"->addQuotes(edgeNameMap("condition"))))
        gnn_input.tenaryAdjacency+=ListBuffer(gnn_input.nodeNameToIDMap(clauseInfo.controlFlowHyperEdge.from),
          gnn_input.nodeNameToIDMap(clauseInfo.guardASTRootName),
          gnn_input.nodeNameToIDMap(clauseInfo.controlFlowHyperEdge.to))
      }
      //if there is no guard add true condition
      if (clauseInfo.guardASTGraph.isEmpty) {
        writerGraph.write(addQuotes(clauseInfo.trueCondition) + " [label=\"" + "true" + "\"" +" nodeName="+addQuotes(clauseInfo.trueCondition)+" class=true"+ " shape=\"rect\"" + "];" + "\n") //add true node
        dot.node(addQuotes(clauseInfo.trueCondition),addQuotes("true"),attrs = MuMap("nodeName"->addQuotes(clauseInfo.trueCondition),"class"->"true","shape"->"rect"))
        gnn_input.incrementNodeIds(clauseInfo.trueCondition)
        writerGraph.write(addQuotes(clauseInfo.trueCondition) + " -> " + addQuotes(clauseInfo.controlFlowHyperEdge.name)//add edge to control flow hyper edges
          + " [label=\"" + edgeNameMap("condition") + "\"" + "];" + "\n")
        dot.edge(addQuotes(clauseInfo.trueCondition),addQuotes(clauseInfo.controlFlowHyperEdge.name),attrs = MuMap("label"->addQuotes(edgeNameMap("condition"))))
        gnn_input.tenaryAdjacency+=ListBuffer(gnn_input.nodeNameToIDMap(clauseInfo.controlFlowHyperEdge.from),
          gnn_input.nodeNameToIDMap(clauseInfo.trueCondition),
          gnn_input.nodeNameToIDMap(clauseInfo.controlFlowHyperEdge.to))
      }

      //draw data flow ast
      for (graphInfo <- clauseInfo.dataFlowASTGraph; argNode <- clauseInfo.head.argumentList if (graphInfo.argumentName == argNode.name)) {
        writerGraph.write(graphInfo.graphText + "\n") //draw AST
        writerGraph.write(addQuotes(graphInfo.astRootName) + " -> " + addQuotes(argNode.dataFLowHyperEdge.name) //connect to data flow hyper edge
          + " [label=\"" + edgeNameMap("dataFlow") + "\"" + "];" + "\n")
        argNode.dataFLowHyperEdge.fromData=graphInfo.astRootName
        dot.edge(addQuotes(graphInfo.astRootName),addQuotes(argNode.dataFLowHyperEdge.name),attrs = MuMap("label"->addQuotes(edgeNameMap("dataFlow"))))
      }
    }



    //draw data flow
    //draw guarded data flow hyperedge for head
    for (clauseInfo <- clauseList; headArg <- clauseInfo.head.argumentList; if !clauseInfo.head.argumentList.isEmpty) {
      //create data flow hyperedge node
      if(headArg.dataFLowHyperEdge.fromData!=""){
        drawDataFlowHyperEdge(clauseInfo,headArg)
      }
    }

    //draw constant data flow for head
    for (clauseInfo <- clauseList) {
      for (headArg <- clauseInfo.head.argumentList; if !clauseInfo.head.argumentList.isEmpty) {
        if (headArg.constantFlowInNode != "") {
          writerGraph.write(addQuotes(headArg.constantFlowInNode)
            + " [label=\"" + headArg.originalContent + "\"" +" nodeName="+ "\"" +headArg.constantFlowInNode+ "\"" + " class=Constant"+ "];" + "\n") //create constant node
          dot.node(addQuotes(headArg.constantFlowInNode),addQuotes(headArg.originalContent),
            attrs = MuMap("nodeName"->addQuotes(headArg.constantFlowInNode),"class"->"Constant"))
          gnn_input.incrementNodeIds(headArg.constantFlowInNode)
//          writerGraph.write("\"" + headArg.constantFlowInNode+ "\"" + " -> " + "\"" + headArg.dataFLowHyperEdge.name+"\"" //add edge to argument
//            + " [label=\"" + edgeNameMap("constantDataFlow") + "\"" + "];" + "\n")
          headArg.dataFLowHyperEdge.fromData=headArg.constantFlowInNode
          ///////
          drawDataFlowHyperEdge(clauseInfo,headArg)
        }
      }
      //draw constant data flow for body
      for (bodyArg <- clauseInfo.body.argumentList; if !clauseInfo.body.argumentList.isEmpty) {
        if (!bodyArg.constantFlowInNode.isEmpty) {
          writerGraph.write(addQuotes(bodyArg.constantFlowInNode)
            + " [label=\"" + bodyArg.originalContent + "\"" +" nodeName=" + addQuotes(bodyArg.constantFlowInNode) +" class=Constant"+ "];" + "\n") //create constant node
          dot.node(addQuotes(bodyArg.constantFlowInNode),addQuotes(bodyArg.originalContent),
            attrs = MuMap("nodeName"->addQuotes(bodyArg.constantFlowInNode),"class"->"Constant"))
          gnn_input.incrementNodeIds(bodyArg.constantFlowInNode)
          writerGraph.write(addQuotes(bodyArg.constantFlowInNode) + " -> " + addQuotes(bodyArg.name)//add edge to argument
            + " [label=\"" + edgeNameMap("constantDataFlow") + "\"" + "];" + "\n")
          dot.edge(addQuotes(bodyArg.constantFlowInNode) ,addQuotes(bodyArg.name),
            attrs = MuMap("label"->addQuotes(edgeNameMap("constantDataFlow"))))
          gnn_input.binaryAdjacentcy+=ListBuffer(gnn_input.nodeNameToIDMap(bodyArg.constantFlowInNode),
            gnn_input.nodeNameToIDMap(bodyArg.name))
          //bodyArg.dataFLowHyperEdge.fromData=bodyArg.constantFlowInNode
        }
      }
    }

    def drawDataFlowHyperEdge(clauseInfo:ClauseTransitionInformation,headArg:ArgumentNode): Unit ={
      writerGraph.write(addQuotes(headArg.dataFLowHyperEdge.name) +
        " [label=\""+headArg.dataFLowHyperEdge.name+"\""+" nodeName="+ "\""+ headArg.dataFLowHyperEdge.name+ "\"" +" class=DataFlowHyperedge" +" shape=\"diamond\"" + "];" + "\n")
      dot.node(addQuotes(headArg.dataFLowHyperEdge.name),addQuotes(headArg.dataFLowHyperEdge.name),
        attrs = MuMap("nodeName"->addQuotes(headArg.dataFLowHyperEdge.name),
          "class"->"DataFlowHyperedge","shape"->"diamond"))

      //create data flow hyperedge node coonections
      writerGraph.write(addQuotes(headArg.dataFLowHyperEdge.name) + " -> " + addQuotes(headArg.name) +
        "[label=\"" + edgeNameMap("dataFlowOut") + "\"]" + "\n")
      dot.edge(addQuotes(headArg.dataFLowHyperEdge.name),addQuotes(headArg.name),attrs = MuMap("label"->addQuotes(edgeNameMap("dataFlowOut"))))

      //guard AST root point to data flow hyperedge
      if (!clauseInfo.guardASTRootName.isEmpty) {
        writerGraph.write(addQuotes(clauseInfo.guardASTRootName) + " -> " + addQuotes(headArg.dataFLowHyperEdge.name) +
          "[label=\"" + edgeNameMap("dataFlowIn") + "\"]" + "\n")
        dot.edge(addQuotes(clauseInfo.guardASTRootName),addQuotes(headArg.dataFLowHyperEdge.name),attrs = MuMap("label"->addQuotes(edgeNameMap("dataFlowIn"))))
        headArg.dataFLowHyperEdge.fromASTRoot=clauseInfo.guardASTRootName
      }
      //if there is no guard add true condition to data flow hyperedge
      if (clauseInfo.guardASTGraph.isEmpty) {
        writerGraph.write(addQuotes(clauseInfo.trueCondition) + " -> " + addQuotes(headArg.dataFLowHyperEdge.name) //add edge to data flow hyper edges
          + " [label=\"" + edgeNameMap("condition") + "\"" + "];" + "\n")
        dot.edge(addQuotes(clauseInfo.trueCondition),addQuotes(headArg.dataFLowHyperEdge.name),attrs = MuMap("label"-> addQuotes(edgeNameMap("condition"))))
        headArg.dataFLowHyperEdge.fromASTRoot=clauseInfo.trueCondition
      }
      gnn_input.tenaryAdjacency+=ListBuffer(gnn_input.nodeNameToIDMap(headArg.dataFLowHyperEdge.fromData),
        gnn_input.nodeNameToIDMap(headArg.dataFLowHyperEdge.fromASTRoot),
        gnn_input.nodeNameToIDMap(headArg.dataFLowHyperEdge.to))
    }


    //draw simple data flow connection
    for (clauseInfo <- clauseList) {
      if (!clauseInfo.simpleDataFlowConnection.isEmpty) {
        for ((bodyArg, headArg) <- clauseInfo.simpleDataFlowConnection) {
          writerGraph.write(addQuotes(bodyArg.name) + " -> " + addQuotes(headArg.dataFLowHyperEdge.name) + "[label=\"" + edgeNameMap("dataFlowIn") + "\"]" + "\n")
          headArg.dataFLowHyperEdge.fromData=bodyArg.name
          drawDataFlowHyperEdge(clauseInfo,headArg)
          //writerGraph.write(connection)
        }
      }
    }

    writerGraph.write("\n\n\n\n")
    //draw hints
    //todo:store to dot structure and transform to GNN inputs
    if(GlobalParameters.get.hornGraphWithHints==true){
      for(cfn<-controlFLowNodeList){
        for (pre <- cfn.predicateGraphList) { //draw ast
          val predicateNodeName=pre.predicateName+"_"+pre.predicateType+ "_"+ pre.index
          writerGraph.write("\"" + predicateNodeName + "\"" + " [label=\""+predicateNodeName+"\" "+" nodeName="+ "\"" + predicateNodeName+ "\"" +" class=Predicate shape=\"rect\"];\n")
          writerGraph.write("\"" + pre.ASTRoot+ "\"" +" -> "+ "\"" + predicateNodeName + "\"" + "[label=\""+edgeNameMap("predicateAST")+"\" ];\n")
          writerGraph.write("\"" + predicateNodeName + "\"" +" -> "+ "\"" + pre.predicateName+ "\"" + "[label=\""+edgeNameMap("predicate")+"\" ];\n")
          writerGraph.write(pre.graphText + "\n")
        }
      }
    }

    //todo:check point . output horn graph and gnn input
    dot.save(fileName = fileName+"-auto"+".gv", directory = "../trainData/")
    //dot.render(fileName = fileName+"-auto"+".gv", directory = "../trainData/", view = false)
    writeGNNInputsToJSON(fileName,gnn_input.nodeIds,gnn_input.binaryAdjacentcy,gnn_input.tenaryAdjacency,
      gnn_input.controlLocationIndices,gnn_input.argumentIndices)




    writerGraph.write("}" + "\n")

    writerGraph.close()
  }

  def drawAST(cfn:ControlFlowNode,argumentList:ListBuffer[ArgumentNode],hints:ListBuffer[Triple[String,String,IExpression]],
              freeVariableMap:MHashMap[String,ITerm],
              edgeNameMap:Map[String,String]) = {
    var ASTGraph = ListBuffer[predicateGraph]()
    var nodeCount: Int = 0
    var hintCount: Int = 0
    var astNodeNamePrefix=""
    var root = new TreeNodeForGraph(Map((astNodeNamePrefix + nodeCount) -> "root"))
    var logString: String = "" //store node information
    var rootMark = root
    var rootName = ""
    var nodeHashMap:MHashMap[String,ITerm]=freeVariableMap
    def translateConstraint(e: IExpression, root: TreeNodeForGraph): Unit = {

      e match {
        case INot(subformula) => {
          //println("INOT")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "!"))
            logString = logString + ("\"" + nodeName + "\"" + " [label=\"" + "!" + "\""+" nodeName="+ "\"" + nodeName+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "!"))
            logString = logString + ("\"" + nodeName+ "\"" + " [label=\"" + "!" + "\"" +" nodeName="+ "\"" + nodeName + "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.rchild)
          }
        }
        case IAtom(pred, args) => {
          val p = pred.name
          //println("IAtom")
          if (root.lchild == null) {
            if (argumentList.exists(_.originalContent == p)) {
              root.lchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(p) -> (p)))
              logString = logString + ("\"" + cfn.getArgNameByContent(p) + "\"" +
                " [label=\"" + cfn.getArgNameByContent(p) + "\""+" nodeName="+ "\"" + cfn.getArgNameByContent(p) + "\"" +" class=argument"+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(p)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (p)))
              logString = logString + ("\"" + nodeName +"\"" + " [label=\"" + p + "\""+" nodeName="+ "\"" + nodeName+ "\"" +" class=pred"+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.lchild)
            }

          } else if (root.rchild == null) {
            if (argumentList.exists(_.originalContent == p)) {
              root.rchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(p) -> (p)))
              logString = logString + ("\"" + cfn.getArgNameByContent(p) + "\"" +
                " [label=\"" + cfn.getArgNameByContent(p) + "\""+" nodeName="+ "\"" + cfn.getArgNameByContent(p) + "\"" +" class=argument"+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(p)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (p)))
              logString = logString + ("\"" + nodeName + "\"" + " [label=\"" + p + "\""+" nodeName="+ "\"" + nodeName+ "\"" +" class=pred"+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.rchild)
            }
          }

        }
        case IBinFormula(junctor, f1, f2) => {
          //println("IBinFormula")
          val j = junctor.toString
          println(j.toString)
          if (root.lchild == null) {
            if (argumentList.exists(_.originalContent == j)) {
              root.lchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(j) -> (j)))
              logString = logString + ("\"" + cfn.getArgNameByContent(j) + "\"" +
                " [label=\"" + cfn.getArgNameByContent(j) + "\" "+ " nodeName="+ "\"" + cfn.getArgNameByContent(j) + "\"" +" class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(j)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (j)))
              logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + j + "\""+" nodeName="+ "\"" +nodeName + "\"" + " class=Operator "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            translateConstraint(f1, root.lchild)
            translateConstraint(f2, root.lchild)

          } else if (root.rchild == null) {
            if (argumentList.exists(_.originalContent == j)) {
              root.rchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(j) -> (j)))
              logString = logString + ( "\"" +cfn.getArgNameByContent(j) + "\""  +
                " [label=\"" + j + "\""+" nodeName="+ "\"" +cfn.getArgNameByContent(j)+ "\"" +" class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(j)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (j)))
              logString = logString + ( "\"" +nodeName + "\""  + " [label=\"" + j + "\""+" nodeName="+ "\"" + nodeName+ "\"" +" class=Operator "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            translateConstraint(f1, root.rchild)
            translateConstraint(f2, root.rchild)
          }


        }
        case IBoolLit(value) => {
          //println("IBoolLit")
          //println(value)
          val v = value.toString
          if (root.rchild == null) {
            if (argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" +cfn.getArgNameByContent(v)+ "\""  +
                " [label=\"" + cfn.getArgNameByContent(v) + "\""+" nodeName="+ "\"" +cfn.getArgNameByContent(v) + "\"" +" class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(v)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( "\"" +nodeName + "\""  + " [label=\"" + v + "\""+" nodeName="+ "\"" +nodeName + "\"" +" class=BoolValue "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
          } else if (root.lchild == null) {
            if (argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + cfn.getArgNameByContent(v) + "\"" +
                " [label=\"" + cfn.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + cfn.getArgNameByContent(v)+ "\"" +" class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(v)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( "\"" +nodeName+ "\""  + " [label=\"" + v + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=BoolValue "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
          }
          nodeCount = nodeCount + 1
        }
        case IConstant(constantTerm) => {
          val c = constantTerm.toString()
          //println("IConstant")
          //println(c)
          if (root.lchild == null) {
            if (argumentList.exists(_.originalContent == c)) {
              //              println(clause.body.getArgNameByContent(c))
              //              println(c)
              root.lchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(c) -> (c)))
              if(!cfn.nodeList.exists(x=>x._1==cfn.getArgNameByContent(c))){
                logString = logString + ( "\"" + cfn.getArgNameByContent(c) + "\"" +
                  " [label=\"" + cfn.getArgNameByContent(c) + "\""+" nodeName="+ "\"" + cfn.getArgNameByContent(c)+ "\"" +" class=argument "+"];" + "\n")
                cfn.nodeList+=Pair(cfn.getArgNameByContent(c),cfn.getArgNameByContent(c))
              }
              //              logString = logString + (clause.body.getArgNameByContent(c) +
              //                " [label=\"" + clause.body.getArgNameByContent(c) + "\"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(c)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,c,nodeHashMap, constantTerm)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (c)))
              if(!cfn.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + c + "\""+" nodeName="+ "\"" +nodeName + "\"" +" class=Constant "+"];" + "\n")
                cfn.nodeList+=Pair(nodeName,c)
              }
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
          } else if (root.rchild == null) {
            if (argumentList.exists(_.originalContent == c)) {
              root.rchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(c) -> (c)))
              if(!cfn.nodeList.exists(x=>x._1==cfn.getArgNameByContent(c))){
                logString = logString + ( "\"" + cfn.getArgNameByContent(c) + "\""  +
                  " [label=\"" + cfn.getArgNameByContent(c) + "\""+" nodeName="+ "\"" +cfn.getArgNameByContent(c)+ "\"" +" class=argument "+"];" + "\n")
                cfn.nodeList+=Pair(cfn.getArgNameByContent(c),cfn.getArgNameByContent(c))
              }
              rootName = checkASTRoot(nodeCount,cfn.getArgNameByContent(c),rootName)
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,c,nodeHashMap, constantTerm)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (c)))
              if(!cfn.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + ( "\"" +nodeName + "\""  + " [label=\"" + c + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=Constant "+"];" + "\n")
                cfn.nodeList+=Pair(nodeName,c)
              }
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
          }
          nodeCount = nodeCount + 1
        }
        case IEpsilon(cond) => {
          println("IEpsilon")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "IEpsilon"))
            logString = logString + ( "\"" +nodeName+ "\""  + " [label=\"" + "IEpsilon" + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=Operator "+"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "IEpsilon"))
            logString = logString + ( "\"" +nodeName + "\""  + " [label=\"" + "IEpsilon" + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=Operator "+"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.rchild)
          }
        }
        //case IFormula()=>println("IFormula")
        case IFormulaITE(cond, left, right) => {
          println("IFormulaITE")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "IFormulaITE"))
            logString = logString + ( "\"" +nodeName + "\""  + " [label=\"" + "IFormulaITE" + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=Formula"+"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.lchild)
            translateConstraint(left, root.lchild)
            translateConstraint(right, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "IFormulaITE"))
            logString = logString + ( "\"" +nodeName+ "\""  + " [label=\"" + "IFormulaITE" + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=Formula"+"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.rchild)
            translateConstraint(left, root.rchild)
            translateConstraint(right, root.rchild)

          }
        }
        case IFunApp(fun, args) => {
          println("IFunApp");
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "IFunApp"))
            logString = logString + ( "\"" +nodeName + "\""  + " [label=\"" + "IFunApp" + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=IFunApp"+"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.lchild)
            }

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "IFunApp"))
            logString = logString + ( "\"" +nodeName + "\""  + " [label=\"" + "IFunApp" + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=IFunApp"+"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.rchild)
            }

          }
        }
        case Eq(t1, t2) => {
          val eq = "="
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> eq))
            logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + eq + "\"" +" nodeName="+ "\"" +nodeName+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> eq))
            logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + eq + "\"" +" nodeName="+ "\"" +nodeName+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)

          }
        }
        case Geq(t1, t2) => {
          //println(t1+">="+t2)
          val geq = ">="
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> geq))
            logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + geq + "\""+" nodeName="+ "\"" +nodeName + "\"" +" class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> geq))
            logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + geq + "\""+" nodeName="+ "\"" +nodeName + "\"" +" class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)

          }
        }
        case EqLit(term, lit) => {
          val v = lit.toString()
          val eq = "="
          //println("="+v)
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> eq))
            logString = logString + ( "\"" +nodeName+  "\"" +" [label=\"" + eq + "\"" +" nodeName="+ "\"" +nodeName+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            if (argumentList.exists(_.originalContent == v)) {
              root.lchild.lchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" +cfn.getArgNameByContent(v) + "\""+
              " [label=\"" + cfn.getArgNameByContent(v) + "\""+" nodeName="+ "\"" +cfn.getArgNameByContent(v)+ "\"" +" class=argument "+"];" + "\n")
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, lit)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + v + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=Literal "+"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
            nodeCount = nodeCount + 1
            translateConstraint(term, root.lchild)
          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> eq))
            logString = logString + ( "\"" +nodeName+ "\"" + " [label=\"" + eq + "\"" +" nodeName="+ "\"" +nodeName+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (argumentList.exists(_.originalContent == v)) {
              root.rchild.rchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" +cfn.getArgNameByContent(v) + "\""+
              " [label=\"" + cfn.getArgNameByContent(v) + "\""+" nodeName="+ "\"" +cfn.getArgNameByContent(v)+ "\"" +" class=argument "+"];" + "\n")
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, lit)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild.rchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + v + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=Literal "+"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
            nodeCount = nodeCount + 1
            translateConstraint(term, root.rchild)

          }
        }
        case GeqZ(t) => {
          //println(">=0")
          val geq = ">="
          if (root.lchild == null) {
            val nn=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nn -> geq))
            logString = logString + ( "\"" +nn + "\"" + " [label=\"" + geq + "\"" +" nodeName="+ "\"" +nn+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,"0",nodeHashMap, 0)
            nodeHashMap=nodeHashMapOut
            val nodeName:String=nodeNameOut
            root.lchild.lchild = new TreeNodeForGraph(Map(nodeName -> ("0")))
            logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + "0" + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=Constant "+"];" + "\n")
            rootName = checkASTRoot(nodeCount,nodeName,rootName)
            nodeCount = nodeCount + 1
            translateConstraint(t, root.lchild)

          } else if (root.rchild == null) {
            val nn=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nn -> geq))
            logString = logString + ( "\"" +nn + "\"" + " [label=\"" + geq + "\"" +" nodeName="+ "\"" +nn+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,"0",nodeHashMap, 0)
            nodeHashMap=nodeHashMapOut
            val nodeName:String=nodeNameOut
            root.rchild.rchild = new TreeNodeForGraph(Map(nodeName -> ("0")))
            logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + "0" + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=Constant "+"];" + "\n")
            rootName = checkASTRoot(nodeCount,nodeName,rootName)

            nodeCount = nodeCount + 1
            translateConstraint(t, root.rchild)
          }
        }
        case IIntLit(value) => {
          val v = value.toString()
          //println("IIntLit")
          //println(v)
          if (root.lchild == null) {
            if (argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(v) -> (v)))
              if(!cfn.nodeList.exists(x=>x._1==cfn.getArgNameByContent(v))){
                logString = logString + ( "\"" +cfn.getArgNameByContent(v) + "\""+
                " [label=\"" + cfn.getArgNameByContent(v) + "\""+" nodeName="+ "\"" +cfn.getArgNameByContent(v)+ "\"" +" class=argument "+"];" + "\n")
                cfn.nodeList+=Pair(cfn.getArgNameByContent(v),cfn.getArgNameByContent(v))
              }
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, value)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              if(!cfn.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + v + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=Literal "+"];" + "\n")
                cfn.nodeList+=Pair(nodeName,v)
              }
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
          } else if (root.rchild == null) {
            if (argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(v) -> (v)))
              if(!cfn.nodeList.exists(x=>x._1==cfn.getArgNameByContent(v))){
                logString = logString + ( "\"" +cfn.getArgNameByContent(v) + "\""+
                " [label=\"" + cfn.getArgNameByContent(v) + "\""+" nodeName="+ "\"" +cfn.getArgNameByContent(v)+ "\"" +" class=argument "+"];" + "\n")
                cfn.nodeList+=Pair(cfn.getArgNameByContent(v),cfn.getArgNameByContent(v))
              }
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, value)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              if(!cfn.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + ( "\"" +nodeName +  "\"" +" [label=\"" + v + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=Literal "+"];" + "\n")
                cfn.nodeList+=Pair(nodeName,v)
              }
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
          }
          nodeCount = nodeCount + 1
        }
        case INamedPart(name, subformula) => {
          println("INamedPart")
          val n = name.toString
          if (root.lchild == null) {
            if (argumentList.exists(_.originalContent == n)) {
              root.lchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(n) -> (n)))
              logString = logString + ( "\"" +cfn.getArgNameByContent(n) + "\""+
              " [label=\"" + cfn.getArgNameByContent(n) + "\""+" nodeName="+ "\"" +cfn.getArgNameByContent(n)+ "\"" +" class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(n)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName-> (n)))
              logString = logString + ( "\"" +nodeName + "\"" +" [label=\"" + n + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=INamePart "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)
          } else if (root.rchild == null) {
            if (argumentList.exists(_.originalContent == n)) {
              root.rchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(n) -> (n)))
              logString = logString + ( "\"" +cfn.getArgNameByContent(n) + "\""+
              " [label=\"" + cfn.getArgNameByContent(n) + "\""+" nodeName="+ "\"" +cfn.getArgNameByContent(n)+ "\"" +" class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(n)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (n)))
              logString = logString + ( "\"" +nodeName +  "\"" +" [label=\"" + n + "\""+" nodeName="+ "\"" +nodeName+ "\"" +" class=INamePart "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)
          }
        }
        case Difference(t1, t2) => {
          //println(t1+"-"+t2)
          val d = "-"
          if (root.lchild == null) {
            root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> d))
            val nodeName=astNodeNamePrefix + nodeCount
            logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + d + "\"" +" nodeName="+ "\"" + nodeName+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> d))
            logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + d + "\"" +" nodeName="+ "\"" +nodeName+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)

          }
        }
        case IPlus(t1, t2) => {
          val p = "+"
          //println(t1+"+"+t2)
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> p))
            logString = logString + ( "\"" +nodeName + "\"" + " [label=\"" + p + "\"" +" nodeName="+ "\"" +nodeName+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> p))
            logString = logString + ( "\"" + nodeName + " [label=\"" + p + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)

          }

        }
        case IQuantified(quan, subformula) => {
          val q = quan.toString
          println("IQuantified")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> q))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + q + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> q))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + q + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.rchild)
          }
        }
        //case ITerm()=>println("ITerm")
        case ITermITE(cond, left, right) => {
          println("ITermITE")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "ITermITE"))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "ITermITE" + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=ITermITE "+"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.lchild)
            translateConstraint(left, root.lchild)
            translateConstraint(right, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "ITermITE"))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "ITermITE" + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=ITermITE "+"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.rchild)
            translateConstraint(left, root.rchild)
            translateConstraint(right, root.rchild)

          }
        }
        case ITimes(coeff, t) => {
          val v = coeff.toString()
          //println("*"+v)
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "*"))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"*\""+ " nodeName="+ "\"" + nodeName+ "\"" + " class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + cfn.getArgNameByContent(v) + "\"" +
                " [label=\"" + cfn.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + cfn.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, coeff)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + v + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Coeff "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            translateConstraint(t, root.lchild)
          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "*"))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"*\""+ " nodeName="+ "\"" + nodeName+ "\"" + " class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(cfn.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + cfn.getArgNameByContent(v) + "\"" +
                " [label=\"" + cfn.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + cfn.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, coeff)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild.rchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + v + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Coeff "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            translateConstraint(t, root.rchild)
          }

        }
        case ITrigger(patterns, subformula) => {
          println("ITrigger");
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "ITrigger"))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "ITrigger" + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=ITrigger "+"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)
            for (p <- patterns) {
              translateConstraint(p, root.lchild)
            }

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "ITrigger"))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "ITrigger" + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=ITrigger "+"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.rchild)
            for (p <- patterns) {
              translateConstraint(p, root.rchild)
            }

          }
        }
        case IVariable(index) => {
          //println("IVariable")
          val i = index.toString
          //println(i)
          if (root.rchild == null) {
            if (argumentList.exists(_.hintIndex == i)) {
              root.rchild = new TreeNodeForGraph(Map(cfn.getArgNameByIndex(i) -> (i)))
              logString = logString + ( "\"" + cfn.getArgNameByIndex(i) + "\"" +
                " [label=\"" + cfn.getArgNameByIndex(i) + "\""+" nodeName="+ "\"" + cfn.getArgNameByIndex(i)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByIndex(i)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (i)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + i + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Variable "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
          } else if (root.lchild == null) {
            if (argumentList.exists(_.hintIndex == i)) {
              root.lchild = new TreeNodeForGraph(Map(cfn.getArgNameByIndex(i) -> (i)))
              logString = logString + ( "\"" + cfn.getArgNameByIndex(i) + "\"" +
                " [label=\"" + cfn.getArgNameByIndex(i) + "\""+" nodeName="+ "\"" + cfn.getArgNameByIndex(i)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = cfn.getArgNameByIndex(i)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> (i)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + i + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Variable "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
          }
        }
        case IIntFormula(rel, t) => {
          println("IIntFormula")
          //          if(root.lchild==null){
          //            if(rel.toString=="GeqZero"){
          //              root.lchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->">="))
          //              logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ ">=" +"\"];"+"\n")
          //              if(nodeCount==0){
          //                rootName=astNodeNamePrefix+nodeCount
          //              }
          //              nodeCount=nodeCount+1
          //              root.lchild.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->"constant_0"))
          //              //println(nodeCount + " [label=\""+ "0" +"\"];")
          //              logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ "0" +"\"];"+"\n")
          //              if(nodeCount==0){
          //                rootName=astNodeNamePrefix+nodeCount
          //              }
          //              nodeCount=nodeCount+1
          //              //root=root.lchild
          //              translateConstraint(t,root.lchild)
          //              //println(nodeCount + " [label=\""+ ">=" +"\"];")
          //
          //            }
          //          }else if(root.rchild==null){
          //            if(rel.toString=="GeqZero"){
          //              root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->">="))
          //              logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ ">=" +"\"];"+"\n")
          //              if(nodeCount==0){
          //                rootName=astNodeNamePrefix+nodeCount
          //              }
          //              nodeCount=nodeCount+1
          //              root.rchild.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->"constant_0"))
          //              //println(nodeCount + " [label=\""+ "0" +"\"];")
          //              logString=logString+(astNodeNamePrefix+nodeCount + " [label=\""+ "0" +"\"];"+"\n")
          //              if(nodeCount==0){
          //                rootName=astNodeNamePrefix+nodeCount
          //              }
          //              nodeCount=nodeCount+1
          //              //root=root.lchild
          //              translateConstraint(t,root.rchild)
          //              //println(nodeCount + " [label=\""+ ">=" +"\"];")
          //
          //            }
          //          }
        }
        case _ => println("?")
      }
    }

    for (((hintName,hintType,hint),i) <- hints.zipWithIndex) { //get dataflow or guard element list and parse data flow to AST
      //println(hint)
      astNodeNamePrefix =hintName + "predicate_"+ hintCount + "_node_"
      translateConstraint(hint, root) //define nodes in graph, information is stored in logString

      val binary_search_tree_for_graph = new BinarySearchTreeForGraphClass(edgeNameMap("predicateAST"))
      binary_search_tree_for_graph.nodeString = logString
      binary_search_tree_for_graph.preOrder(rootMark) //connect nodes in graph, information is stored in relationString
      logString = binary_search_tree_for_graph.nodeString + binary_search_tree_for_graph.relationString

      val currentASTGraph = new predicateGraph(rootName, hintName, logString,hintType,i.toString,hint)
      ASTGraph += currentASTGraph //record graph as string
      logString = ""
      nodeCount = 0
      hintCount = hintCount + 1
      root = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "root"))
      rootMark = root
    }
    (ASTGraph,nodeHashMap)
  }


  def drawAST(clause: ClauseTransitionInformation, ASTType: String,
              conatraintMap: Map[String, IExpression],
              freeVariableMap:MHashMap[String,ITerm],
              edgeNameMap:Map[String,String],gnn_inputs:GNNInput,dot:Digraph) = {
    var ASTGraph = ListBuffer[DataFlowASTGraphInfo]()
    var nodeCount: Int = 0
    var dataFlowCount: Int = 0
    var astNodeNamePrefix = "xxx" + clause.name + "_" + clause.clauseID + "xxx" + ASTType +"_"+ dataFlowCount + "_node_"
    //todo:rewire root
    var logString: String = "" //store node information
    var rootName = ""
    var nodeHashMap:MHashMap[String,ITerm]=freeVariableMap

    def translateConstraint(e: IExpression, root: TreeNodeForGraph): Unit = {

      e match {
        case INot(subformula) => {
          //println("INOT")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "!"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "!" + "\"" +" nodeName="+ addQuotes(nodeName) + " class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("!"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)
          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "!"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "!" + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("!"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.rchild)
          }
        }
        case IAtom(pred, args) => {
          val p = pred.name
          //println("IAtom")
          if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == p)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(p) -> (p)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(p)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == p)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(p) -> (p)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(p)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (p)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + p + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Pred "+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(p),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"Pred","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = nodeName
              }
            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.lchild)
            }

          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == p)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(p) -> (p)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(p)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == p)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(p) -> (p)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(p)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (p)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + p + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Pred "+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(p),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"Pred","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.rchild)
            }
          }

        }
        case IBinFormula(junctor, f1, f2) => {
          //println("IBinFormula")
          //println(j.toString)
          val j = junctor.toString
          if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == j)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(j) -> (j)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(j)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == j)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(j) -> (j)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(j)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (j)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + j + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator "+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(j),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"Operator","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            translateConstraint(f1, root.lchild)
            translateConstraint(f2, root.lchild)

          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == j)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(j) -> (j)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(j)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == j)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(j) -> (j)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(j)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (j)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + j + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator "+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(j),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"Operator","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            translateConstraint(f1, root.rchild)
            translateConstraint(f2, root.rchild)
          }


        }
        case IBoolLit(value) => {
          //println("IBoolLit")
          //println(value)
          val v = value.toString
          if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName-> (v)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + v + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=BoolValue "+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(v),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"BoolValue","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
          } else if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + v + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=BoolValue "+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(v),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"BoolValue","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
          }
          nodeCount = nodeCount + 1
        }
        case IConstant(constantTerm) => {
          val c = constantTerm.toString()
          //println("IConstant")
          //println(c)
          if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == c)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(c) -> (c)))
              if(!clause.nodeList.exists(x=>x._1==clause.body.getArgNameByContent(c))){
                clause.nodeList+=Pair(clause.body.getArgNameByContent(c),clause.body.getArgNameByContent(c))
              }
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(c)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == c)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(c) -> (c)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(c))){
                clause.nodeList+=Pair(clause.head.getArgNameByContent(c),clause.head.getArgNameByContent(c))
              }
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(c)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,c,nodeHashMap, constantTerm)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (c)))
              if(!clause.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + ( addQuotes(nodeName) +  " [label=\"" + c + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Constant "+"];" + "\n")
                clause.nodeList+=Pair(nodeName,c)
                dot.node(addQuotes(nodeName),addQuotes(c),MuMap("nodeName"->addQuotes(nodeName),
                  "class"->"Constant","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
                gnn_inputs.incrementNodeIds(nodeName)
              }
              //logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + c + "\"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
            //root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->(c.toString)))
            //root=root.lchild
          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == c)) {
              //              println(clause.body.getArgNameByContent(c))
              //              println(c)
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(c) -> (c)))
              if(!clause.nodeList.exists(x=>x._1==clause.body.getArgNameByContent(c))){
                clause.nodeList+=Pair(clause.body.getArgNameByContent(c),clause.body.getArgNameByContent(c))
              }
              rootName = checkASTRoot(nodeCount,clause.body.getArgNameByContent(c),rootName)
            } else if (clause.head.argumentList.exists(_.originalContent == c)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(c) -> (c)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(c))){
                clause.nodeList+=Pair(clause.head.getArgNameByContent(c),clause.head.getArgNameByContent(c))
              }
              rootName = checkASTRoot(nodeCount,clause.head.getArgNameByContent(c),rootName)
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,c,nodeHashMap, constantTerm)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (c)))
              if(!clause.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + ( addQuotes(nodeName) +  " [label=\"" + c + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Constant "+"];" + "\n")
                clause.nodeList+=Pair(nodeName,c)
                dot.node(addQuotes(nodeName),addQuotes(c),MuMap("nodeName"->addQuotes(nodeName),
                  "class"->"Constant","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
                gnn_inputs.incrementNodeIds(nodeName)
              }
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
          }
          nodeCount = nodeCount + 1
        }
        case IEpsilon(cond) => {
          //println("IEpsilon")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "IEpsilon"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "IEpsilon" +" nodeName="+ addQuotes(nodeName) +  "\""+" class=Operator "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("IEpsilon"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "IEpsilon"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "IEpsilon" +" nodeName="+ addQuotes(nodeName) +  "\""+" class=Operator "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("IEpsilon"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.rchild)
          }
        }
        //case IFormula()=>println("IFormula")
        case IFormulaITE(cond, left, right) => {
          //println("IFormulaITE")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "IFormulaITE"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "IFormulaITE" + "\""+" nodeName="+ addQuotes(nodeName) + " class=Formula "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("IFormulaITE"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Formula","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.lchild)
            translateConstraint(left, root.lchild)
            translateConstraint(right, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName-> "IFormulaITE"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "IFormulaITE" + "\""+" nodeName="+ addQuotes(nodeName) + " class=Formula "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("IFormulaITE"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Formula","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.rchild)
            translateConstraint(left, root.rchild)
            translateConstraint(right, root.rchild)

          }
        }
        case IFunApp(fun, args) => {
          //println("IFunApp");
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "IFunApp"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "IFunApp" + "\""+" nodeName="+ addQuotes(nodeName) + " class=IFunApp "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("IFunApp"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"IFunApp","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.lchild)
            }

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "IFunApp"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "IFunApp" + "\""+" nodeName="+ addQuotes(nodeName) + " class=IFunApp "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("IFunApp"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"IFunApp","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.rchild)
            }
          }
        }
        case Eq(t1, t2) => {
          val eq = "="
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> eq))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + eq + "\"" +" nodeName="+ addQuotes(nodeName) + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(eq),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> eq))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + eq + "\"" +" nodeName="+ addQuotes(nodeName) + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(eq),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)

          }
        }
        case Geq(t1, t2) => {
          val geq = ">="
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> geq))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + geq + "\"" +" nodeName="+ addQuotes(nodeName) + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(geq),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> geq))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + geq + "\"" +" nodeName="+ addQuotes(nodeName) + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(geq),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)

          }
        }
        case EqLit(term, lit) => {
          val v = lit.toString()
          val eq = "="
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> eq))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + eq + "\"" +" nodeName="+ addQuotes(nodeName) + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(eq),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.lchild.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, lit)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + v + "\""+" nodeName="+ addQuotes(nodeName) + " class=Literal "+"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
              dot.node(addQuotes(nodeName),addQuotes(v),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"Literal","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
            }
            nodeCount = nodeCount + 1
            translateConstraint(term, root.lchild)
          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> eq))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + eq + "\"" + " shape=\"rect\"" +" class=Operator "+ "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(eq),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.rchild.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, lit)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild.rchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + v + "\""+" nodeName="+ addQuotes(nodeName) + " class=Literal "+"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
              dot.node(addQuotes(nodeName),addQuotes(v),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"Literal","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
            }
            nodeCount = nodeCount + 1
            translateConstraint(term, root.rchild)
          }
        }
        case GeqZ(t) => {
          val geq = ">="
          if (root.lchild == null) {
            val nn=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nn -> geq))
            logString = logString + ( addQuotes(nn) +  " [label=\"" + geq + "\"" +" nodeName="+ addQuotes(nn) + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nn),addQuotes(geq),MuMap("nodeName"->addQuotes(nn),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nn)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1


            val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,"0",nodeHashMap, 0)
            nodeHashMap=nodeHashMapOut
            val nodeName:String=nodeNameOut
            root.lchild.lchild = new TreeNodeForGraph(Map(nodeName -> ("0")))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "0" + "\""+" nodeName="+ addQuotes(nodeName) + " class=Constant "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("0"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Constant","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            rootName = checkASTRoot(nodeCount,nodeName,rootName)
            nodeCount = nodeCount + 1
            translateConstraint(t, root.lchild)

          } else if (root.rchild == null) {
            val nn=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nn -> geq))
            logString = logString + ( addQuotes(nn) +  " [label=\"" + geq + "\"" +" nodeName="+ addQuotes(nn) + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nn),addQuotes(geq),MuMap("nodeName"->addQuotes(nn),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nn)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,"0",nodeHashMap, 0)
            nodeHashMap=nodeHashMapOut
            val nodeName:String=nodeNameOut
            root.rchild.rchild = new TreeNodeForGraph(Map(nodeName -> ("0")))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "0" + "\""+" nodeName="+ addQuotes(nodeName) + " class=Constant "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("0"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Constant","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            rootName = checkASTRoot(nodeCount,nodeName,rootName)
            nodeCount = nodeCount + 1
            translateConstraint(t, root.rchild)
          }
        }
        case IIntLit(value) => {
          val v = value.toString()
          //println("IIntLit")
          //println(v)
          if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              if(!clause.nodeList.exists(x=>x._1==clause.body.getArgNameByContent(v))){
                clause.nodeList+=Pair(clause.body.getArgNameByContent(v),clause.body.getArgNameByContent(v))
              }
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(v))){
                clause.nodeList+=Pair(clause.head.getArgNameByContent(v),clause.head.getArgNameByContent(v))
              }
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, value)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              if(!clause.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + ( addQuotes(nodeName) +  " [label=\"" + v + "\""+" nodeName="+ addQuotes(nodeName) + " class=Literal "+"];" + "\n")
                dot.node(addQuotes(nodeName),addQuotes(v),MuMap("nodeName"->addQuotes(nodeName),
                  "class"->"Literal","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
                gnn_inputs.incrementNodeIds(nodeName)
                clause.nodeList+=Pair(nodeName,v)
              }
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
            //root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->(v)))
          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              if(!clause.nodeList.exists(x=>x._1==clause.body.getArgNameByContent(v))){
                clause.nodeList+=Pair(clause.body.getArgNameByContent(v),clause.body.getArgNameByContent(v))
              }
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(v))){
                clause.nodeList+=Pair(clause.head.getArgNameByContent(v),clause.head.getArgNameByContent(v))
              }
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, value)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              if(!clause.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + ( addQuotes(nodeName) +  " [label=\"" + v + "\""+" nodeName="+ addQuotes(nodeName) + " class=Literal "+"];" + "\n")
                dot.node(addQuotes(nodeName),addQuotes(v),MuMap("nodeName"->addQuotes(nodeName),
                  "class"->"Literal","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
                gnn_inputs.incrementNodeIds(nodeName)
                clause.nodeList+=Pair(nodeName,v)
              }
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
          }
          nodeCount = nodeCount + 1
        }
        case INamedPart(name, subformula) => {
          //println("INamedPart")
          val n = name.toString
          if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == n)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(n) -> (n)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(n)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == n)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(n) -> (n)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(n)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (n)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + n + "\""+" nodeName="+ addQuotes(nodeName) + " class=INamePart "+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(n),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"INamePart","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)


          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == n)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(n) -> (n)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(n)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == n)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(n) -> (n)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(n)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (n)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + n + "\""+" nodeName="+ addQuotes(nodeName) + " class=INamePart "+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(n),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"INamePart","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)
          }
        }
        case Difference(t1, t2) => {
          val d = "-"
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> d))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + d + "\"" +" nodeName="+ addQuotes(nodeName) + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(d),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> d))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + d + "\"" +" nodeName="+ addQuotes(nodeName) + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(d),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)

          }
        }
        case IPlus(t1, t2) => {
          val p = "+"
          //println("IPLUS")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> p))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + p + "\"" +" nodeName="+ addQuotes(nodeName) + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(p),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> p))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + p + "\"" +" nodeName="+ addQuotes(nodeName) + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(p),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.rchild)
            translateConstraint(t2, root.rchild)
          }
        }
        case IQuantified(quan, subformula) => {
          val q = quan.toString
          //println("IQuantified")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> q))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + q + "\"" +" nodeName="+ addQuotes(nodeName) + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(q),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> q))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + q + "\"" +" nodeName="+ addQuotes(nodeName) + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes(q),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.rchild)
          }
        }
        //case ITerm()=>println("ITerm")
        case ITermITE(cond, left, right) => {
          //println("ITermITE")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName-> "ITermITE"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "ITermITE" + "\""+" nodeName="+ addQuotes(nodeName) + " class=ITermITE "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("ITermITE"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"ITermITE","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.lchild)
            translateConstraint(left, root.lchild)
            translateConstraint(right, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "ITermITE"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "ITermITE" + "\""+" nodeName="+ addQuotes(nodeName) + " class=ITermITE "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("ITermITE"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"ITermITE","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.rchild)
            translateConstraint(left, root.rchild)
            translateConstraint(right, root.rchild)

          }
        }
        case ITimes(coeff, t) => {
          val v = coeff.toString()
          //println("ITimes")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "*"))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"*\"" +" nodeName="+ addQuotes(nodeName) + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("*"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, coeff)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + v + "\""+" nodeName="+ addQuotes(nodeName) + " class=Coeff "+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(v),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"Coeff","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            translateConstraint(t, root.lchild)
          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "*"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"*\"" +" nodeName="+ addQuotes(nodeName) + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("*"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"Operator","shape"->"rect","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, coeff)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild.rchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( addQuotes(nodeName)  + " [label=\"" + v + "\""+" nodeName="+ addQuotes(nodeName) + " class=Coeff "+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(v),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"Coeff","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            translateConstraint(t, root.rchild)
          }

        }
        case ITrigger(patterns, subformula) => {
          //println("ITrigger");
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "ITrigger"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "ITrigger" + "\""+" nodeName="+ addQuotes(nodeName) + " class=ITrigger "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("ITrigger"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"ITrigger","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)
            for (p <- patterns) {
              translateConstraint(p, root.lchild)
            }

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "ITrigger"))
            logString = logString + ( addQuotes(nodeName) +  " [label=\"" + "ITrigger" + "\""+" nodeName="+ addQuotes(nodeName) + " class=ITrigger "+"];" + "\n")
            dot.node(addQuotes(nodeName),addQuotes("ITrigger"),MuMap("nodeName"->addQuotes(nodeName),
              "class"->"ITrigger","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
            gnn_inputs.incrementNodeIds(nodeName)
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.rchild)
            for (p <- patterns) {
              translateConstraint(p, root.rchild)
            }

          }
        }
        case IVariable(index) => {
          println("IVariable")
          val i = index.toString
          println(i)
          if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == i)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(i) -> (i)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(i)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == i)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(i) -> (i)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(i)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (i)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + i + "\""+" nodeName="+ addQuotes(nodeName) + " class=Variable"+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(i),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"Variable","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
          } else if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == i)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(i) -> (i)))
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(i)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == i)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(i) -> (i)))
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(i)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (i)))
              logString = logString + ( addQuotes(nodeName) +  " [label=\"" + i + "\""+" nodeName="+ addQuotes(nodeName) + " class=Variable"+"];" + "\n")
              dot.node(addQuotes(nodeName),addQuotes(i),MuMap("nodeName"->addQuotes(nodeName),
                "class"->"Variable","GNNNodeID"->gnn_inputs.GNNNodeID.toString))
              gnn_inputs.incrementNodeIds(nodeName)
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
          }
        }
        case IIntFormula(rel, t) => {
          println("IIntFormula")
        }
        case _ => println("?")
      }
    }

    for ((argumentName, conatraint) <- conatraintMap) { //get dataflow or guard element list and parse data flow to AST
      if (ASTType == "guard") {
        clause.guardNumber = clause.guardNumber + 1
      } else {
        clause.dataFlowNumber = clause.dataFlowNumber + 1
      }
      val root = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "root"))
      translateConstraint(conatraint, root) //define nodes in graph, information is stored in logString
      val binary_search_tree_for_graph=new BinarySearchTreeForGraphClass(edgeNameMap("dataFlowAST"),ASTType)
      binary_search_tree_for_graph.nodeString = logString
      binary_search_tree_for_graph.preOrder(root,gnn_inputs,dot) //connect nodes in graph, information is stored in relationString
      logString = binary_search_tree_for_graph.nodeString + binary_search_tree_for_graph.relationString

      val currentASTGraph = new DataFlowASTGraphInfo(rootName, argumentName, logString)
      ASTGraph += currentASTGraph //record graph as string
      logString = ""
      nodeCount = 0
      dataFlowCount = dataFlowCount + 1
      astNodeNamePrefix = "xxx" + clause.name + "_" + clause.clauseID + "xxx" + ASTType + dataFlowCount + "_node_"
    }
    (ASTGraph,nodeHashMap)
  }

  def checkASTRoot(nodeCount:Int,nodeName:String,currentRoot:String): String ={
    if(nodeCount==0){
      nodeName
    }else{
      currentRoot
    }
  }
  def mergeFreeVariables(astNodeNamePrefix:String,nodeCount:Int,v:String,nodeHashMapIn:MHashMap[String,ITerm],
                         value:IdealInt) ={
    var nodeHashMap:MHashMap[String,ITerm]=nodeHashMapIn
    var nodeName:String=astNodeNamePrefix + nodeCount
    var forFlag=false
    if(nodeHashMap.exists(node=>node._2.toString==v)){
      for((nName,nContent)<-nodeHashMap if !nodeHashMap.isEmpty && forFlag==false){
        if(nContent.toString==v){ //if the node existed in hash map, use it name
          nodeName=nName
          forFlag=true
        }
      }
    }else{
      nodeHashMap+=(nodeName->new IIntLit(value))
    }
//    for((nName,nContent)<-nodeHashMap if !nodeHashMap.isEmpty && forFlag==false){
//      if(nContent.toString!=v){ //if the node existed in hash map
//        println(nContent.toString+"!="+v)
//        nodeHashMap+=(nodeName->new IIntLit(value))
//      }else{
//        println(nContent.toString+"=="+v)
//        nodeName=nName
//        println(nodeName)
//        forFlag=true
//      }
//    }
    if(nodeHashMap.isEmpty){
      nodeHashMap+=(nodeName->new IIntLit(value))
    }
    (nodeHashMap,nodeName)
  }

  //rewrite to deal with IConstant
  def mergeFreeVariables(astNodeNamePrefix:String,nodeCount:Int,v:String,nodeHashMapIn:MHashMap[String,ITerm],
                         value:ConstantTerm) ={
    var nodeHashMap:MHashMap[String,ITerm]=nodeHashMapIn
    var nodeName:String=astNodeNamePrefix + nodeCount
    var forFlag=false
    if(nodeHashMap.exists(node=>node._2.toString==v)){
      for((nName,nContent)<-nodeHashMap if !nodeHashMap.isEmpty && forFlag==false){
        if(nContent.toString==v){ //if the node existed in hash map, use it name
          nodeName=nName
          forFlag=true
        }
      }
    }else{
      nodeHashMap+=(nodeName->new IConstant(value))
    }
    //    for((nName,nContent)<-nodeHashMap if !nodeHashMap.isEmpty && forFlag==false){
    //      if(nContent.toString!=v){ //if the node existed in hash map
    //        println(nContent.toString+"!="+v)
    //        nodeHashMap+=(nodeName->new IIntLit(value))
    //      }else{
    //        println(nContent.toString+"=="+v)
    //        nodeName=nName
    //        println(nodeName)
    //        forFlag=true
    //      }
    //    }
    if(nodeHashMap.isEmpty){
      nodeHashMap+=(nodeName->new IConstant(value))
    }
    (nodeHashMap,nodeName)
  }

  def addQuotes(str:String): String ={
    return "\"" + str + "\""
  }


}

