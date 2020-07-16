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

import scala.collection.mutable.{ListBuffer, HashMap => MHashMap}


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
    println(oneGraphGNNInput)


    println("Write GNNInput to file")
    val writer = new PrintWriter(new File("../trainData/" + file +"-test"+ ".JSON")) //python path
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


  def writeHornClausesGraphToFile(file: String, simpClauses: Clauses,hints:VerificationHints): Unit = {
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
        }
      }
      //add body argument to node list
      for(arg<-currentClause.body.argumentList if !currentClause.body.argumentList.isEmpty){
        if(!currentClause.nodeList.exists(x=>x._1==arg.name)){
          currentClause.nodeList+=Pair(arg.name,arg.originalContent)
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
      val (dataFLowAST,dataFlowNodeHashMap) = drawAST(currentClause, "dataFlow", dataFlowMap,MHashMap.empty[String,ITerm],edgeNameMap)
      currentClause.dataFlowASTGraph=dataFLowAST
      //draw simple data flow
      for (comArg <- commonArg) {
        if (!dataFlowElementList.contains(comArg._1)) {
          writer.write(comArg._1 + "<-" + comArg._1 + "\n")

          for (bodyArg <- currentClause.body.argumentList; headArg <- currentClause.head.argumentList
               if headArg.originalContent == comArg._1 && bodyArg.originalContent == comArg._1) {
            currentClause.simpleDataFlowConnection = currentClause.simpleDataFlowConnection ++
              Map(headArg.dataFLowHyperEdge.name ->
                ("\"" + bodyArg.name + "\"" + " -> " + "\"" + headArg.dataFLowHyperEdge.name+ "\"" +
                  "[label=\"" + edgeNameMap("dataFlowIn") + "\"]" + "\n"))
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
      val (guardASTList,guardNodeHashMap) = drawAST(currentClause, "guard", guardMap,dataFlowNodeHashMap,edgeNameMap)
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
    import scala.collection.mutable.Map
    val dot = new Digraph(comment = "Horn Graph")
    var GNNNodeID=0
    var hyperEdgeNodeID=0
    var TotalNodeID=0

    var nodeIds=new ListBuffer[Int]()
    var binaryAdjacentcy=new ListBuffer[ListBuffer[Int]]()
    var tenaryAdjacency=new ListBuffer[ListBuffer[Int]]()
    var controlLocationIndices=new ListBuffer[Int]()
    var argumentIndices=new ListBuffer[Int]()

    var nodeNameToIDMap =   scala.collection.mutable.Map[String, Int]()
    var unfinishedTenaryAdjacency=new ListBuffer[ListBuffer[Int]]()

    //val nodeIdsList = nodeIds.toList
    //val binaryAdjacentcyList = binaryAdjacentcy.toList ?

    def addQuotes(str:String): String ={
      return "\"" + str + "\""
    }

    println("Write horn to graph")
    val writerGraph = new PrintWriter(new File("../trainData/" + fileName + ".gv")) //python path


    writerGraph.write("digraph dag {" + "\n")
    //control flow node
    for (p <- predicates) {
      //println("" + predIndex(p) + " [label=\"" + p.name + "\"];")
      writerGraph.write("" + addQuotes(p.name)+ " [label=" + addQuotes(p.name) +" nodeName="+ addQuotes(p.name) +" class=cfn "+ " shape=\"rect\"" + "];" + "\n")
      dot.node(addQuotes(p.name), addQuotes(p.name),attrs = Map("nodeName"->addQuotes(p.name),
        "shape"->addQuotes("rect"),"class"->"cfn","GNNNodeID"->GNNNodeID.toString))
      nodeIds+=GNNNodeID
      controlLocationIndices+=GNNNodeID
      nodeNameToIDMap(p.name)=GNNNodeID
      GNNNodeID+=1
    }
    writerGraph.write("FALSE" + " [label=\"" + "FALSE" + "\""+" nodeName=FALSE"+" class=cfn " + " shape=\"rect\"" + "];" + "\n") //false node
    dot.node("FALSE","False",
      attrs = Map("nodeName"->"False","shape"->addQuotes("rect"),"class"->"cfn","GNNNodeID"->GNNNodeID.toString))
    nodeIds+=GNNNodeID
    controlLocationIndices+=GNNNodeID
    nodeNameToIDMap("FALSE")=GNNNodeID
    GNNNodeID+=1

    writerGraph.write("Initial" + " [label=\"" + "Initial" + "\"" +" nodeName=Initial"+" class=cfn "+ " shape=\"rect\"" + "];" + "\n") //initial node
    dot.node("Initial","Initial",
      attrs = Map("nodeName"->"Initial","shape"->addQuotes("rect"),"class"->"cfn","GNNNodeID"->GNNNodeID.toString))
    nodeIds+=GNNNodeID
    controlLocationIndices+=GNNNodeID
    nodeNameToIDMap("Initial")=GNNNodeID
    GNNNodeID+=1



    var ControlFowHyperEdgeList = new ListBuffer[ControlFowHyperEdge]() //build control flow hyper edge list


    //create control flow hyper edges, connections to control flow nodes, catch unique control flow node list
    var uniqueControlFLowNodeList = ListBuffer[ControlFlowNode]()
    for (clauseInfo <- clauseList) {
      //create control flow hyper edges and connections to control flow nodes
      //create control flow hyper edge nodes
      val cfheName=clauseInfo.controlFlowHyperEdge.name
      writerGraph.write(cfheName + " [label=\"Control flow hyperedge\""+" nodeName="+cfheName +" class=controlFlowHyperEdge"+ " shape=\"diamond\"" + "];" + "\n")
      dot.node(cfheName,addQuotes("Control flow hyperedge"),attrs = Map("nodeName"->cfheName,
        "shape"->addQuotes("diamond"),"class"->"controlFlowHyperEdge","hyperEdgeNodeID"->hyperEdgeNodeID.toString))
      hyperEdgeNodeID+=1
      //create edges of control flow hyper edge
      writerGraph.write(addQuotes(clauseInfo.body.name)+ " -> " + cfheName + " [label=\"" + edgeNameMap("controlFlowIn") + "\"]" + "\n")
      writerGraph.write(cfheName + " -> " + addQuotes(clauseInfo.head.name) + " [label=\"" + edgeNameMap("controlFlowOut") + "\"]" + "\n")
      dot.edge(addQuotes(clauseInfo.body.name),cfheName,attrs=Map("label"->addQuotes(edgeNameMap("controlFlowIn"))))
      dot.edge(addQuotes(cfheName),addQuotes(clauseInfo.head.name),attrs=Map("label"->addQuotes(edgeNameMap("controlFlowOut"))))
      //todo:hyperedges are tenary edges. Need guard AST root here
      unfinishedTenaryAdjacency+=ListBuffer(nodeNameToIDMap(clauseInfo.body.name),-1,nodeNameToIDMap(clauseInfo.head.name))

      //get unique control flow nodes
      if (!uniqueControlFLowNodeList.exists(_.name == clauseInfo.head.name)) {
        uniqueControlFLowNodeList += clauseInfo.head
      }
      if (!uniqueControlFLowNodeList.exists(_.name == clauseInfo.body.name)) {
        uniqueControlFLowNodeList += clauseInfo.body
      }
    }

    //todo:check point . to be continue...
    dot.render(fileName = fileName+"-test.gv", directory = "../trainData/", view = false)
    writeGNNInputsToJSON(fileName,nodeIds,binaryAdjacentcy,tenaryAdjacency,controlLocationIndices,argumentIndices)


    //create and connect to argument nodes
    for (controlFLowNode <- uniqueControlFLowNodeList; arg <- controlFLowNode.argumentList) {
      //create argument nodes
      writerGraph.write("\"" +arg.name+ "\"" + " [label=\"" + arg.name + "\"" +" nodeName=argument"+arg.index+" class=argument "+ " head="+"\""+controlFLowNode.name+"\"" +" shape=\"oval\"" + "];" + "\n")
      //connect arguments to location
      writerGraph.write("\"" + arg.name+ "\"" + " -> " +"\""+ controlFLowNode.name+"\"" + "[label=" + "\"" + edgeNameMap("argument") + "\"" +
        " style=\"dashed\"" + "]" + "\n")
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
      if (clauseInfo.guardNumber > 1) { //connect constraints by &
        andName = "xxx" + clauseInfo.name + "_" + clauseInfo.clauseID + "xxx" + "_and"
        writerGraph.write("\"" + andName+ "\"" + " [label=\"" + "&" + "\"" +" nodeName="+ "\"" +andName+ "\"" +" class=Operator"+ " shape=\"rect\"" + "];" + "\n")
        clauseInfo.guardASTRootName = andName //store this node to clauses's guardASTRootName
      }
      //draw guard ast
      for ((rootName, ast) <- clauseInfo.guardASTGraph) { //draw guard ast
        writerGraph.write(ast + "\n")
        if (clauseInfo.guardNumber > 1) { //connect constraints by &
          //writerGraph.write(clauseInfo.name + "_and"+"->"+rootName//ast.substring(0,ast.indexOf("[label")-1)
          writerGraph.write("\"" + rootName + "\"" + " -> " + "\"" + andName +"\"" //ast.substring(0,ast.indexOf("[label")-1)
            + " [label=\"" + edgeNameMap("astAnd") + "\"" + "];" + "\n")
        } else {
          clauseInfo.guardASTRootName = rootName
        }

      }
      //guard AST root point to control flow hyperedge
      if (!clauseInfo.guardASTRootName.isEmpty) {
        writerGraph.write("\"" + clauseInfo.guardASTRootName+ "\"" + " -> " + "\"" +clauseInfo.controlFlowHyperEdge.name +"\""
          + " [label=\"" + edgeNameMap("condition") + "\"" + "];" + "\n")
      }
      //if there is no guard add true condition
      if (clauseInfo.guardASTGraph.isEmpty) {
        writerGraph.write("\"" + clauseInfo.trueCondition+ "\"" + " [label=\"" + "true" + "\"" +" nodeName="+"\""+clauseInfo.trueCondition+"\""+" class=true"+ " shape=\"rect\"" + "];" + "\n") //add true node
        writerGraph.write("\"" + clauseInfo.trueCondition+ "\"" + " -> " + "\"" +clauseInfo.controlFlowHyperEdge.name +"\"" //add edge to control flow hyper edges
          + " [label=\"" + edgeNameMap("condition") + "\"" + "];" + "\n")

      }
      //draw data flow ast

      for (graphInfo <- clauseInfo.dataFlowASTGraph; argNode <- clauseInfo.head.argumentList if (graphInfo.argumentName == argNode.name)) {
        //writerGraph.write("// graphtext begin \n") //draw AST
        writerGraph.write(graphInfo.graphText + "\n") //draw AST
        //writerGraph.write("// graphtext end \n") //draw AST
        writerGraph.write("\"" + graphInfo.astRootName +"\"" + " -> " + "\"" +argNode.dataFLowHyperEdge.name + "\"" //connect to data flow hyper edge
          + " [label=\"" + edgeNameMap("dataFlow") + "\"" + "];" + "\n")

      }


    }

    //draw data flow

    //draw guarded data flow hyperedge for head
    for (clauseInfo <- clauseList; headArg <- clauseInfo.head.argumentList; if !clauseInfo.head.argumentList.isEmpty) {
      //create data flow hyperedge node
      writerGraph.write("\""+ headArg.dataFLowHyperEdge.name+ "\"" +
        " [label=\""+headArg.dataFLowHyperEdge.name+"\""+" nodeName="+ "\""+ headArg.dataFLowHyperEdge.name+ "\"" +" class=DataFlowHyperedge" +" shape=\"diamond\"" + "];" + "\n")
      //create data flow hyperedge node coonections
      writerGraph.write("\"" + headArg.dataFLowHyperEdge.name+ "\"" + " -> " + "\"" +headArg.name+ "\"" +
        "[label=\"" + edgeNameMap("dataFlowOut") + "\"]" + "\n")
      //guard AST root point to data flow hyperedge
      if (!clauseInfo.guardASTRootName.isEmpty) {
        writerGraph.write("\"" +clauseInfo.guardASTRootName+ "\"" + " -> " + "\"" +headArg.dataFLowHyperEdge.name+ "\"" +
          "[label=\"" + edgeNameMap("dataFlowIn") + "\"]" + "\n")
      }
      //if there is no guard add true condition to data flow hyperedge
      if (clauseInfo.guardASTGraph.isEmpty) {
        writerGraph.write("\"" +clauseInfo.trueCondition+ "\"" + " -> " + "\"" +headArg.dataFLowHyperEdge.name +"\"" //add edge to data flow hyper edges
          + " [label=\"" + edgeNameMap("condition") + "\"" + "];" + "\n")
        //todo:add true condition to data flow hyperedge (check)
      }
      //data flow AST root point to data flow hyperedge


    }
    //draw constant data flow for head
    for (clauseInfo <- clauseList) {
      for (headArg <- clauseInfo.head.argumentList; if !clauseInfo.head.argumentList.isEmpty) {
        if (headArg.constantFlowInNode != "") {
          writerGraph.write("\"" + headArg.constantFlowInNode +"\""
            + " [label=\"" + headArg.originalContent + "\"" +" nodeName="+ "\"" +headArg.constantFlowInNode+ "\"" + " class=Constant"+ "];" + "\n") //create constant node
          writerGraph.write("\"" + headArg.constantFlowInNode+ "\"" + " -> " + "\"" + headArg.dataFLowHyperEdge.name+"\"" //add edge to argument
            + " [label=\"" + edgeNameMap("constantDataFlow") + "\"" + "];" + "\n")
        }
      }
      //draw constant data flow for body
      for (bodyArg <- clauseInfo.body.argumentList; if !clauseInfo.body.argumentList.isEmpty) {
        if (!bodyArg.constantFlowInNode.isEmpty) {
          writerGraph.write("\"" + bodyArg.constantFlowInNode +"\""
            + " [label=\"" + bodyArg.originalContent + "\"" +" nodeName=" + "\"" + bodyArg.constantFlowInNode + "\"" +" class=Constant"+ "];" + "\n") //create constant node
          //todo: find where this body be head, and find that dataflow hyper edge
          writerGraph.write("\"" + bodyArg.constantFlowInNode + "\"" + " -> " + "\"" + bodyArg.name + "\""//add edge to argument
            + " [label=\"" + edgeNameMap("constantDataFlow") + "\"" + "];" + "\n")
        }
      }
    }



    //draw simple data flow connection
    for (clauseInfo <- clauseList) {
      if (!clauseInfo.simpleDataFlowConnection.isEmpty) {
        for ((hyperedge, connection) <- clauseInfo.simpleDataFlowConnection) {
          writerGraph.write(connection)
        }
      }
    }

    writerGraph.write("\n\n\n\n")
    //draw hints
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
              //todo: remove node declare redundancy
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
      BinarySearchTreeForGraph.connectionType=edgeNameMap("predicateAST")
      BinarySearchTreeForGraph.nodeString = logString
      BinarySearchTreeForGraph.preOrder(rootMark) //connect nodes in graph, information is stored in relationString
      logString = BinarySearchTreeForGraph.nodeString + BinarySearchTreeForGraph.relationString
      BinarySearchTreeForGraph.relationString = ""
      BinarySearchTreeForGraph.nodeString = ""

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
              edgeNameMap:Map[String,String]) = {
    var ASTGraph = ListBuffer[DataFlowASTGraphInfo]()
    var nodeCount: Int = 0
    var dataFlowCount: Int = 0
    var astNodeNamePrefix = "xxx" + clause.name + "_" + clause.clauseID + "xxx" + ASTType +"_"+ dataFlowCount + "_node_"
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "!" + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)
          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "!"))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "!" + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator"+ " shape=\"rect\"" + "];" + "\n")
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
              logString = logString + ( "\"" + clause.body.getArgNameByContent(p) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(p) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(p)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(p)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == p)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(p) -> (p)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(p) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(p) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(p)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(p)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (p)))
              logString = logString + ( "\"" + astNodeNamePrefix + nodeCount + "\"" +  " [label=\"" + p + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Pred "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
            for (arg <- args) {
              translateConstraint(arg, root.lchild)
            }

          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == p)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(p) -> (p)))
              logString = logString + ( "\"" + clause.body.getArgNameByContent(p) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(p) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(p)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(p)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == p)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(p) -> (p)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(p) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(p) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(p)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(p)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (p)))
              logString = logString + ( "\"" + astNodeNamePrefix + nodeCount + "\"" +  " [label=\"" + p + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Pred "+"];" + "\n")
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
              logString = logString + ( "\"" + clause.body.getArgNameByContent(j) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(j) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(j)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(j)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == j)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(j) -> (j)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(j) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(j) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(j)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(j)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (j)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + j + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator "+"];" + "\n")
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
              logString = logString + ( "\"" + clause.body.getArgNameByContent(j) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(j) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(j)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(j)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == j)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(j) -> (j)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(j) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(j) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(j)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(j)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (j)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + j + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator "+"];" + "\n")
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
              logString = logString + ( "\"" + clause.body.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName-> (v)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + v + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=BoolValue "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
          } else if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + clause.body.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + v + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=BoolValue "+"];" + "\n")
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
                logString = logString + ( "\"" + clause.body.getArgNameByContent(c) + "\"" +
                  " [label=\"" + clause.body.getArgNameByContent(c) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(c)+ "\"" + " class=argument "+"];" + "\n")
                clause.nodeList+=Pair(clause.body.getArgNameByContent(c),clause.body.getArgNameByContent(c))
              }
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(c)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == c)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(c) -> (c)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(c))){
                logString = logString + ( "\"" + clause.head.getArgNameByContent(c) + "\"" +
                  " [label=\"" + clause.head.getArgNameByContent(c) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(c)+ "\"" + " class=argument "+"];" + "\n")
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
                logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + c + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Constant "+"];" + "\n")
                clause.nodeList+=Pair(nodeName,c)
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
                logString = logString + ( "\"" + clause.body.getArgNameByContent(c) + "\"" +
                  " [label=\"" + clause.body.getArgNameByContent(c) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(c)+ "\"" + " class=argument "+"];" + "\n")
                clause.nodeList+=Pair(clause.body.getArgNameByContent(c),clause.body.getArgNameByContent(c))
              }
//              logString = logString + ( "\"" + clause.body.getArgNameByContent(c) + "\"" +
//                " [label=\"" + clause.body.getArgNameByContent(c) + "\"];" + "\n")
              rootName = checkASTRoot(nodeCount,clause.body.getArgNameByContent(c),rootName)
            } else if (clause.head.argumentList.exists(_.originalContent == c)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(c) -> (c)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(c))){
                logString = logString + ( "\"" + clause.head.getArgNameByContent(c) + "\"" +
                  " [label=\"" + clause.head.getArgNameByContent(c) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(c)+ "\"" + " class=argument "+"];" + "\n")
                clause.nodeList+=Pair(clause.head.getArgNameByContent(c),clause.head.getArgNameByContent(c))
              }
              rootName = checkASTRoot(nodeCount,clause.head.getArgNameByContent(c),rootName)
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,c,nodeHashMap, constantTerm)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (c)))
              if(!clause.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + c + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Constant "+"];" + "\n")
                clause.nodeList+=Pair(nodeName,c)
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "IEpsilon" +" nodeName="+ "\"" + nodeName+ "\"" +  "\""+" class=Operator "+"];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(cond, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "IEpsilon"))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "IEpsilon" +" nodeName="+ "\"" + nodeName+ "\"" +  "\""+" class=Operator "+"];" + "\n")
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "IFormulaITE" + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Formula "+"];" + "\n")
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "IFormulaITE" + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Formula "+"];" + "\n")
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "IFunApp" + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=IFunApp "+"];" + "\n")
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "IFunApp" + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=IFunApp "+"];" + "\n")
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + eq + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> eq))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + eq + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + geq + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> geq))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + geq + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + eq + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.lchild.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + clause.body.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, lit)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.lchild.lchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + v + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Literal "+"];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
            nodeCount = nodeCount + 1
            translateConstraint(term, root.lchild)
          } else if (root.rchild == null) {
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> eq))
            logString = logString + ( "\"" + astNodeNamePrefix + nodeCount + "\"" +  " [label=\"" + eq + "\"" + " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.rchild.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + clause.body.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, lit)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild.rchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( "\"" + astNodeNamePrefix + nodeCount + "\"" +  " [label=\"" + eq + "\"" + " shape=\"rect\"" + "];" + "\n")
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
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
            logString = logString + ( "\"" + nn + "\"" +  " [label=\"" + geq + "\"" +" nodeName="+ "\"" + nn+ "\"" + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1


            val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,"0",nodeHashMap, 0)
            nodeHashMap=nodeHashMapOut
            val nodeName:String=nodeNameOut
            root.lchild.lchild = new TreeNodeForGraph(Map(nodeName -> ("0")))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "0" + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Constant "+"];" + "\n")
            rootName = checkASTRoot(nodeCount,nodeName,rootName)
            nodeCount = nodeCount + 1
            translateConstraint(t, root.lchild)

          } else if (root.rchild == null) {
            val nn=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nn -> geq))
            logString = logString + ( "\"" + nn + "\"" +  " [label=\"" + geq + "\"" +" nodeName="+ "\"" + nn+ "\"" + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,"0",nodeHashMap, 0)
            nodeHashMap=nodeHashMapOut
            val nodeName:String=nodeNameOut
            root.rchild.rchild = new TreeNodeForGraph(Map(nodeName -> ("0")))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + "0" + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Constant "+"];" + "\n")
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
                logString = logString + ( "\"" + clause.body.getArgNameByContent(v) + "\"" +
                  " [label=\"" + clause.body.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
                clause.nodeList+=Pair(clause.body.getArgNameByContent(v),clause.body.getArgNameByContent(v))
              }
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(v))){
                logString = logString + ( "\"" + clause.head.getArgNameByContent(v) + "\"" +
                  " [label=\"" + clause.head.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
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
              //todo: remove node declare redundancy
              if(!clause.nodeList.exists(x=>x._1==nodeName)){
                logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + v + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Literal "+"];" + "\n")
                clause.nodeList+=Pair(nodeName,v)
              }
              rootName = checkASTRoot(nodeCount,nodeName,rootName)
            }
            //root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix+nodeCount->(v)))
          } else if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              if(!clause.nodeList.exists(x=>x._1==clause.body.getArgNameByContent(v))){
                logString = logString + ( "\"" + clause.body.getArgNameByContent(v) + "\"" +
                  " [label=\"" + clause.body.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
                clause.nodeList+=Pair(clause.body.getArgNameByContent(v),clause.body.getArgNameByContent(v))
              }
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              if(!clause.nodeList.exists(x=>x._1==clause.head.getArgNameByContent(v))){
                logString = logString + ( "\"" + clause.head.getArgNameByContent(v) + "\"" +
                  " [label=\"" + clause.head.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
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
                logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + v + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Literal "+"];" + "\n")
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
              logString = logString + ( "\"" + clause.body.getArgNameByContent(n) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(n) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(n)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(n)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == n)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(n) -> (n)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(n) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(n) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(n)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(n)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (n)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + n + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=INamePart "+"];" + "\n")
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
              logString = logString + ( "\"" + clause.body.getArgNameByContent(n) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(n) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(n)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(n)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == n)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(n) -> (n)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(n) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(n) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(n)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(n)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (n)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + n + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=INamePart "+"];" + "\n")
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + d + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> d))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + d + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + p + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(t1, root.lchild)
            translateConstraint(t2, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> p))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + p + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
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
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + q + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1
            translateConstraint(subformula, root.lchild)

          } else if (root.rchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.rchild = new TreeNodeForGraph(Map(nodeName -> q))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + q + "\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class= Operator"+ " shape=\"rect\"" + "];" + "\n")
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
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "ITermITE"))
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
          //println("ITimes")
          if (root.lchild == null) {
            val nodeName=astNodeNamePrefix + nodeCount
            root.lchild = new TreeNodeForGraph(Map(nodeName -> "*"))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"*\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + clause.body.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
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
            root.rchild = new TreeNodeForGraph(Map(nodeName -> "*"))
            logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"*\"" +" nodeName="+ "\"" + nodeName+ "\"" + " class=Operator "+ " shape=\"rect\"" + "];" + "\n")
            if (nodeCount == 0) {
              rootName = astNodeNamePrefix + nodeCount
            }
            nodeCount = nodeCount + 1

            if (clause.body.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + clause.body.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(v)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == v)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(v) -> (v)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(v) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(v) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(v)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(v)
              }
            } else {
              val (nodeHashMapOut,nodeNameOut)=mergeFreeVariables(astNodeNamePrefix,nodeCount,v,nodeHashMap, coeff)
              nodeHashMap=nodeHashMapOut
              val nodeName:String=nodeNameOut
              root.rchild.rchild = new TreeNodeForGraph(Map(nodeName -> (v)))
              logString = logString + ( "\"" + nodeName + "\""  + " [label=\"" + v + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Coeff "+"];" + "\n")
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
            root.rchild = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "ITrigger"))
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
          println("IVariable")
          val i = index.toString
          println(i)
          if (root.rchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == i)) {
              root.rchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(i) -> (i)))
              logString = logString + ( "\"" + clause.body.getArgNameByContent(i) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(i) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(i)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(i)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == i)) {
              root.rchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(i) -> (i)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(i) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(i) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(i)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(i)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.rchild = new TreeNodeForGraph(Map(nodeName -> (i)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + i + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Variable"+"];" + "\n")
              if (nodeCount == 0) {
                rootName = astNodeNamePrefix + nodeCount
              }
            }
            nodeCount = nodeCount + 1
          } else if (root.lchild == null) {
            if (clause.body.argumentList.exists(_.originalContent == i)) {
              root.lchild = new TreeNodeForGraph(Map(clause.body.getArgNameByContent(i) -> (i)))
              logString = logString + ( "\"" + clause.body.getArgNameByContent(i) + "\"" +
                " [label=\"" + clause.body.getArgNameByContent(i) + "\""+" nodeName="+ "\"" + clause.body.getArgNameByContent(i)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.body.getArgNameByContent(i)
              }
            } else if (clause.head.argumentList.exists(_.originalContent == i)) {
              root.lchild = new TreeNodeForGraph(Map(clause.head.getArgNameByContent(i) -> (i)))
              logString = logString + ( "\"" + clause.head.getArgNameByContent(i) + "\"" +
                " [label=\"" + clause.head.getArgNameByContent(i) + "\""+" nodeName="+ "\"" + clause.head.getArgNameByContent(i)+ "\"" + " class=argument "+"];" + "\n")
              if (nodeCount == 0) {
                rootName = clause.head.getArgNameByContent(i)
              }
            } else {
              val nodeName=astNodeNamePrefix + nodeCount
              root.lchild = new TreeNodeForGraph(Map(nodeName -> (i)))
              logString = logString + ( "\"" + nodeName + "\"" +  " [label=\"" + i + "\""+" nodeName="+ "\"" + nodeName+ "\"" + " class=Variable"+"];" + "\n")
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

    for ((argumentName, conatraint) <- conatraintMap) { //get dataflow or guard element list and parse data flow to AST
      if (ASTType == "guard") {
        clause.guardNumber = clause.guardNumber + 1
      } else {
        clause.dataFlowNumber = clause.dataFlowNumber + 1
      }
      translateConstraint(conatraint, root) //define nodes in graph, information is stored in logString
      BinarySearchTreeForGraph.connectionType=edgeNameMap("dataFlowAST")
      BinarySearchTreeForGraph.ASTtype = ASTType
      BinarySearchTreeForGraph.nodeString = logString
      BinarySearchTreeForGraph.preOrder(rootMark) //connect nodes in graph, information is stored in relationString
      logString = BinarySearchTreeForGraph.nodeString + BinarySearchTreeForGraph.relationString
      BinarySearchTreeForGraph.relationString = ""
      BinarySearchTreeForGraph.nodeString = ""


      val currentASTGraph = new DataFlowASTGraphInfo(rootName, argumentName, logString)
      ASTGraph += currentASTGraph //record graph as string
      //writer.write("}"+"\n")
      logString = ""
      nodeCount = 0
      dataFlowCount = dataFlowCount + 1
      astNodeNamePrefix = "xxx" + clause.name + "_" + clause.clauseID + "xxx" + ASTType + dataFlowCount + "_node_"
      root = new TreeNodeForGraph(Map(astNodeNamePrefix + nodeCount -> "root"))
      rootMark = root
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



}

