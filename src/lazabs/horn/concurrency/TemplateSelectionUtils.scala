package lazabs.horn.concurrency

import ap.PresburgerTools
import ap.parser.IExpression.Predicate
import ap.parser.{IAtom, IFormula}
import ap.terfor.TerForConvenience
import ap.terfor.TerForConvenience.{conj, disj, v}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.terfor.substitutions.ConstantSubst
import lazabs.GlobalParameters
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType
import lazabs.horn.abstractions.{AbsReader, StaticAbstractionBuilder, VerificationHints}
import lazabs.horn.bottomup.CEGAR.Counterexample
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{AbstractState, CEGAR, HornClauses, HornPredAbs, HornPredAbsContext, HornTranslator, HornWrapper, NormClause, PredicateMiner, PredicateStore, TemplateInterpolator}
import lazabs.horn.concurrency.DrawHornGraph.{HornGraphType, addQuotes}
import lazabs.horn.concurrency.HintsSelection.{detectIfAJSONFieldExists, generateCombinationTemplates, getArgumentInfo, getParametersFromVerifHintElement, getPredGenerator, termContains, wrappedReadHintsCheckExistence}
import lazabs.horn.preprocessor.HornPreprocessor.Clauses
import play.api.libs.json.{JsSuccess, JsValue, Json}

import scala.util.Random
import java.io.{File, PrintWriter}

object TemplateSelectionUtils{

  object CombineTemplateStrategy extends Enumeration {
    val union, random = Value
  }

  def outputPrologFile(normalizedClauses:Seq[Clause],typeName:String="normalized"): Unit ={
    val writerGraph = new PrintWriter(new File(GlobalParameters.get.fileName + "."+typeName+".prolog"))
    for (c<-normalizedClauses)
      writerGraph.write(c.toPrologString+"\n")
    writerGraph.close()
  }

  def writeGNNInputFieldToJSONFile(fieldName: String, fiedlContent: Arrays, writer: PrintWriter, lastFiledFlag: Boolean): Unit = {
    fiedlContent match {
      case StringArray(x) => writeOneField(fieldName, x, writer)
      case IntArray(x) => writeOneField(fieldName, x, writer)
      case PairArray(x) => writeOneField(fieldName, x, writer)
      case TripleArray(x) => writeOneField(fieldName, x, writer)
      case PairStringArray(x)=> writePairStringArrayField(fieldName, x, writer)
    }
    if (lastFiledFlag == false)
      writer.write(",\n")
    else
      writer.write("\n")
  }

  sealed abstract class Arrays
  case class StringArray(x: Array[String]) extends Arrays
  case class IntArray(x: Array[Int]) extends Arrays
  case class PairArray(x: Array[Pair[Int, Int]]) extends Arrays
  case class PairStringArray(x: Array[Pair[String, String]]) extends Arrays
  case class TripleArray(x: Array[Triple[Int, Int, Int]]) extends Arrays

  def writeOneField(fieldName: String, fiedlContent: Array[Pair[Int, Int]], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write("[")
      writer.write(p._1.toString)
      writer.write(",")
      writer.write(p._2.toString)
      writer.write("]")
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }
  def writePairStringArrayField(fieldName: String, fiedlContent: Array[Pair[String, String]], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write("[")
      writer.write(p._1)
      writer.write(",")
      writer.write(p._2)
      writer.write("]")
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }
  def writeOneField(fieldName: String, fiedlContent: Array[Triple[Int, Int, Int]], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write("[")
      writer.write(p._1.toString)
      writer.write(",")
      writer.write(p._2.toString)
      writer.write(",")
      writer.write(p._3.toString)
      writer.write("]")
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }

  def writeOneField(fieldName: String, fiedlContent: Array[Int], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write(p.toString)
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }

  def writeOneField(fieldName: String, fiedlContent: Array[String], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write(addQuotes(p.toString))
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }
  def readOneJSONFieldToMap(fieldName:String,fileName:String,json_data: JsValue,fields:Map[String,String]): Map[String,String] ={
    try{
      val stRelationalEqs= (json_data \ fieldName).validate[Array[String]] match {
        case JsSuccess(st,_)=> st
      }
      fields++Map(fieldName->stRelationalEqs.head)
    } catch {
      case _=> fields
    }
  }
  def readJSONFieldToMap(solvingTimeFileName:String,fieldNames:Seq[String]=Seq("RelationalEqs","Term","Octagon","RelationalIneqs","splitClauses")): Map[String,String] ={
    var fields:Map[String,String]=Map()
    val json_content = scala.io.Source.fromFile(solvingTimeFileName).mkString
    val json_data = Json.parse(json_content)
    //println("json_data",json_data)
    for (f<-fieldNames)
      fields=readOneJSONFieldToMap(fieldName = f,fileName = solvingTimeFileName,json_data=json_data,fields = fields)
    fields
  }

  def writeSolvingTimeToJSON(solvingTimeFileName:String,fields:Map[String,String]): Unit ={
    val writer = new PrintWriter(new File(solvingTimeFileName))
    writer.write("{\n")
    var lastFiledFlag= false
    for (f<-fields)
      writeGNNInputFieldToJSONFile(f._1, StringArray(Array[String](f._2)), writer, lastFiledFlag)
    lastFiledFlag = true
    writeGNNInputFieldToJSONFile("dummyFiled", StringArray(Array[String]()), writer, lastFiledFlag)
    writer.write("}")
    writer.close()
  }

  def getSolvability(unsimplifiedClauses: Seq[Clause],
                     simplifiedClausesForGraph:Seq[Clause],
                     initialPredicatesForCEGAR:Map[Predicate, Seq[IFormula]],
                     predGenerator : Dag[AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]]): Unit ={
    println(Console.BLUE+"--------------check solvability ---------------")
    val unlabeledTemplates = wrappedReadHintsCheckExistence(simplifiedClausesForGraph,".unlabeledPredicates",VerificationHints(Map()))
    val unlabeledTemplatesStatistics=HintsSelection.getVerificationHintsStatistics(unlabeledTemplates)
    val labeledTemplates = wrappedReadHintsCheckExistence(simplifiedClausesForGraph,".labeledPredicates",VerificationHints(Map()))
    val labeledTemplatesStatistics=HintsSelection.getVerificationHintsStatistics(labeledTemplates)
    val minedTemplates = wrappedReadHintsCheckExistence(simplifiedClausesForGraph,".minedPredicates",VerificationHints(Map()))
    val minedTemplatesStatistics=HintsSelection.getVerificationHintsStatistics(minedTemplates)
    val jsonFileName= if (GlobalParameters.get.getSolvingTime) "solvingTime" else if (GlobalParameters.get.checkSolvability) "solvability" else ""
    val solvingTimeFileName = GlobalParameters.get.fileName + "." + jsonFileName + ".JSON"
    val fixedFields:Map[String,Int]=Map("clauseNumberBeforeSimplification"->unsimplifiedClauses.length,
      "clauseNumberAfterSimplification"->simplifiedClausesForGraph.length,
      "smt2FileSizeByte"->new File(GlobalParameters.get.fileName).length().toInt, //bytes,
      "relationSymbolNumberBeforeSimplification"->unsimplifiedClauses.map(_.allAtoms.length).reduce(_+_),
      "relationSymbolNumberAfterSimplification"->
        (if(simplifiedClausesForGraph.size!=0) simplifiedClausesForGraph.map(_.allAtoms.length).reduce(_+_) else 0),
      "minedSingleVariableTemplatesNumber"->minedTemplatesStatistics._1,
      "minedBinaryVariableTemplatesNumber"->minedTemplatesStatistics._2,
      "minedTemplateNumber"->minedTemplatesStatistics._3,
      "minedTemplateRelationSymbolNumber"->minedTemplatesStatistics._4,
      "labeledSingleVariableTemplatesNumber"->labeledTemplatesStatistics._1,
      "labeledBinaryVariableTemplatesNumber"->labeledTemplatesStatistics._2,
      "labeledTemplateNumber"->labeledTemplatesStatistics._3,
      "labeledTemplateRelationSymbolNumber"->labeledTemplatesStatistics._4,
      "unlabeledSingleVariableTemplatesNumber"->unlabeledTemplatesStatistics._1,
      "unlabeledBinaryVariableTemplatesNumber"->unlabeledTemplatesStatistics._2,
      "unlabeledTemplateNumber"->unlabeledTemplatesStatistics._3,
      "unlabeledTemplateRelationSymbolNumber"->unlabeledTemplatesStatistics._4)
    val meansureFields=Seq("solvingTime","cegarIterationNumber","generatedPredicateNumber",
      "averagePredicateSize","predicateGeneratorTime","satisfiability")
    val combianedOptions=Seq("Term","Octagon","RelationalEqs","RelationalIneqs","Mined")
    val explorationRate=Seq(0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9)
    val combinedAbstractTypeFields=for(g<-Seq("_hyperEdgeGraph_union_","_monoDirectionLayerGraph_union_");a<-combianedOptions) yield a+g+"0.0"
    val randomAbstractTypeFields=for(g<-Seq("_hyperEdgeGraph_random_","_monoDirectionLayerGraph_random_");e<-explorationRate.map(_.toString);a<-combianedOptions) yield a+g+e
    val AbstractionTypeFields=AbstractionType.values.map(_.toString).toSeq ++ combinedAbstractTypeFields ++ randomAbstractTypeFields
    val splitClausesOption=Seq("splitClauses_0","splitClauses_1")
    val costOption=Seq("cost_shape","cost_logit","cost_same")
    val initialFieldsSeq= (for (m<-meansureFields;a<-AbstractionTypeFields;s<-splitClausesOption;c<-costOption) yield (m+"_"+a+"_"+s+"_"+c)->(m,a,s,c)).toMap
    val timeout = 60 * 60 * 3 * 1000 //milliseconds
    val initialFields: Map[String, Int] = (for ((k, v) <- initialFieldsSeq) yield k -> timeout) ++ fixedFields
    if(!jsonFileName.isEmpty && !new java.io.File(solvingTimeFileName).exists){
      writeSolvingTimeToJSON(solvingTimeFileName, initialFields.mapValues(_.toString))
    }

    val outStream = Console.err
    val predAbs = Console.withOut(outStream) {
        new HornPredAbs(simplifiedClausesForGraph, initialPredicatesForCEGAR, predGenerator)
    }


    if (new java.io.File(solvingTimeFileName).exists){ //update the solving time for current abstract option in JSON file
      val satisfiability= predAbs.result match {
        case Left(res) =>1 //SAT
        case Right(cex)=>0 //UNSAT
      }
      val solvingTime=(predAbs.cegar.cegarEndTime - predAbs.cegar.cegarStartTime) //milliseconds
      val cegarIterationNumber=predAbs.cegar.iterationNum
      val generatedPredicateNumber=predAbs.cegar.generatedPredicateNumber
      val averagePredicateSize=predAbs.cegar.averagePredicateSize
      val predicateGeneratorTime=predAbs.cegar.predicateGeneratorTime
      val resultList=Seq(solvingTime,cegarIterationNumber,generatedPredicateNumber,
        averagePredicateSize,predicateGeneratorTime,satisfiability).map(_.toInt).map(_.toString)
      for ((m,v)<-meansureFields.zip(resultList)) {
        val newField=
        if (GlobalParameters.get.combineTemplates)
          (m + "_" + GlobalParameters.get.templateBasedInterpolationType+"_"+GlobalParameters.get.hornGraphType + "_"+GlobalParameters.get.combineTemplateStrategy +"_"+GlobalParameters.get.explorationRate+ "_splitClauses_" + GlobalParameters.get.splitClauses.toString + "_cost_" + GlobalParameters.get.readCostType, v)
        else {
          //println(m+"_"+GlobalParameters.get.templateBasedInterpolationType.toString+"_splitClauses_"+GlobalParameters.get.splitClauses.toString+"_cost_"+GlobalParameters.get.readCostType,v)
          (m+"_"+GlobalParameters.get.templateBasedInterpolationType.toString+"_splitClauses_"+GlobalParameters.get.splitClauses.toString+"_cost_"+GlobalParameters.get.readCostType,v)
        }
        val oldFields=readJSONFieldToMap(solvingTimeFileName, fieldNames = initialFields.keys.toSeq)
        val updatedFields=
        if (oldFields.map(_._1).toSeq.contains(newField._1))
          oldFields.updated(newField._1, newField._2)
        else
          (oldFields.toSeq++Seq((newField._1,newField._2))).toMap
        writeSolvingTimeToJSON(solvingTimeFileName, updatedFields)

      }
    }
    sys.exit()

  }

  def mineTemplates(simplifiedClausesForGraph:Clauses,initialPredicatesForCEGAR:Map[Predicate, Seq[IFormula]],predGenerator : Dag[AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom, NormClause)]]): Unit ={
    //full code in TrainDataGeneratorTemplatesSmt2.scala

//    if (GlobalParameters.get.generateTemplates){
//      val unlabeledPredicateFileName=".unlabeledPredicates"
//      val generatedTpl = generateCombinationTemplates(simplifiedClausesForGraph, onlyLoopHead = true) //false
//      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName + unlabeledPredicateFileName + ".tpl")) {AbsReader.printHints(generatedTpl)}
//      sys.exit()
//    }

    val predAbs =
      new HornPredAbs(simplifiedClausesForGraph, initialPredicatesForCEGAR, predGenerator)

    val absBuilder =
      new StaticAbstractionBuilder(
        simplifiedClausesForGraph,
        GlobalParameters.get.templateBasedInterpolationType)

    def labelTemplates(unlabeledTemplates:VerificationHints): (VerificationHints,VerificationHints) ={
      if (GlobalParameters.get.debugLog){println("Mining the templates...")}
      val predMiner=new PredicateMiner(predAbs)
      //val predMiner=new PredicateMiner(predAbs)
      val positiveTemplates=predMiner.unitTwoVariableTemplates//predMiner.variableTemplates
      val costThreshold=99
      val filteredPositiveTemplates= VerificationHints((for((k,ps)<-positiveTemplates.predicateHints) yield {
        k->ps.filter(getParametersFromVerifHintElement(_)._2<costThreshold)
      }).filterNot(_._2.isEmpty))
      if (GlobalParameters.get.debugLog){
        println("predicates from " +lazabs.GlobalParameters.get.templateBasedInterpolationType.toString)
        absBuilder.abstractionHints.pretyPrintHints()
        println("mined predicates (unitTwoVariableTemplates)")
        positiveTemplates.pretyPrintHints()
        println("filtered mined predicates")
        filteredPositiveTemplates.pretyPrintHints()
      }
//      if(filteredPositiveTemplates.isEmpty){
//        HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/empty-mined-label/"+HintsSelection.getFileName(),"empty-mined-label")
//      }
      val labeledTemplates=VerificationHints(for ((kp,vp)<-unlabeledTemplates.predicateHints;
                                                  (kf,vf)<-filteredPositiveTemplates.predicateHints;
                                                  if kp.name==kf.name) yield
        kp -> (for (p<-vp;if termContains(vf.map(getParametersFromVerifHintElement(_)),getParametersFromVerifHintElement(p))._1) yield p)
      )
      if (GlobalParameters.get.debugLog){
        println("-"*10+"unlabeledTemplates"+"-"*10)
        unlabeledTemplates.pretyPrintHints()
        println("-"*10+"labeledTemplates"+"-"*10)
        labeledTemplates.pretyPrintHints()
      }
      (positiveTemplates,labeledTemplates)
      //filteredPositiveTemplates
    }

    val combinationTemplates=generateCombinationTemplates(simplifiedClausesForGraph,onlyLoopHead = false)
    val unlabeledTemplates=combinationTemplates
    val (positiveTemplates,labeledTemplates)=labelTemplates(unlabeledTemplates)

//    if(labeledTemplates.totalPredicateNumber==0){
//      HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/no-predicates-selected/"+HintsSelection.getFileName(),"labeledPredicates is empty")
//    }
    HintsSelection.writeTemplatesToFile(unlabeledTemplates,"unlabeledPredicates")
    HintsSelection.writeTemplatesToFile(labeledTemplates,"labeledPredicates")
    HintsSelection.writeTemplatesToFile(positiveTemplates,"minedPredicates")
    //HintsSelection.writePredicatesToFiles(unlabeledTemplates,labeledTemplates,positiveTemplates)

    sys.exit()
  }

  def getHornGraphForTemplatesSelection(simpClauses:Seq[Clause]): Unit ={
    val simplifiedClausesForGraph = HintsSelection.normalizedClausesForGraphs(simpClauses, VerificationHints(Map()))
    if (GlobalParameters.get.debugLog)
      simplifiedClausesForGraph.map(_.toPrologString).foreach(println)

    if (GlobalParameters.get.getHornGraph == true) {
      HintsSelection.filterInvalidInputs(simplifiedClausesForGraph)
      HintsSelection.checkMaxNode(simplifiedClausesForGraph)
    }

    val unlabeledTemplates=HintsSelection.wrappedReadHintsCheckExistence(simplifiedClausesForGraph,".unlabeledPredicates",generateCombinationTemplates(simplifiedClausesForGraph, onlyLoopHead = true) )
    if (unlabeledTemplates.totalPredicateNumber == 0 ) {
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName, "../benchmarks/exceptions/no-initial-predicates/" + GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/"), GlobalParameters.get.fileName.length), message = "no initial predicates")
    }
    val truePredicates = if (new java.io.File(GlobalParameters.get.fileName + ".labeledPredicates" + ".tpl").exists)
      HintsSelection.wrappedReadHints(simplifiedClausesForGraph, ".labeledPredicates")
    else if (new java.io.File(GlobalParameters.get.fileName + "." + GlobalParameters.get.hornGraphType.toString + ".JSON").exists)
      HintsSelection.readPredicateLabelFromOneJSON(new VerificationHintsInfo(unlabeledTemplates, VerificationHints(Map()), VerificationHints(Map())), "templateRelevanceLabel")
    else VerificationHints(Map())

    val predictedPredicates = if ((new java.io.File(GlobalParameters.get.fileName + "." + GlobalParameters.get.hornGraphType.toString + ".JSON")).exists)
      HintsSelection.readPredictedHints(simplifiedClausesForGraph, unlabeledTemplates)
    else
      VerificationHints(Map())

    //    val argumentInfo = HintsSelection.getArgumentLabel(simplifiedClausesForGraph,simpHints,predGenerator,disjunctive,
    //      argumentOccurrence = GlobalParameters.get.argumentOccurenceLabel,argumentBound =GlobalParameters.get.argumentBoundLabel)
    val argumentList = (for (p <- HornClauses.allPredicates(simplifiedClausesForGraph)) yield (p, p.arity)).toArray.sortBy(_._1.name)
    val argumentInfo =getArgumentInfo(argumentList)

    val clauseCollection = new ClauseInfo(simplifiedClausesForGraph, Seq())

    val hintsCollection = new VerificationHintsInfo(unlabeledTemplates, truePredicates, VerificationHints(Map()),predictedPredicates)
    GraphTranslator.drawAllHornGraph(clauseCollection, hintsCollection, argumentInfo)

    sys.exit()

  }
  def getSMT2Files(simplifiedClauses:Seq[Clause]): Unit ={
    GlobalParameters.get.hornGraphType=HornGraphType.monoDirectionLayerGraph
    HintsSelection.normalizedClausesForGraphs(simplifiedClauses, VerificationHints(Map()))
    GlobalParameters.get.hornGraphType=HornGraphType.hyperEdgeGraph
    HintsSelection.normalizedClausesForGraphs(simplifiedClauses, VerificationHints(Map()))
    sys.exit()
  }

  def randomPredicateGenerator(template: AbstractionMap, templateGNN: AbstractionMap, timeout: Long,explorationRate:Float)
                              (clauseDag: Dag[AndOrNode[NormClause, Unit]])
  : Either[Seq[(Predicate, Seq[Conjunction])], //new predicate
    Dag[(IAtom, NormClause)]] = {
    val predgen1 = TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(template, timeout)
    val predgen2 = TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(templateGNN, timeout)
    (predgen1(clauseDag), predgen2(clauseDag)) match {
      case (Left(newPredicate1), Left(newPredicate2)) => {
//        if (newPredicate1!=newPredicate2){
//          for (p <- newPredicate1)
//            println(Console.BLUE + p)
//          for (p <- newPredicate2)
//            println(Console.GREEN + p)
//        }

        val random = new Random
        if (GlobalParameters.get.fixRandomSeed)
          random.setSeed(42)

        if (random.nextInt(10)<10*explorationRate) {
//          for (p <- newPredicate2)
//            println(Console.CYAN_B + p)
          Left(newPredicate2)
        } else {
//          for (p <- newPredicate1)
//            println(Console.CYAN_B + p)
          Left(newPredicate1)
        }

      }
      case (Right(cex1), Right(cex2)) => {
        Right(cex1)
      }
    }
  }

  def combinedPredicateGenerator(template: AbstractionMap, templateGNN: AbstractionMap, timeout: Long)
                                           (clauseDag: Dag[AndOrNode[NormClause, Unit]])
  : Either[Seq[(Predicate, Seq[Conjunction])], //new predicate
    Dag[(IAtom, NormClause)]] = {
    val predgen1 = TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(template, timeout)
    val predgen2 = TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(templateGNN, timeout)

    (predgen1(clauseDag), predgen2(clauseDag)) match {
      case (Left(newPredicate1), Left(newPredicate2)) => {

//        if (newPredicate1!=newPredicate2){
//          println()
//          for (p <- newPredicate1)
//            println(Console.BLUE + p)
//          for (p <- newPredicate2)
//            println(Console.GREEN + p)
//
//        }
        val commonHead = (for (p1 <- newPredicate1; p2 <- newPredicate2; if p1._1 == p2._1) yield {
          (p1._1, (p1._2 ++ p2._2).distinct)
        }).distinct
        val p1Unique = for (p1 <- newPredicate1; if !newPredicate2.map(_._1).contains(p1._1)) yield p1
        val p2Unique = for (p2 <- newPredicate2; if !newPredicate1.map(_._1).contains(p2._1)) yield p2
        val mergedPredicates = commonHead ++ p1Unique ++ p2Unique

//        for (p <- mergedPredicates)
//          println(Console.CYAN_B + p)

        Left(mergedPredicates)
      }
      case (Right(cex1), Right(cex2)) => {
        Right(cex1)
      }
    }
  }

  def getRandomElement[A](seq: Seq[A]): A =
    {
      val random = new Random
      if (GlobalParameters.get.fixRandomSeed)
        random.setSeed(42)
      seq(random.nextInt(seq.length))
    }

}


