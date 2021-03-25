/**
 * Copyright (c) 2011-2020 Philipp Ruemmer, CHencheng Liang. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 * list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * * Neither the name of the authors nor the names of their
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
package lazabs.horn.concurrency
import ap.PresburgerTools
import ap.basetypes.IdealInt
import ap.parser.IExpression._
import ap.parser.{IExpression, IFormula, _}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.theories.TheoryCollector
import ap.types.{SortedPredicate, TypeTheory}
import ap.util.Timeout
import lazabs.GlobalParameters
import lazabs.horn.abstractions.AbstractionRecord.AbstractionMap
import lazabs.horn.abstractions.VerificationHints.{VerifHintElement, _}
import lazabs.horn.abstractions.{VerificationHints, _}
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs.{NormClause, RelationSymbol, SymbolFactory}
import lazabs.horn.bottomup.Util.Dag
import lazabs.horn.bottomup.{HornClauses, _}
import lazabs.horn.preprocessor.{ConstraintSimplifier, HornPreprocessor}
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}

import java.io.{File, PrintWriter}
import java.lang.System.currentTimeMillis
import java.nio.file.{Files, Paths, StandardCopyOption}
import scala.collection.mutable.{ArrayBuffer, LinkedHashMap, HashSet => MHashSet}
import scala.io.Source
import play.api.libs.json._

case class wrappedHintWithID(ID:Int,head:String, hint:String)

class LiteralCollector extends CollectingVisitor[Unit, Unit] {
  val literals = new MHashSet[IdealInt]
  def postVisit(t : IExpression, arg : Unit,
                subres : Seq[Unit]) : Unit = t match {
    case IIntLit(v)  =>
      literals += v
    case _ => ()
  }
}

object HintsSelection {
  val sp =new Simplifier
  val spAPI = ap.SimpleAPI.spawn
  val cs=new ConstraintSimplifier

  def measurePredicates(simplePredicatesGeneratorClauses:Clauses,predGenerator: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, HornPredAbs.NormClause)]], counterexampleMethod: HornPredAbs.CounterexampleMethod.Value,
                        predictedPredicates:Map[Predicate, Seq[IFormula]],
                        fullPredicates:Map[Predicate, Seq[IFormula]],
                        minimizedPredicates:Map[Predicate, Seq[IFormula]]): Unit ={
    HintsSelection.checkSolvability(simplePredicatesGeneratorClauses,predictedPredicates,predGenerator,counterexampleMethod,moveFile = false)

    //run trails to reduce time consumption deviation
    val trial_1=if (minimizedPredicates.isEmpty) Seq() else measureCEGAR(simplePredicatesGeneratorClauses,minimizedPredicates,predGenerator,counterexampleMethod)
    val trial_2=measureCEGAR(simplePredicatesGeneratorClauses,fullPredicates,predGenerator,counterexampleMethod)
    val trial_3=measureCEGAR(simplePredicatesGeneratorClauses,Map(),predGenerator,counterexampleMethod)
    val trial_4=measureCEGAR(simplePredicatesGeneratorClauses,predictedPredicates,predGenerator,counterexampleMethod)

    val measurementWithEmptyLabel=averageMeasureCEGAR(simplePredicatesGeneratorClauses,Map(),predGenerator,counterexampleMethod)
    val measurementWithTrueLabel=if (minimizedPredicates.isEmpty) measurementWithEmptyLabel else averageMeasureCEGAR(simplePredicatesGeneratorClauses,minimizedPredicates,predGenerator,counterexampleMethod)
    val measurementWithFullLabel=averageMeasureCEGAR(simplePredicatesGeneratorClauses,fullPredicates,predGenerator,counterexampleMethod)
    val measurementWithPredictedLabel=averageMeasureCEGAR(simplePredicatesGeneratorClauses,predictedPredicates,predGenerator,counterexampleMethod)


    val measurementList=Seq(("measurementWithTrueLabel",measurementWithTrueLabel),("measurementWithFullLabel",measurementWithFullLabel),
      ("measurementWithEmptyLabel",measurementWithEmptyLabel),("measurementWithPredictedLabel",measurementWithPredictedLabel))
    HintsSelection.writeMeasurementToJSON(measurementList)
  }
  def getExceptionalPredicatedGenerator():  Dag[AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]] ={
      (x: Dag[AndOrNode[HornPredAbs.NormClause, Unit]]) =>
        //throw new RuntimeException("interpolator exception")
        throw lazabs.Main.TimeoutException //if catch Counterexample and generate predicates, throw timeout exception
  }
  def getCounterexampleMethod(disjunctive:Boolean):  HornPredAbs.CounterexampleMethod.Value ={
    if (disjunctive)
      HornPredAbs.CounterexampleMethod.AllShortest
    else
      HornPredAbs.CounterexampleMethod.FirstBestShortest
  }
  def getMinimumSetPredicates(originalPredicates: Map[Predicate, Seq[IFormula]],simplePredicatesGeneratorClauses:Clauses,
                              exceptionalPredGen: Dag[AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]]=getExceptionalPredicatedGenerator(),
                              counterexampleMethod: HornPredAbs.CounterexampleMethod.Value=getCounterexampleMethod(GlobalParameters.get.disjunctive)):
  (Map[Predicate, Seq[IFormula]],Long) ={
    val startTimeForExtraction = System.currentTimeMillis()
    val mainTimeoutChecker = () => {
      if ((currentTimeMillis - startTimeForExtraction) > GlobalParameters.get.mainTimeout)
        throw lazabs.Main.MainTimeoutException //Main.TimeoutException
    }
    val predicatesExtractingBeginTime=System.currentTimeMillis
    var currentInitialPredicates:Map[Predicate,Seq[IFormula]]=sortHints(originalPredicates)
    var pIndex = 0
    if (!originalPredicates.isEmpty) {
      for ((head, preds) <- sortHints(originalPredicates)) {
        //var leftPredicates:Seq[IFormula]=preds
        for (p <- preds) {
          //delete p and useless predicates
          currentInitialPredicates=currentInitialPredicates.transform((k,v)=>if (k.name==head.name) {
            pIndex = v.indexWhere(x=>x.toString==p.toString)
            v.filterNot(x=>x.toString==p.toString)
          } else v)
          //leftPredicates=leftPredicates.filterNot(x=>x.toString==p.toString)
          //currentInitialPredicates=sortHints(currentInitialPredicates.filterNot(_._1==head)  ++ Map(head->leftPredicates))
          val predicateUsefulnessTimeoutChecker=clonedTimeChecker(GlobalParameters.get.threadTimeout)
          try GlobalParameters.parameters.withValue(predicateUsefulnessTimeoutChecker){
            println("----------------------------------- CEGAR --------------------------------------")
            new HornPredAbs(simplePredicatesGeneratorClauses, currentInitialPredicates, exceptionalPredGen,counterexampleMethod).result
            //p is useless
            mainTimeoutChecker()//check total used time for minimizing process
          }catch{
            case lazabs.Main.TimeoutException=>{
              //p is useful,append p to usefulPredicatesInCurrentHead, add it back to left predicates
              //leftPredicates=leftPredicates.:+(p)
              currentInitialPredicates=currentInitialPredicates.transform((k,v)=>if(k.name==head.name) {
                v.take(pIndex).:+(p) ++ v.drop(pIndex)
                //v.:+(p)
              } else v)
            }
            case _=>{throw lazabs.Main.MainTimeoutException}
          }
        }
        //minimumSetPredicate=minimumSetPredicate++Map(head->leftPredicates)
      }
    }
    val predicatesExtractingTime=(System.currentTimeMillis-predicatesExtractingBeginTime)/1000
    (currentInitialPredicates,predicatesExtractingTime)
  }


  def getPredicatesUsedInMinimizedPredicateFromCegar(initialPredicates:Map[Predicate, Seq[IFormula]],
                                                     minimizedPredicatesFromCegar:Map[Predicate, Seq[IFormula]],
                                                     simplePredicatesGeneratorClauses:Clauses,
                                                     exceptionalPredGen: Dag[AndOrNode[NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, NormClause)]]=getExceptionalPredicatedGenerator(),
                                                     counterexampleMethod: HornPredAbs.CounterexampleMethod.Value=getCounterexampleMethod(GlobalParameters.get.disjunctive)):
  (Map[Predicate, Seq[IFormula]],Map[Predicate, Seq[IFormula]]) ={
    val mergedPredicates=sortHints(mergePredicateMaps(initialPredicates,minimizedPredicatesFromCegar))
    //delete predicates from minimizedPredicatesFromCegar
    var usefulPredicatesInInitialPredicatesFormat: Map[Predicate, Seq[IFormula]]=Map()
    val startTimeForExtraction = System.currentTimeMillis()
    val mainTimeoutChecker = () => {
      if ((currentTimeMillis - startTimeForExtraction) > GlobalParameters.get.mainTimeout)
        throw lazabs.Main.MainTimeoutException //Main.TimeoutException
    }
    var pIndex=0
    var currentInitialPredicates:Map[Predicate,Seq[IFormula]]=mergedPredicates
    for ((head,preds)<-mergedPredicates){
      //todo: check this when varyGeneratedPredicates is on
      //var leftPredicates:Seq[IFormula]=preds
      for(p<-minimizedPredicatesFromCegar(head)){
        //delete p
        currentInitialPredicates=currentInitialPredicates.transform((k,v)=>if (k.name==head.name) {
          pIndex = v.indexWhere(x=>x.toString==p.toString)
          v.filterNot(x=>x.toString==p.toString)
        } else v)
//        leftPredicates=leftPredicates.filterNot(x=>x.toString==p.toString)
//        currentInitialPredicates=sortHints(currentInitialPredicates.filterNot(_._1.name==head.name) ++ Map(head->leftPredicates))
        val predicateUsefulnessTimeoutChecker=clonedTimeChecker(GlobalParameters.get.threadTimeout)
        try GlobalParameters.parameters.withValue(predicateUsefulnessTimeoutChecker){
          println("----------------------------------- CEGAR --------------------------------------")
          new HornPredAbs(simplePredicatesGeneratorClauses, currentInitialPredicates, exceptionalPredGen,counterexampleMethod).result
          //p is useless
          mainTimeoutChecker()//check total used time for minimizing process
        }catch{
          case lazabs.Main.TimeoutException=>{
            //p is useful
            //leftPredicates=leftPredicates.:+(p)
            //todo: intert it back in exact position where it is deleted
            currentInitialPredicates=currentInitialPredicates.transform((k,v)=>if(k.name==head.name) {
              v.take(pIndex).:+(p) ++ v.drop(pIndex)
              //v.:+(p)
            } else v)
          }
          case _=>{throw lazabs.Main.MainTimeoutException}
        }
      }
      //usefulPredicatesInInitialPredicatesFormat=usefulPredicatesInInitialPredicatesFormat++Map(head->leftPredicates)
    }
    usefulPredicatesInInitialPredicatesFormat=currentInitialPredicates
    //minimized
    val (minimizedUsefulPredicatesInInitialPredicateFormat,_)=getMinimumSetPredicates(usefulPredicatesInInitialPredicatesFormat,simplePredicatesGeneratorClauses,exceptionalPredGen,counterexampleMethod)
    //intersect
    //intersectPredicatesByString(minimizedUsefulPredicatesInInitialPredicateFormat,initialPredicates).mapValues(distinctByString(_))
    // use AuB-B without minimize
    //intersectPredicatesByString(usefulPredicatesInInitialPredicatesFormat,initialPredicates).mapValues(distinctByString(_))

    //debug:begin with different input predicates (even if the relation is subset) will generate different predicate set
//    val (minimizedMergedPredicates,_)=getMinimumSetPredicates(mergedPredicates,simplePredicatesGeneratorClauses,exceptionalPredGen,counterexampleMethod)
//    val (minimizedA,_)=getMinimumSetPredicates(initialPredicates,simplePredicatesGeneratorClauses,exceptionalPredGen,counterexampleMethod)
//    val (minimizedB,_)=getMinimumSetPredicates(minimizedPredicatesFromCegar,simplePredicatesGeneratorClauses,exceptionalPredGen,counterexampleMethod)
//    //vary predicates with the same logical meaning in B then minimize it.
//    val variedMinimizedB=(for ((k,v)<-minimizedB)yield {
//      k->(v ++ (for (p<-v) yield varyPredicateWithOutLogicChanges(p)))
//    }).mapValues(distinctByString(_))
//    val (minimizedVariedMinimizedB,_)=getMinimumSetPredicates(variedMinimizedB,simplePredicatesGeneratorClauses,exceptionalPredGen,counterexampleMethod)
//
//    println("A",initialPredicates.values.flatten.size)
//    printPredicateInMapFormat(initialPredicates,"A")
//    println("B",minimizedPredicatesFromCegar.values.flatten.size)
//    printPredicateInMapFormat(sortHints(minimizedPredicatesFromCegar),"B")
//    println("A u B",mergedPredicates.values.flatten.size)
//    printPredicateInMapFormat(sortHints(mergedPredicates),"A u B")
//    println("minimized A u B",minimizedMergedPredicates.values.flatten.size)
//    printPredicateInMapFormat(minimizedMergedPredicates,"minimized A u B")
//    println("minimized A",minimizedA.values.flatten.size)
//    printPredicateInMapFormat(minimizedA,"minimized A")
//    println("minimized B",minimizedB.values.flatten.size)
//    //printPredicateInMapFormat(minimizedB,"minimized B")
//    println("variedMinimized B",variedMinimizedB.values.flatten.size)
//    //printPredicateInMapFormat(variedMinimizedB,"variedMinimized B")
//    println("minimizedVariedMinimized B",minimizedVariedMinimizedB.values.flatten.size)
//    //printPredicateInMapFormat(minimizedVariedMinimizedB,"minimizedVariedMinimized B")
//    println("A u B -B",usefulPredicatesInInitialPredicatesFormat.values.flatten.size)
//    printPredicateInMapFormat(usefulPredicatesInInitialPredicatesFormat,"A u B -B")
//    println("minimized A u B -B",minimizedUsefulPredicatesInInitialPredicateFormat.values.flatten.size)
//    printPredicateInMapFormat(minimizedUsefulPredicatesInInitialPredicateFormat,"minimized A u B -B")
    // use AuB-B with minimize
    val res=intersectPredicatesByString(minimizedUsefulPredicatesInInitialPredicateFormat,initialPredicates).mapValues(distinctByString(_))
    //printPredicateInMapFormat(res,"A wedge F")
    //println("A wedge F",res.values.flatten.size)
    (res,minimizedUsefulPredicatesInInitialPredicateFormat)

  }

  def printPredicateInMapFormat(p:Map[Predicate,Seq[IFormula]],message:String=""): Unit ={
    println(message)
    for ((h,b)<-p) {
      println(h)
      for (bb<-b)
        println(bb)
    }
  }

  def clonedTimeChecker(to: Int, coefficient: Int = 1): GlobalParameters = {
    val startTimePredicateGenerator = currentTimeMillis
    val clonedGlovalParameter = GlobalParameters.get.clone
    clonedGlovalParameter.timeoutChecker = () => {
      //println("time check point:solvabilityTimeout", ((System.currentTimeMillis - startTimePredicateGenerator)/1000).toString + "/" + ((GlobalParameters.get.solvabilityTimeout * 5)/1000).toString)
      if ((currentTimeMillis - startTimePredicateGenerator) > (to * coefficient)) //timeout seconds
        throw lazabs.Main.TimeoutException //Main.TimeoutException
    }
    clonedGlovalParameter
  }

  def simplifyClausesForGraphs(simplifiedClauses:Clauses,hints:VerificationHints): Clauses ={
    val uniqueClauses = HintsSelection.distinctByString(simplifiedClauses)
    val (csSimplifiedClauses,_,_)=cs.process(uniqueClauses.distinct,hints)

    val simplePredicatesGeneratorClauses = GlobalParameters.get.hornGraphType match {
      case DrawHornGraph.HornGraphType.hyperEdgeGraph | DrawHornGraph.HornGraphType.equivalentHyperedgeGraph | DrawHornGraph.HornGraphType.concretizedHyperedgeGraph => for(clause<-csSimplifiedClauses) yield clause.normalize()
      case _ => csSimplifiedClauses
    }
    simplePredicatesGeneratorClauses
  }

  def transformPredicatesToCanonical( lastPredicates:Map[HornPredAbs.RelationSymbol, ArrayBuffer[HornPredAbs.RelationSymbolPred]]):
  Map[Predicate, Seq[IFormula]] ={
    var numberOfpredicates = 0
    val predicateFromCEGAR = for ((head, preds) <- lastPredicates) yield{
      // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
      val subst = (for ((c, n) <- head.arguments.head.iterator.zipWithIndex) yield (c, IVariable(n))).toMap
      //val headPredicate=new Predicate(head.name,head.arity) //class Predicate(val name : String, val arity : Int)
      val predicateSequence = for (p <- preds) yield {
        val simplifiedPredicate = sp(Internal2InputAbsy(p.rawPred, p.rs.sf.getFunctionEnc().predTranslation))
        val varPred = ConstantSubstVisitor(simplifiedPredicate, subst) //transform variables to _1,_2,_3...
        numberOfpredicates = numberOfpredicates + 1
        varPred
      }
      head.pred -> predicateSequence.distinct.toSeq
    }
    predicateFromCEGAR
  }

  def checkSatisfiability(simplePredicatesGeneratorClauses: HornPreprocessor.Clauses,
                          originalPredicates: VerificationHints,
                          predicateGen: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
                            Either[Seq[(Predicate, Seq[Conjunction])],
                              Dag[(IAtom, HornPredAbs.NormClause)]], counterexampleMethod: HornPredAbs.CounterexampleMethod.Value,
                          moveFile: Boolean = true, exit: Boolean = true): Boolean = {
    val filePath = GlobalParameters.get.fileName
    val fileName=filePath.substring(filePath.lastIndexOf("/"),filePath.length)
    val solvabilityTimeoutChecker = clonedTimeChecker(GlobalParameters.get.solvabilityTimeout, 1)
    var satisfiability = true
    try GlobalParameters.parameters.withValue(solvabilityTimeoutChecker) {
      val cegar = new HornPredAbs(simplePredicatesGeneratorClauses,
        originalPredicates.toInitialPredicates, predicateGen,
        counterexampleMethod)
      cegar.result match {
        case Left(a) => {
          satisfiability = true
        }
        case Right(b) => {
          satisfiability = false
          println(Console.RED + "-"*10+"unsat"+"-"*10)
          if (moveFile == true)
            HintsSelection.moveRenameFile(filePath, "../benchmarks/exceptions/unsat/" + fileName)
          if (exit == true)
            sys.exit()
        }
      }
    } catch {
      case lazabs.Main.TimeoutException => {
        println(Console.RED + "-"*10 +"solvability-timeout"+"-"*10)
        HintsSelection.moveRenameFile(filePath, "../benchmarks/exceptions/solvability-timeout/" + fileName)
        sys.exit()
      }
    }

    satisfiability
  }

  def checkSolvability(simplePredicatesGeneratorClauses: HornPreprocessor.Clauses, originalPredicates: Map[Predicate, Seq[IFormula]], predicateGen: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
    Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom, HornPredAbs.NormClause)]], counterexampleMethod: HornPredAbs.CounterexampleMethod.Value,
                       fileName: String = "noFileName", moveFile: Boolean = true, exit: Boolean = true, coefficient: Int = 5): (Int, Map[Predicate, Seq[IFormula]]) = {
    println("check solvability using current predicates")
    var solveTime = (GlobalParameters.get.solvabilityTimeout / 1000).toInt
    val solvabilityTimeoutChecker = clonedTimeChecker(GlobalParameters.get.solvabilityTimeout, coefficient)
    val startTime = currentTimeMillis()
    var cegarGeneratedPredicates: Map[Predicate, Seq[IFormula]] = Map()
    try GlobalParameters.parameters.withValue(solvabilityTimeoutChecker) {
      val cegar = new HornPredAbs(simplePredicatesGeneratorClauses,
        originalPredicates, predicateGen,
        counterexampleMethod)
      solveTime = ((currentTimeMillis - startTime) / 1000).toInt
      val predicateFromCEGAR = HintsSelection.transformPredicatesToCanonical(cegar.predicates)
      cegarGeneratedPredicates = predicateFromCEGAR
    }
    catch {
      case lazabs.Main.TimeoutException => {
        println(Console.RED + "-"*10 +"solvability-timeout"+"-"*10)
        if (moveFile == true)
          HintsSelection.moveRenameFile(GlobalParameters.get.fileName, "../benchmarks/exceptions/solvability-timeout/" + fileName)
        if (exit == true)
          sys.exit() //throw TimeoutException
        solveTime = ((currentTimeMillis - startTime) / 1000).toInt
      }
      case _ => println(Console.RED + "-"*10+"solvability-debug"+"-"*10)
    }
    (solveTime, cegarGeneratedPredicates)
  }

  def writeSolvabilityToJSON[A](fields:Seq[(String, A)]): Unit ={
    val writer = new PrintWriter(new File(GlobalParameters.get.fileName + "." + "solvability" + ".JSON"))
    writer.write("{\n")
    writeFildToJSON(writer,fields)
    writer.write("}")
    writer.close()
  }

  def writeMeasurementToJSON(measurementList:Seq[(String,Seq[(String, Double)])]): Unit ={
    val writer = new PrintWriter(new File(GlobalParameters.get.fileName + "." + "measurement" + ".JSON"))
    writer.write("{\n")
    for(m<-measurementList.dropRight(1)){
      writer.write(DrawHornGraph.addQuotes(m._1)+": {\n")
      writeFildToJSON(writer,m._2)
      writer.write("},\n")
    }
    val last=measurementList.last
    writer.write(DrawHornGraph.addQuotes(last._1)+": {\n")
    writeFildToJSON(writer,last._2)
    writer.write("}\n")

    writer.write("\n}")
    writer.close()
  }
  def writeFildToJSON[A](writer:PrintWriter,fields:Seq[(String, A)]): Unit ={
    for (field<-fields.dropRight(1)){
      writer.write(DrawHornGraph.addQuotes(field._1)+":"+DrawHornGraph.addQuotes(field._2.toString)+",\n")
    }
    val last=fields.last
    writer.write(DrawHornGraph.addQuotes(last._1)+":"+DrawHornGraph.addQuotes(last._2.toString)+"\n")
  }

  def averageMeasureCEGAR(simplePredicatesGeneratorClauses: HornPreprocessor.Clauses,initialHints: Map[Predicate, Seq[IFormula]],predicateGenerator : Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
    Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom, HornPredAbs.NormClause)]],counterexampleMethod : HornPredAbs.CounterexampleMethod.Value =
                   HornPredAbs.CounterexampleMethod.FirstBestShortest,adverageTime:Int=20): Seq[Tuple2[String,Double]] ={
    val avg=(for (i<-Range(0,adverageTime,1)) yield{
      val mList=measureCEGAR(simplePredicatesGeneratorClauses,initialHints,predicateGenerator,counterexampleMethod)
      for (x<-mList) yield x._2
    }).transpose.map(_.sum/adverageTime)
    val measurementNameList=Seq("timeConsumptionForCEGAR","itearationNumber","generatedPredicateNumber","averagePredicateSize","predicateGeneratorTime","averagePredicateSize")
    for((m,name)<-avg.zip(measurementNameList)) yield Tuple2(name,m)
  }

  def measureCEGAR(simplePredicatesGeneratorClauses: HornPreprocessor.Clauses,initialHints: Map[Predicate, Seq[IFormula]],predicateGenerator : Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
    Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom, HornPredAbs.NormClause)]],counterexampleMethod : HornPredAbs.CounterexampleMethod.Value =
  HornPredAbs.CounterexampleMethod.FirstBestShortest): Seq[Tuple2[String,Double]] ={
    val startCEGARTime=currentTimeMillis()
    val Cegar = new HornPredAbs(simplePredicatesGeneratorClauses,
      initialHints,
      predicateGenerator,
      counterexampleMethod)
    val timeConsumptionForCEGAR=(currentTimeMillis()-startCEGARTime)
    println(Console.GREEN + "timeConsumptionForCEGAR (ms)",timeConsumptionForCEGAR)
    val measurementList:Seq[Tuple2[String,Double]]=Seq(Tuple2("timeConsumptionForCEGAR",timeConsumptionForCEGAR),Tuple2("itearationNumber",Cegar.itearationNumber),
      Tuple2("generatedPredicateNumber",Cegar.generatedPredicateNumber),Tuple2("averagePredicateSize",Cegar.averagePredicateSize),
      Tuple2("predicateGeneratorTime",Cegar.predicateGeneratorTime),Tuple2("averagePredicateSize",Cegar.averagePredicateSize))
    measurementList
  }

  def writePredicateDistributionToFiles(initialPredicates:VerificationHints,selectedPredicates:VerificationHints,
                                        labeledPredicates:VerificationHints,unlabeledPredicates:VerificationHints,simpleGeneratedPredicates:VerificationHints,
                                        constraintPredicates:VerificationHints,argumentConstantEqualPredicate:VerificationHints,outputAllPredicates:Boolean=true): Unit ={
    Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".unlabeledPredicates.tpl")) {
      AbsReader.printHints(unlabeledPredicates)}
    Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".labeledPredicates.tpl")) {
      AbsReader.printHints(labeledPredicates)}

    val writer=new PrintWriter(new File(GlobalParameters.get.fileName + ".predicateDistribution"))
    val positiveConstraintPredicates= for ((ck,cv)<-constraintPredicates.predicateHints;(lk,lv)<-selectedPredicates.predicateHints if ck.equals(lk)) yield ck->(for (p<-cv if lv.map(_.toString).contains(p.toString)) yield p)
    val predicateNumberOfPositiveConstraintPredicates = positiveConstraintPredicates.values.flatten.size
    val positiveArgumentConstantEqualPredicate = for ((ck,cv)<-argumentConstantEqualPredicate.predicateHints;(lk,lv)<-selectedPredicates.predicateHints if ck.equals(lk)) yield ck->(for (p<-cv if lv.map(_.toString).contains(p.toString)) yield p)
    val predicateNumberOfPositiveArgumentConstantEqualPredicate=positiveArgumentConstantEqualPredicate.values.flatten.size
    val predicatesFromCEGAR = for((ki,vi)<-initialPredicates.predicateHints;(ks,vs)<-simpleGeneratedPredicates.predicateHints if ki.equals(ks)) yield {ki->vi.map(_.toString).diff(vs.map(_.toString))}
    val positivePredicatesFromCEGAR = for ((ck,cv)<-predicatesFromCEGAR;(lk,lv)<-selectedPredicates.predicateHints if ck.equals(lk)) yield ck->(for (p<-cv if lv.map(_.toString).contains(p.toString)) yield p)
    val predicateNumberOfPositivePredicatesFromCEGAR=positivePredicatesFromCEGAR.values.flatten.size

    writer.println("vary predicates: " + (if(GlobalParameters.get.varyGeneratedPredicates==true) "on" else "off"))
    writer.println("Predicate distributions: ")
    writer.println("initialPredicates (initial predicatesFromCEGAR, heuristic simpleGeneratedPredicates):"+initialPredicates.predicateHints.values.flatten.size.toString)
    writer.println("selectedPredicates (initialPredicates go through CEGAR Filter):"+selectedPredicates.predicateHints.values.flatten.size.toString)
    writer.println("simpleGeneratedPredicates:"+simpleGeneratedPredicates.predicateHints.values.flatten.size.toString)
    writer.println("   constraintPredicates:"+constraintPredicates.predicateHints.values.flatten.size.toString)
    writer.println("       positiveConstraintPredicates:"+predicateNumberOfPositiveConstraintPredicates.toString)
    writer.println("       negativeConstraintPredicates:"+ (constraintPredicates.predicateHints.values.flatten.size - predicateNumberOfPositiveConstraintPredicates).toString)
    writer.println("   argumentConstantEqualPredicate:"+argumentConstantEqualPredicate.predicateHints.values.flatten.size.toString)
    writer.println("       positiveArgumentConstantEqualPredicate:"+predicateNumberOfPositiveArgumentConstantEqualPredicate.toString)
    writer.println("       negativeArgumentConstantEqualPredicate:"+ (argumentConstantEqualPredicate.predicateHints.values.flatten.size - predicateNumberOfPositiveArgumentConstantEqualPredicate).toString)
    //todo:see if we can get this in HornPredAbs?
    writer.println("initialPredicates - simpleGeneratedPredicates:"+predicatesFromCEGAR.values.flatten.size.toString)
    writer.println("       positive(initialPredicates - simpleGeneratedPredicates):"+predicateNumberOfPositivePredicatesFromCEGAR.toString)
    writer.println("       negative(initialPredicates - simpleGeneratedPredicates):"+(predicatesFromCEGAR.values.flatten.size-predicateNumberOfPositivePredicatesFromCEGAR).toString)
    writer.println("unlabeledPredicates:"+unlabeledPredicates.predicateHints.values.flatten.size.toString)
    writer.println("labeledPredicates:"+labeledPredicates.predicateHints.values.flatten.size.toString)
    writer.close()

    if (outputAllPredicates==true){
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".simpleGenerated.tpl")) {
        AbsReader.printHints(simpleGeneratedPredicates)}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".constraintPredicates.tpl")) {
        AbsReader.printHints(constraintPredicates)}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".positiveConstraintPredicates.tpl")) {
        AbsReader.printHints(VerificationHints(positiveConstraintPredicates))}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".argumentConstantEqualPredicate.tpl")) {
        AbsReader.printHints(argumentConstantEqualPredicate)}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".positiveArgumentConstantEqualPredicate.tpl")) {
        AbsReader.printHints(VerificationHints(positiveArgumentConstantEqualPredicate))}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".initial.tpl")) {
        AbsReader.printHints(initialPredicates)}
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName+".selected.tpl")) {
        AbsReader.printHints(selectedPredicates)}
    }
  }

//  def labelSimpleGeneratedPredicatesBySelectedPredicates(optimizedPredicate: Map[Predicate, Seq[IFormula]],
//                                                         simpleGeneratedPredicates: Map[Predicate, Seq[IFormula]]): Map[Predicate, Seq[IFormula]] ={
//    for ((ko,vo)<-optimizedPredicate;(ks,vs)<-simpleGeneratedPredicates; if ko.equals(ks) ) yield {
//      ko->(for (p<-vs if vo.map(_.toString).contains(p.toString))yield p)
//    }
//  }
  def intersectPredicatesByString(first: Map[Predicate, Seq[IFormula]],
                                  second:Map[Predicate, Seq[IFormula]]): Map[Predicate, Seq[IFormula]] ={
    for ((fk,fv)<-first;(sk,sv)<-second;if fk.equals(sk)) yield {
      fk->(for (p<-fv if sv.map(_.toString).contains(p.toString)) yield p)
    }
  }

  def varyPredicateWithOutLogicChanges(f:IFormula): IFormula = {
    //associativity
    //replace a-b to -1*x + b
    f match {
      case Eq(a,b)=>{
        //println(a.toString,"=",b.toString)
        Eq(varyTerm(a),varyTerm(b))
      }
      case Geq(a,b)=>{
        //println(a.toString,">=",b.toString)
        Geq(varyTerm(a),varyTerm(b))
      }
      case INot(subformula)=> INot(varyPredicateWithOutLogicChanges(subformula))
      case IQuantified(quan, subformula) =>  IQuantified(quan, varyPredicateWithOutLogicChanges(subformula))
      case IBinFormula(j, f1, f2) => IBinFormula(j, varyPredicateWithOutLogicChanges(f1), varyPredicateWithOutLogicChanges(f2))
      case _=> f
    }
  }


  def varyTerm(e:ITerm): ITerm = {
    e match {
      case IPlus(t1,t2)=> IPlus(varyTerm(t2),varyTerm(t1))
      case Difference(t1,t2)=> IPlus(varyTerm(t1),varyTerm(-1*t2))
      //case ITimes(coeff, subterm) => ITimes(coeff, varyTerm(subterm))
      case _=> e
    }
  }

  def varyPredicates(optimizedPredicate: Map[Predicate, Seq[IFormula]],verbose:Boolean=false): Map[Predicate, Seq[IFormula]] ={
    val transformedPredicates=optimizedPredicate.mapValues(_.map(HintsSelection.varyPredicateWithOutLogicChanges(_)).map(sp(_)))
    val mergedPredicates= mergePredicateMaps(transformedPredicates,optimizedPredicate)
    if (verbose==true){
      println("predicates before transform")
      transformPredicateMapToVerificationHints(optimizedPredicate).pretyPrintHints()
      //optimizedPredicate.foreach(k=>{println(k._1);k._2.foreach(println)})
      println("transformed predicates")
      transformPredicateMapToVerificationHints(transformedPredicates).pretyPrintHints()
      //transformedPredicates.foreach(k=>{println(k._1);k._2.foreach(println)})
      println("merged predicates")
      transformPredicateMapToVerificationHints(mergedPredicates).pretyPrintHints()
      //mergedPredicates.foreach(k=>{println(k._1);k._2.foreach(println)})
    }
    mergedPredicates.mapValues(distinctByString(_))
  }


  def readPredictedHints(simplifiedClausesForGraph: Clauses, fullInitialPredicates: VerificationHints): VerificationHints = {
    val predictedHints = {
      if (new java.io.File(GlobalParameters.get.fileName + "." + "predictedHints" + ".tpl").exists == true) {
        VerificationHints(HintsSelection.wrappedReadHints(simplifiedClausesForGraph, "predictedHints").toInitialPredicates.mapValues(_.map(sp(_)).map(VerificationHints.VerifHintInitPred(_))))
      }
      else if (HintsSelection.detectIfAJSONFieldExists("predictedLabel")) {
        val initialHintsCollection = new VerificationHintsInfo(fullInitialPredicates, VerificationHints(Map()), VerificationHints(Map()))
        HintsSelection.readPredicateLabelFromJSON(initialHintsCollection, "predictedLabel")
      }
      else {
        println(Console.RED + "no predicted predicates")
        VerificationHints(Map())
      }
    }
    if (GlobalParameters.get.log == true)
      Console.withOut(new java.io.FileOutputStream(GlobalParameters.get.fileName + ".predictedHints.tpl")) {
        AbsReader.printHints(predictedHints)
      }

    predictedHints
  }

  def detectIfAJSONFieldExists(readLabel: String = "predictedLabel"): Boolean ={
    val input_file = GlobalParameters.get.fileName+".hyperEdgeHornGraph.JSON"
    val json_content = scala.io.Source.fromFile(input_file).mkString
    val json_data = Json.parse(json_content)
    try{(json_data \ readLabel).validate[Array[Int]] match {
      case JsSuccess(templateLabel,_)=> true}
    }catch {
      case _=>{
        println("read json file field error")
        false}
    }
  }
  def readPredicateLabelFromJSON(initialHintsCollection: VerificationHintsInfo,readLabel:String="predictedLabel"): VerificationHints ={
    val initialHints=initialHintsCollection.initialHints.getPredicateHints.toSeq sortBy (_._1.name)
    val input_file = GlobalParameters.get.fileName+".hyperEdgeHornGraph.JSON"
    val json_content = scala.io.Source.fromFile(input_file).mkString
    val json_data = Json.parse(json_content)

    try{(json_data \ readLabel).validate[Array[Int]] match {
      case JsSuccess(templateLabel,_)=> }
    }catch {
      case _=>{
        println("read json file field error")
      sys.exit()}
    }

    val predictedLabel= (json_data \ readLabel).validate[Array[Int]] match {
      case JsSuccess(templateLabel,_)=> templateLabel
    }
    println("predictedLabel",predictedLabel.toList.length,predictedLabel.toList)


    val mapLengthList=for ((k,v)<-initialHints) yield v.length
    var splitTail=predictedLabel
    val splitedPredictedLabel = for(l<-mapLengthList) yield {
      val temp=splitTail.splitAt(l)._1
      splitTail=splitTail.splitAt(l)._2
      temp
    }
    for (x<-splitedPredictedLabel)
      println(x.toSeq,x.size)

    val labeledPredicates=(for (((k,v),label)<-initialHints zip splitedPredictedLabel) yield {
      k-> (for ((p,l)<-v zip label if l==1) yield p) //match labels with predicates
    }).filterNot(_._2.isEmpty) //delete empty head

    println("--------Filtered initial predicates---------")
    for((k,v)<-labeledPredicates) {
      println(k)
      for(p<-v)
        println(p)
    }

    //simplePredicates ++ simpHints
    VerificationHints(labeledPredicates.toMap)
  }

  def wrappedReadHints(simplifiedClausesForGraph:Seq[Clause],hintType:String=""):VerificationHints={
    val name2Pred =
      (for (Clause(head, body, _) <- simplifiedClausesForGraph.iterator;
            IAtom(p, _) <- (head :: body).iterator)
        yield (p.name -> p)).toMap
    HintsSelection.readHints(GlobalParameters.get.fileName+"."+hintType+".tpl", name2Pred)
  }

  def readHints(filename : String,
                name2Pred : Map[String, Predicate])
  : VerificationHints = filename match {
    case "" =>
      EmptyVerificationHints
    case hintsFile => {
      val reader = new AbsReader (
        new java.io.BufferedReader (
          new java.io.FileReader(hintsFile)))
      val hints =
        (for ((predName, hints) <- reader.allHints.toSeq.sortBy(_._1).iterator;
              pred = name2Pred get predName;
              if {
                if (pred.isDefined) {
                  if (pred.get.arity != reader.predArities(predName))
                    throw new Exception(
                      "Hints contain predicate with wrong arity: " +
                        predName + " (should be " + pred.get.arity + " but is " +
                        reader.predArities(predName) + ")")
                } else {
                  Console.err.println(
                    "   Ignoring hints for " + predName + "\n")
                }
                pred.isDefined
              }) yield {
          (pred.get, hints)
        }).toMap
      VerificationHints(hints)
    }
  }

  def getSimplePredicates( simplePredicatesGeneratorClauses: HornPreprocessor.Clauses,verbose:Boolean=false):  (Map[Predicate, Seq[IFormula]],Map[Predicate, Seq[IFormula]],Map[Predicate, Seq[IFormula]]) ={
//    for (clause <- simplePredicatesGeneratorClauses)
//      println(Console.BLUE + clause.toPrologString)
//    val constraintPredicates = (for(clause <- simplePredicatesGeneratorClauses;atom<-clause.allAtoms) yield {
//      val subst=(for(const<-clause.constants;(arg,n)<-atom.args.zipWithIndex; if const.name==arg.toString) yield const->IVariable(n)).toMap
//      val argumentReplacedPredicates= for(constraint <- LineariseVisitor(ConstantSubstVisitor(clause.constraint,subst), IBinJunctor.And)) yield constraint
//      val freeVariableReplacedPredicates= for(p<-argumentReplacedPredicates) yield{
//        val constants=SymbolCollector.constants(p)
//        if(constants.isEmpty)
//          p
//        else
//          IExpression.quanConsts(Quantifier.EX,constants,p)
//      }
//      atom.pred-> freeVariableReplacedPredicates
//    }).groupBy(_._1).mapValues(_.flatMap(_._2).distinct)

    //generate predicates from constraint
    val constraintPredicatesTemp= (for (clause<-simplePredicatesGeneratorClauses;atom<-clause.allAtoms) yield {
      //println(Console.BLUE + clause.toPrologString)
      val subst=(for(const<-clause.constants;(arg,n)<-atom.args.zipWithIndex; if const.name==arg.toString) yield const->IVariable(n)).toMap
      val argumentReplacedPredicates= ConstantSubstVisitor(clause.constraint,subst)
      val constants=SymbolCollector.constants(argumentReplacedPredicates)
      val freeVariableReplacedPredicates= {
        val simplifiedPredicates =
          if(constants.isEmpty)
            sp(argumentReplacedPredicates)
          else
            sp(IExpression.quanConsts(Quantifier.EX,constants,argumentReplacedPredicates))
        if(clause.body.map(_.toString).contains(atom.toString)) {
          (for (p<-LineariseVisitor(sp(simplifiedPredicates.unary_!),IBinJunctor.And)) yield p) ++ (for (p<-LineariseVisitor(simplifiedPredicates,IBinJunctor.And)) yield sp(p.unary_!))
        } else
          LineariseVisitor(simplifiedPredicates,IBinJunctor.And)
      }
      atom.pred-> freeVariableReplacedPredicates.map(sp(_)).filter(!_.isTrue).filter(!_.isFalse)//map(spAPI.simplify(_)) //get rid of true and false
    }).groupBy(_._1).mapValues(_.flatMap(_._2).distinct).filterKeys(_.arity!=0)
    val constraintPredicates=
      if(GlobalParameters.get.varyGeneratedPredicates==true)
        HintsSelection.varyPredicates(constraintPredicatesTemp)
      else
        constraintPredicatesTemp

    //generate predicates from clause's integer constants
    val integerConstantVisitor = new LiteralCollector
    val argumentConstantEqualPredicate = (
      for (clause <- simplePredicatesGeneratorClauses; atom <- clause.allAtoms) yield {
        integerConstantVisitor.visitWithoutResult(clause.constraint,()) //collect integer constant in clause
        val eqConstant = integerConstantVisitor.literals.toSeq
        integerConstantVisitor.literals.clear()
        atom.pred -> (for ((arg, n) <- atom.args.zipWithIndex) yield argumentEquationGenerator(n, eqConstant,arg)).flatten
      }
      ).groupBy(_._1).mapValues(_.flatMap(_._2).distinct).filterKeys(_.arity != 0)

    //merge constraint and constant predicates
    val simplelyGeneratedPredicates = mergePredicateMaps(constraintPredicates,argumentConstantEqualPredicate)
    if (verbose==true){
      println("--------predicates from constrains---------")
      for((k,v)<-constraintPredicates;p<-v) println(k,p)
      println("--------predicates from constant and argumenteEqation---------")
      for(cc<-argumentConstantEqualPredicate; b<-cc._2) println(cc._1,b)
      println("--------all generated predicates---------")
      for((k,v)<-simplelyGeneratedPredicates;(p,i)<-v.zipWithIndex) println(k,i,p)
    }

    (simplelyGeneratedPredicates,constraintPredicates,argumentConstantEqualPredicate)
  }
  def mergePredicateMaps(first:Map[Predicate,Seq[IFormula]],second:Map[Predicate,Seq[IFormula]]): Map[Predicate,Seq[IFormula]] ={
    if (first.isEmpty)
      second
    else if (second.isEmpty)
      first
    else
      (for ((cpKey, cpPredicates) <- first; (apKey, apPredicates) <- second; if cpKey.name==apKey.name) yield cpKey ->(cpPredicates ++ apPredicates)).mapValues(distinctByString(_))
  }

  def distinctByString[A](formulas:Seq[A]): Seq[A] ={
    val FormulaStrings = new MHashSet[String]
    val uniqueFormulas= formulas filter {f => FormulaStrings.add(f.toString)} //de-duplicate formulas
    uniqueFormulas
  }
  def isArgBoolean(arg:ITerm): Boolean ={
    Sort.sortOf(arg) match {
      case Sort.MultipleValueBool=>{true}
      case _=>{false}
    }
  }
  def argumentEquationGenerator(n:Int,eqConstant:Seq[IdealInt],arg:ITerm): Seq[IFormula] ={
    if(isArgBoolean(arg))
      Seq()
    else
      (for (c<-eqConstant) yield Seq(sp(Eq(IVariable(n),c)),sp(Geq(c,IVariable(n))),sp(Geq(c,IVariable(n))))).flatten
  }

  def moveRenameFile(sourceFilename: String, destinationFilename: String,message:String=""): Unit = {
    if (GlobalParameters.get.moveFile==true){
      println(Console.RED+"-"*5+message+"-"*5)
      val path = Files.move(
        Paths.get(sourceFilename),
        Paths.get(destinationFilename),
        StandardCopyOption.REPLACE_EXISTING
      )
      if (path != null) {
        println(s"moved the file $sourceFilename successfully")
      } else {
        println(s"could NOT move the file $sourceFilename")
      }
    }
  }
  def removeRelativeFiles(fileName:String): Unit ={
    Files.delete(Paths.get(fileName+".circles.gv"))
    Files.delete(Paths.get(fileName+".HornGraph"))
    Files.delete(Paths.get(fileName+".hyperEdgeHornGraph.gv"))
    Files.delete(Paths.get(fileName+".unlabeledPredicates.tpl"))
  }
  def copyRenameFile(sourceFilename: String, destinationFilename: String): Unit = {
    val path = Files.copy(
      Paths.get(sourceFilename),
      Paths.get(destinationFilename),
      StandardCopyOption.REPLACE_EXISTING
    )
    if (path != null) {
      println(s"moved the file $sourceFilename successfully")
    } else {
      println(s"could NOT move the file $sourceFilename")
    }
  }

  def getClausesInCounterExamples(result: Either[Map[Predicate, IFormula], Dag[(IAtom, Clause)]], clauses: Clauses): Clauses = {
    if (result.isRight)
    (result match {
      case Right(cex) => {
        for (node <- cex.subdagIterator; clau <- clauses if (node.d._2.equals(clau))) yield clau
      }
    }).toSeq
    else
      Seq()
  }

  def sortHints[A](hints: A): A = {
    hints match {
      case h:VerificationHints=>{
        var tempHints = VerificationHints(Map()) //sort the hints
        for ((oneHintKey, oneHintValue) <- h.getPredicateHints()) {
          val tempSeq = oneHintValue.sortBy(_.toString)
          tempHints = tempHints.addPredicateHints(Map(oneHintKey -> tempSeq))
        }
        tempHints.asInstanceOf[A]
      }
      case h:Map[Predicate,Seq[IFormula]]=>{
        val sortedByKey=h.toSeq.sortBy(_._1.name)
        (for ((oneHintKey, oneHintValue) <- sortedByKey) yield {
          val tempSeq = oneHintValue.sortBy(_.toString)
          oneHintKey->tempSeq
        }).toMap.asInstanceOf[A]
      }
    }

  }


  def getInitialPredicates(encoder: ParametricEncoder, simpHints: VerificationHints, simpClauses: Clauses): VerificationHints = {
    val interpolator = if (GlobalParameters.get.templateBasedInterpolation)
      Console.withErr(Console.out) {
        val builder =
          new StaticAbstractionBuilder(
            simpClauses,
            GlobalParameters.get.templateBasedInterpolationType)


        val autoAbstractionMap =
          builder.abstractionRecords
        val abstractionMap =
          if (encoder.globalPredicateTemplates.isEmpty) {
            autoAbstractionMap
          } else {

            val loopDetector = builder.loopDetector

            print("Using interpolation templates provided in program: ")


            val hintsAbstractionMap =
              loopDetector hints2AbstractionRecord simpHints //emptyHints
            //DEBUG

            println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

            AbstractionRecord.mergeMaps(autoAbstractionMap, hintsAbstractionMap) //autoAbstractionMap=Map()
          }

        TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
          abstractionMap,
          GlobalParameters.get.templateBasedInterpolationTimeout)
      } else {
      DagInterpolator.interpolatingPredicateGenCEXAndOr _
    }

    println("extract original predicates")
    val cegar = new HornPredAbs(simpClauses,
      simpHints.toInitialPredicates,
      interpolator)

    val LastPredicate = cegar.predicates //Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]]

    var originalPredicates: Map[Predicate, Seq[IFormula]] = Map()
    //show original predicates
    var numberOfpredicates = 0
    println("Original predicates:")
    for ((head, preds) <- LastPredicate) {
      // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
      println("key:" + head.pred)
      val subst = (for ((c, n) <- head.arguments.head.iterator.zipWithIndex) yield (c, IVariable(n))).toMap
      //val headPredicate=new Predicate(head.name,head.arity) //class Predicate(val name : String, val arity : Int)
      val predicateSequence = for (p <- preds) yield {
        val simplifiedPredicate = sp (Internal2InputAbsy(p.rawPred, p.rs.sf.getFunctionEnc().predTranslation))
        //println("value:"+simplifiedPredicate)
        val varPred = ConstantSubstVisitor(simplifiedPredicate, subst) //transform variables to _1,_2,_3...
        println("value:" + varPred)
        numberOfpredicates = numberOfpredicates + 1
        varPred
      }
      originalPredicates = originalPredicates ++ Map(head.pred -> predicateSequence.distinct)
    }
    //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
    var initialPredicates = VerificationHints(Map())
    for ((head, preds) <- originalPredicates) {
      var x: Seq[VerifHintElement] = Seq()
      for (p <- preds) {
        x = x ++ Seq(VerificationHints.VerifHintInitPred(p))
      }
      initialPredicates = initialPredicates.addPredicateHints(Map(head -> x))
    }
    //    var initialPredicates:VerificationHints=VerificationHints(Map())
    //    for((head,preds)<-originalPredicates){
    //      val predicateSeq=
    //      for (p<-preds)yield {
    //        VerificationHints.VerifHintInitPred(p)
    //      }
    //      initialPredicates=initialPredicates.addPredicateHints(Map(head->predicateSeq))
    //    }
    return initialPredicates
  }


  def tryAndTestSelectionPredicate(encoder: ParametricEncoder, simpHints: VerificationHints,
                                   simpClauses: Clauses, file: String, InitialHintsWithID: Seq[wrappedHintWithID]): VerificationHints = {

    val interpolator = if (GlobalParameters.get.templateBasedInterpolation)
      Console.withErr(Console.out) {
        val builder =
          new StaticAbstractionBuilder(
            simpClauses,
            GlobalParameters.get.templateBasedInterpolationType)


        val autoAbstractionMap =
          builder.abstractionRecords
        val abstractionMap =
          if (encoder.globalPredicateTemplates.isEmpty) {
            autoAbstractionMap
          } else {

            val loopDetector = builder.loopDetector

            print("Using interpolation templates provided in program: ")


            val hintsAbstractionMap =
              loopDetector hints2AbstractionRecord simpHints //emptyHints currentTemplates
            //DEBUG

            println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

            AbstractionRecord.mergeMaps(autoAbstractionMap, hintsAbstractionMap) //autoAbstractionMap=Map()
          }

        TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
          abstractionMap,
          GlobalParameters.get.templateBasedInterpolationTimeout)
      } else {
      DagInterpolator.interpolatingPredicateGenCEXAndOr _
    }
    val fileName = file.substring(file.lastIndexOf("/") + 1)
    val timeOut = GlobalParameters.get.threadTimeout //timeout

    val exceptionalPredGen: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
      Either[Seq[(Predicate, Seq[Conjunction])],
        Dag[(IAtom, HornPredAbs.NormClause)]] =
      (x: Dag[AndOrNode[HornPredAbs.NormClause, Unit]]) =>
        //throw new RuntimeException("interpolator exception")
        throw lazabs.Main.TimeoutException

    println("extract original predicates")
    val cegar = new HornPredAbs(simpClauses,
      simpHints.toInitialPredicates,
      interpolator)

    val LastPredicate = cegar.predicates //Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]]
    if (LastPredicate.isEmpty) {
      return VerificationHints(Map())
    } else {

      var originalPredicates: Map[Predicate, Seq[IFormula]] = Map()
      //show LastPredicate
      println("Original predicates:")
      for ((head, preds) <- LastPredicate) {
        // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
        val subst = (for ((c, n) <- head.arguments.head.iterator.zipWithIndex) yield (c, IVariable(n))).toMap
        //val headPredicate=new Predicate(head.name,head.arity) //class Predicate(val name : String, val arity : Int)
        val predicateSequence = for (p <- preds) yield {
          val simplifiedPredicate = sp (Internal2InputAbsy(p.rawPred, p.rs.sf.getFunctionEnc().predTranslation))
          //println("value:"+simplifiedPredicate)
          val varPred = ConstantSubstVisitor(simplifiedPredicate, subst) //transform variables to _1,_2,_3...
          println("value:" + varPred)
          varPred
        }
        originalPredicates = originalPredicates ++ Map(head.pred -> predicateSequence.distinct)
      }

      //      var initialPredicates = VerificationHints(Map())
      //      for ((head, preds) <- originalPredicates) {
      //        var x: Seq[VerifHintElement] = Seq()
      //        for (p <- preds) {
      //          x = x ++ Seq(VerificationHints.VerifHintInitPred(p))
      //        }
      //        initialPredicates = initialPredicates.addPredicateHints(Map(head -> x))
      //      }
      //
      //      val sortedHints=HintsSelection.sortHints(initialPredicates)
      ////      if(sortedHints.isEmpty){}else{
      //        //write selected hints with IDs to file
      //        val InitialHintsWithID=initialIDForHints(sortedHints) //ID:head->hint
      //        println("---initialHints-----")
      //        for (wrappedHint<-InitialHintsWithID){
      //          println(wrappedHint.ID.toString,wrappedHint.head,wrappedHint.hint)
      //        }

      //Predicate selection begin
      println("------Predicates selection begin----")
      var PositiveHintsWithID: Seq[wrappedHintWithID] = Seq()
      var NegativeHintsWithID: Seq[wrappedHintWithID] = Seq()
      var optimizedPredicate: Map[Predicate, Seq[IFormula]] = Map()
      var currentPredicate: Map[Predicate, Seq[IFormula]] = originalPredicates
      for ((head, preds) <- originalPredicates) {
        // transfor Map[relationSymbols.values,ArrayBuffer[RelationSymbolPred]] to Map[Predicate, Seq[IFormula]]
        var criticalPredicatesSeq: Seq[IFormula] = Seq()
        var redundantPredicatesSeq: Seq[IFormula] = Seq()
        var CurrentTemplates = VerificationHints(Map())

        for (p <- preds) {
          //println("before delete")
          //          println("head",head)
          //          println("predicates",currentPredicate(head))
          //          //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
          //          for ((head,preds)<-currentPredicate) {
          //            val x:Seq[VerifHintElement]=
          //            for (p<-preds)yield{
          //              VerificationHints.VerifHintInitPred(p)
          //            }
          //            CurrentTemplates=CurrentTemplates.addPredicateHints(Map(head->x))
          //          }
          //          CurrentTemplates=HintsSelection.sortHints(CurrentTemplates)
          //          CurrentTemplates.pretyPrintHints()

          //delete one predicate
          println("delete predicate", p)
          val currentPredicateSeq = currentPredicate(head).filter(_ != p) //delete one predicate
          currentPredicate = currentPredicate.filterKeys(_ != head) //delete original head
          if (!currentPredicateSeq.isEmpty) {
            currentPredicate = currentPredicate ++ Map(head -> currentPredicateSeq) //add the head with deleted predicate
          }

          //println("after delete")
          //          println("head",head)
          //          println("predicates",currentPredicate(head))

          //          //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
          //          for ((head,preds)<-currentPredicate) {
          //            var x:Seq[VerifHintElement]=Seq()
          //            for (p<-preds){
          //              x=x++Seq(VerificationHints.VerifHintInitPred(p))
          //            }
          //            CurrentTemplates=CurrentTemplates.addPredicateHints(Map(head->x))
          //          }
          //          CurrentTemplates=HintsSelection.sortHints(CurrentTemplates)
          //          CurrentTemplates.pretyPrintHints()


          //try cegar
          val startTime = currentTimeMillis
          val toParams = GlobalParameters.get.clone
          toParams.timeoutChecker = () => {
            if ((currentTimeMillis - startTime) > timeOut ) //timeout milliseconds
              throw lazabs.Main.TimeoutException //Main.TimeoutException
          }
          try {
            GlobalParameters.parameters.withValue(toParams) {


              println(
                "----------------------------------- CEGAR --------------------------------------")

              new HornPredAbs(simpClauses, // loop
                currentPredicate, //emptyHints currentPredicate CurrentTemplates
                exceptionalPredGen).result
              //not timeout
              println("add redundant predicate", p.toString)
              redundantPredicatesSeq = redundantPredicatesSeq ++ Seq(p)
              //add useless hint to NegativeHintsWithID   //ID:head->hint
              for (wrappedHint <- InitialHintsWithID) {
                val pVerifHintInitPred = "VerifHintInitPred(" + p.toString + ")"
                if (wrappedHint.head == head.name.toString && wrappedHint.hint == pVerifHintInitPred) {
                  NegativeHintsWithID = NegativeHintsWithID ++ Seq(wrappedHint) //some redundancy
                }
              }
            }
          } catch {
            case lazabs.Main.TimeoutException => {
              //catch timeout
              println("add critical predicate", p.toString)
              criticalPredicatesSeq = criticalPredicatesSeq ++ Seq(p)
              //add deleted predicate back to curren predicate
              currentPredicate = currentPredicate.filterKeys(_ != head) //delete original head
              currentPredicate = currentPredicate ++ Map(head -> (currentPredicateSeq ++ Seq(p))) //add the head with deleted predicate
              //
              for (wrappedHint <- InitialHintsWithID) { //add useful hint to PositiveHintsWithID
                val pVerifHintInitPred = "VerifHintInitPred(" + p.toString + ")"
                if (head.name.toString() == wrappedHint.head && wrappedHint.hint == pVerifHintInitPred) {
                  PositiveHintsWithID = PositiveHintsWithID ++ Seq(wrappedHint)
                }
              }
            }
          }
        }
        //store selected predicate
        if (!criticalPredicatesSeq.isEmpty) {
          optimizedPredicate = optimizedPredicate ++ Map(head -> criticalPredicatesSeq)
        }
        println("current head:", head.toString())
        println("critical predicates:", criticalPredicatesSeq.toString())
        println("redundant predicates", redundantPredicatesSeq.toString())
      }


      //transform Map[Predicate,Seq[IFomula] to VerificationHints:[Predicate,VerifHintElement]
      var selectedTemplates = VerificationHints(Map())
      for ((head, preds) <- optimizedPredicate) {
        var x: Seq[VerifHintElement] = Seq()
        for (p <- preds) {
          x = x ++ Seq(VerificationHints.VerifHintInitPred(p))
        }
        selectedTemplates = selectedTemplates.addPredicateHints(Map(head -> x))
      }

      println("\n------------predicates selection end-------------------------")
      //println("\nsimpHints Hints:")
      //simpHints.pretyPrintHints()
      println("\nOptimized Hints:")
      println("!@@@@")
      selectedTemplates.pretyPrintHints()
      println("@@@@!")
      println("timeout:" + GlobalParameters.get.threadTimeout)

      println("\n------------test selected predicates-------------------------")
      val test = new HornPredAbs(simpClauses, // loop
        selectedTemplates.toInitialPredicates, //emptyHints
        exceptionalPredGen).result
      println("-----------------test finished-----------------------")

      if (selectedTemplates.isEmpty) {
        //writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial") //write hints and their ID to file
      } else {
        //only write to file when optimized hint is not empty
        writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial") //write hints and their ID to file
        writeHintsWithIDToFile(PositiveHintsWithID, fileName, "positive")
        writeHintsWithIDToFile(NegativeHintsWithID, fileName, "negative")
      }

      return selectedTemplates
    }

  }


  def tryAndTestSelectionTemplates(encoder: ParametricEncoder, simpHints: VerificationHints,
                                   simpClauses: Clauses, file: String, InitialHintsWithID: Seq[wrappedHintWithID],
                                   predicateFlag: Boolean = true): (VerificationHints, Either[Map[Predicate, IFormula], Dag[(IAtom, Clause)]]) = {


    val fileName = file.substring(file.lastIndexOf("/") + 1)
    val timeOut = GlobalParameters.get.threadTimeout //timeout
    var currentTemplates = simpHints
    var optimizedTemplates = VerificationHints(Map())
    var PositiveHintsWithID: Seq[wrappedHintWithID] = Seq()
    var NegativeHintsWithID: Seq[wrappedHintWithID] = Seq()

    println("-------------------------Hints selection begins------------------------------------------")
    if (simpHints.isEmpty) {
      val result: Either[Map[Predicate, IFormula], Dag[(IAtom, Clause)]] = Left(Map())
      (simpHints, result)
    } else {
      for ((head, preds) <- simpHints.predicateHints) {
        var criticalTemplatesSeq: Seq[VerifHintElement] = Seq()
        var redundantTemplatesSeq: Seq[VerifHintElement] = Seq()
        for (p <- preds) {
          //delete on template in a head
          val currentTemplatesList = currentTemplates.predicateHints(head).filter(_ != p)
          currentTemplates = currentTemplates.filterNotPredicates(Set(head))

          currentTemplates = currentTemplates.addPredicateHints(Map(head -> currentTemplatesList))

          //try cegar

          val startTime = currentTimeMillis
          val toParams = GlobalParameters.get.clone
          toParams.timeoutChecker = () => {
            if ((currentTimeMillis - startTime) > timeOut ) //timeout milliseconds
              throw lazabs.Main.TimeoutException //Main.TimeoutException
          }
          try {
            GlobalParameters.parameters.withValue(toParams) {
              //interpolator
              val interpolator = if (GlobalParameters.get.templateBasedInterpolation)
                Console.withErr(Console.out) {
                  val builder =
                    new StaticAbstractionBuilder(
                      simpClauses,
                      GlobalParameters.get.templateBasedInterpolationType)


                  val autoAbstractionMap =
                    builder.abstractionRecords
                  val abstractionMap =
                    if (encoder.globalPredicateTemplates.isEmpty) {
                      autoAbstractionMap
                    } else {
                      val loopDetector = builder.loopDetector
                      print("Using interpolation templates provided in program: ")
                      val hintsAbstractionMap =
                        loopDetector hints2AbstractionRecord currentTemplates //emptyHints criticalHints
                      //DEBUG
                      println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

                      AbstractionRecord.mergeMaps(Map(), hintsAbstractionMap) //autoAbstractionMap=Map()
                    }

                  TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
                    abstractionMap,
                    GlobalParameters.get.templateBasedInterpolationTimeout)
                } else {
                DagInterpolator.interpolatingPredicateGenCEXAndOr _
              }

              println(
                "----------------------------------- CEGAR --------------------------------------")

              new HornPredAbs(simpClauses, // loop
                currentTemplates.toInitialPredicates, //emptyHints
                interpolator).result

              // not timeout ...
              println("Delete a redundant hint:\n" + head + "\n" + p)
              redundantTemplatesSeq = redundantTemplatesSeq ++ Seq(p)

              for (wrappedHint <- InitialHintsWithID) { //add useless hint to NegativeHintsWithID   //ID:head->hint
                if (head.name.toString == wrappedHint.head && wrappedHint.hint == p.toString) {
                  NegativeHintsWithID = NegativeHintsWithID ++ Seq(wrappedHint)
                }
              }


            }

          } catch {
            // ,... Main.TimeoutException
            //time out
            case lazabs.Main.TimeoutException => {
              println("Add a critical hint\n" + head + "\n" + p)
              criticalTemplatesSeq = criticalTemplatesSeq ++ Seq(p)
              currentTemplates = currentTemplates.filterNotPredicates(Set(head))
              //currentTemplates=currentTemplates.filterPredicates(GSet(oneHintKey))
              currentTemplates = currentTemplates.addPredicateHints(Map(head -> (currentTemplatesList ++ Seq(p)))) //beforeDeleteHints

              for (wrappedHint <- InitialHintsWithID) { //add useful hint to PositiveHintsWithID
                if (head.name.toString() == wrappedHint.head && wrappedHint.hint == p.toString) {
                  PositiveHintsWithID = PositiveHintsWithID ++ Seq(wrappedHint)
                }
              }

            }

          } //catch end

        } // second for end
        if (!criticalTemplatesSeq.isEmpty) {
          optimizedTemplates = optimizedTemplates.addPredicateHints(Map(head -> criticalTemplatesSeq))
        }

      } // first for end


      println("\n------------DEBUG-Select critical hints end-------------------------")

      println("\n------------test selected hints-------------------------")
      val result = GlobalParameters.parameters.withValue(GlobalParameters.get.clone) {
        //interpolator
        val interpolator = if (GlobalParameters.get.templateBasedInterpolation)
          Console.withErr(Console.out) {
            val builder =
              new StaticAbstractionBuilder(
                simpClauses,
                GlobalParameters.get.templateBasedInterpolationType)
            val autoAbstractionMap =
              builder.abstractionRecords
            val abstractionMap =
              if (encoder.globalPredicateTemplates.isEmpty) {
                autoAbstractionMap
              } else {
                val loopDetector = builder.loopDetector
                print("Using interpolation templates provided in program: ")
                val hintsAbstractionMap =
                  loopDetector hints2AbstractionRecord currentTemplates //emptyHints criticalHints
                //DEBUG
                println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

                AbstractionRecord.mergeMaps(Map(), hintsAbstractionMap) //autoAbstractionMap=Map()
              }

            TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
              abstractionMap,
              GlobalParameters.get.templateBasedInterpolationTimeout)
          } else {
          DagInterpolator.interpolatingPredicateGenCEXAndOr _
        }

        println(
          "----------------------------------- CEGAR --------------------------------------")

        new HornPredAbs(simpClauses, // loop
          optimizedTemplates.toInitialPredicates, //emptyHints
          interpolator).result
      }

      //println("\nsimpHints Hints:")
      //simpHints.pretyPrintHints()
      println("\nOptimized Hints:")
      println("!@@@@")
      optimizedTemplates.pretyPrintHints()
      println("@@@@!")
      println("timeout:" + GlobalParameters.get.threadTimeout)
      //GlobalParameters.get.printHints=optimizedHints


      if (optimizedTemplates.isEmpty) {
        //writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial")//write hints and their ID to file
      } else {
        //only write to file when optimized hint is not empty
        writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial") //write hints and their ID to file
        writeHintsWithIDToFile(PositiveHintsWithID, fileName, "positive")
        writeHintsWithIDToFile(NegativeHintsWithID, fileName, "negative")
      }


      (optimizedTemplates, result)
    }


  }


  def tryAndTestSelectionTemplatesSmt(simpHints: VerificationHints, simpClauses: Clauses, file: String, InitialHintsWithID: Seq[wrappedHintWithID],
                                      counterexampleMethod: HornPredAbs.CounterexampleMethod.Value =
                                      HornPredAbs.CounterexampleMethod.FirstBestShortest,
                                      hintsAbstraction: AbstractionMap
                                     ): (VerificationHints, Either[Map[Predicate, IFormula], Dag[(IAtom, Clause)]]) = {

    val fileName = file.substring(file.lastIndexOf("/") + 1)
    val timeOut = GlobalParameters.get.threadTimeout //timeout
    //val timeOut=10
    var currentTemplates = simpHints
    var optimizedHints = VerificationHints(Map()) // store final selected heads and hints
    //val InitialHintsWithID=initialIDForHints(simpHints)
    var PositiveHintsWithID: Seq[wrappedHintWithID] = Seq()
    var NegativeHintsWithID: Seq[wrappedHintWithID] = Seq()

    if (simpHints.isEmpty || lazabs.GlobalParameters.get.templateBasedInterpolation == false) {
      println("simpHints is empty or abstract:off")
      val result: Either[Map[Predicate, IFormula], Dag[(IAtom, Clause)]] = Left(Map())
      (simpHints, result)
    }
    else {
      println("-------------------------Hints selection begins------------------------------------------")
      for ((head, oneHintValue) <- simpHints.getPredicateHints()) { //loop for head
        println("Head:" + head)
        println(oneHintValue)
        var criticalHintsList: Seq[VerifHintElement] = Seq()
        var redundantHintsList: Seq[VerifHintElement] = Seq()
        var currentHintsList = simpHints.predicateHints(head) //extract hints in this head

        for (oneHint <- simpHints.predicateHints(head)) { //loop for every hint in one head
          println("Current hints:")
          currentTemplates.pretyPrintHints()

          println("delete: \n" + head + " \n" + oneHint)
          currentHintsList = currentHintsList.filter(_ != oneHint) //delete one hint from hint list
          currentTemplates = currentTemplates.filterNotPredicates(Set(head)) //delete the head

          currentTemplates = currentTemplates.addPredicateHints(Map(head -> currentHintsList)) //add head with one hint back

          println("After delete:\n")
          currentTemplates.pretyPrintHints()

          val startTime = currentTimeMillis
          val toParams = GlobalParameters.get.clone
          toParams.timeoutChecker = () => {
            if ((currentTimeMillis - startTime) > timeOut ) //timeout milliseconds
              throw lazabs.Main.TimeoutException //Main.TimeoutException
          }


          try {
            GlobalParameters.parameters.withValue(toParams) {
              val outStream =
                if (GlobalParameters.get.logStat)
                  Console.err
                else
                  HornWrapper.NullStream
              val loopDetector = new LoopDetector(simpClauses)
              val autoAbstraction = loopDetector.hints2AbstractionRecord(currentTemplates)
              val predGenerator = Console.withErr(outStream) {
                if (lazabs.GlobalParameters.get.templateBasedInterpolation) {
                  val fullAbstractionMap =
                    AbstractionRecord.mergeMaps(Map(), autoAbstraction) //hintsAbstraction,autoAbstraction replaced by Map()

                  if (fullAbstractionMap.isEmpty) {
                    DagInterpolator.interpolatingPredicateGenCEXAndOr _
                  }

                  else {
                    TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
                      fullAbstractionMap,
                      lazabs.GlobalParameters.get.templateBasedInterpolationTimeout)
                  }

                } else {
                  DagInterpolator.interpolatingPredicateGenCEXAndOr _ //if abstract:off
                }
              }
              println(
                "----------------------------------- CEGAR --------------------------------------")

              (new HornPredAbs(simpClauses, //simplifiedClauses
                currentTemplates.toInitialPredicates, predGenerator,
                counterexampleMethod)).result


              // not timeout ...
              println("Delete a redundant hint:\n" + head + "\n" + oneHint)
              redundantHintsList = redundantHintsList ++ Seq(oneHint)
              //add useless hint to NegativeHintsWithID   //ID:head->hint
              for (wrappedHint <- InitialHintsWithID) {
                if (head.name.toString == wrappedHint.head && wrappedHint.hint == oneHint.toString) {
                  NegativeHintsWithID = NegativeHintsWithID ++ Seq(wrappedHint)
                }
              }

            }

          } catch {
            // ,... Main.TimeoutException
            //time out
            case lazabs.Main.TimeoutException =>
              println("Add a critical hint\n" + head + "\n" + oneHint)
              criticalHintsList = criticalHintsList ++ Seq(oneHint)
              currentHintsList = currentHintsList ++ Seq(oneHint)
              currentTemplates = currentTemplates.filterNotPredicates(Set(head))
              currentTemplates = currentTemplates.addPredicateHints(Map(head -> currentHintsList))
              //add useful hint to PositiveHintsWithID
              for (wrappedHint <- InitialHintsWithID) {
                if (head.name.toString() == wrappedHint.head && wrappedHint.hint == oneHint.toString) {
                  PositiveHintsWithID = PositiveHintsWithID ++ Seq(wrappedHint)
                }
              }
          }

          println("Current head:" + head)
          println
          println("criticalHintsList" + criticalHintsList)
          println
          println("redundantHintsList" + redundantHintsList)
          println("---------------------------------------------------------------")
          //optimizedHints=optimizedHints.addPredicateHints(Map(oneHintKey->criticalHintsList))

        } //second for end
        if (!criticalHintsList.isEmpty) { //add critical hints in one head to optimizedHints map
          optimizedHints = optimizedHints.addPredicateHints(Map(head -> criticalHintsList))
        }
      } //first for end

      println("\n------------DEBUG-Select critical hints end-------------------------")
      val result = GlobalParameters.parameters.withValue(GlobalParameters.get.clone) {
        val outStream =
          if (GlobalParameters.get.logStat)
            Console.err
          else
            HornWrapper.NullStream
        val loopDetector = new LoopDetector(simpClauses)
        val autoAbstraction = loopDetector.hints2AbstractionRecord(currentTemplates)
        val predGenerator = Console.withErr(outStream) {
          if (lazabs.GlobalParameters.get.templateBasedInterpolation) {
            val fullAbstractionMap =
              AbstractionRecord.mergeMaps(Map(), autoAbstraction) //hintsAbstraction,autoAbstraction replaced by Map()

            if (fullAbstractionMap.isEmpty) {
              DagInterpolator.interpolatingPredicateGenCEXAndOr _
            }

            else {
              TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
                fullAbstractionMap,
                lazabs.GlobalParameters.get.templateBasedInterpolationTimeout)
            }

          } else {
            DagInterpolator.interpolatingPredicateGenCEXAndOr _ //if abstract:off
          }
        }
        println(
          "----------------------------------- CEGAR --------------------------------------")

        (new HornPredAbs(simpClauses, //simplifiedClauses
          optimizedHints.toInitialPredicates, predGenerator,
          counterexampleMethod)).result
      }

      println("\noriginal Hints:")
      simpHints.pretyPrintHints()
      println("\nOptimized Hints:")
      println("!@@@@")
      optimizedHints.pretyPrintHints()
      println("@@@@!")
      println("timeout:" + GlobalParameters.get.threadTimeout)
      //GlobalParameters.get.printHints=optimizedHints

      if (optimizedHints.isEmpty) {
        //writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial") //write hints and their ID to file
      } else {
        //only write to file when optimized hint is not empty
        writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial") //write hints and their ID to file
        writeHintsWithIDToFile(PositiveHintsWithID, fileName, "positive")
        writeHintsWithIDToFile(NegativeHintsWithID, fileName, "negative")
      }
      (optimizedHints, result)
    }
  }


  def writeHintsWithIDToFile(wrappedHintList: Seq[wrappedHintWithID], fileName: String, hintType: String) {
    val distinctWrappedHintList = wrappedHintList.distinct
    val filePath = GlobalParameters.get.fileName.substring(0, GlobalParameters.get.fileName.lastIndexOf("/") + 1)
    if (hintType == "initial") {
      val writer = new PrintWriter(new File(filePath + fileName + ".initialHints")) //python path
      for (wrappedHint <- wrappedHintList) {
        writer.write(wrappedHint.ID.toString + ":" + wrappedHint.head + ":" + wrappedHint.hint + "\n")
      }
      writer.close()
    }
    if (hintType == "positive") {
      val writer = new PrintWriter(new File(filePath + fileName + ".positiveHints")) //python path
      for (wrappedHint <- wrappedHintList) {
        writer.write(wrappedHint.ID.toString + ":" + wrappedHint.head + ":" + wrappedHint.hint + "\n")
      }
      writer.close()
    }
    if (hintType == "negative") {
      val writer = new PrintWriter(new File(filePath + fileName + ".negativeHints")) //python path
      for (wrappedHint <- wrappedHintList) {
        writer.write(wrappedHint.ID.toString + ":" + wrappedHint.head + ":" + wrappedHint.hint + "\n")
      }
      writer.close()
    }

  }



  def readHintsFromJSON(fileName: String): VerificationHints = {

    //Read JSON
    import scala.io.Source
    import scala.util.parsing.json._
    val fname = "JSON/" + fileName + ".json"

    // Read the JSON file into json variable.
    var json: String = ""
    for (line <- Source.fromFile(fname).getLines) json += line

    // Get parse result Option object back from try/catch block.
    val option = try {
      JSON.parseFull(json)
    } catch {
      case ex: Exception => ex.printStackTrace()
    }

    // Print parsed JSON
    option match {
      case None => println("observations JSON invalid")
      case Some(elements: Map[String, Array[String]]) => {
        //println(elements)
        for ((key, list) <- elements) {
          println(key + "/" + list.length)
          for (value <- list) {
            println(" " + value)
          }

        }


      }
    }

    //JSON to Map[IExpression.Predicate, Seq[VerifHintElement]
    //VerifHintInitPred
    //VerifHintTplPred
    //VerifHintTplEqTerm
    var optimizedHints = VerificationHints(Map())
    val head = "main1"
    val arity = 1
    val h = new IExpression.Predicate(head, arity)
    val h1 = new IExpression.Predicate("main2", 2)


    val Term = "_0,10000"
    val predicate = "_3 + -1 * _4) >= 0"
    val element = VerifHintTplEqTerm(new IConstant(new ConstantTerm("sss")), 10000)
    //    val element1=VerifHintInitPred(IFomula())
    var hintList: Seq[VerifHintElement] = Seq()
    hintList = hintList ++ Seq(element)
    hintList = hintList ++ Seq(element)


    optimizedHints = optimizedHints.addPredicateHints(Map(h -> hintList))
    optimizedHints = optimizedHints.addPredicateHints(Map(h1 -> hintList))
    println("input template:")
    optimizedHints.pretyPrintHints()


    return optimizedHints
  }


  def storeHintsToVerificationHints_binary(parsedHintslist: Seq[Seq[String]], readInitialHintsWithID: Map[String, String], originalHints: VerificationHints) = {
    //store read hints to VerificationHints
    println("---selected hints--")
    var readHints = VerificationHints(Map())
    var readHintsTemp: Map[IExpression.Predicate, VerifHintElement] = Map()
    var readHintsTempList: Seq[Map[IExpression.Predicate, VerifHintElement]] = Seq()
    var parsedHintsCount = 0

    for (element <- parsedHintslist) {
      //println(element)
      if (element(3).toFloat.toInt == 1) { //element(3)==1 means useful, element(4) is score
        val head = element(1).toString
        //element(1) is head
        val hint = readInitialHintsWithID(element(0).toString + ":" + element(1)).toString //InitialHintsWithID ID:head->hint
        for ((key, value) <- originalHints.getPredicateHints()) {
          val keyTemp = key.toString().substring(0, key.toString().indexOf("/"))
          if (head == keyTemp) {
            var usfulHintsList: Seq[VerifHintElement] = Seq()
            for (oneHint <- originalHints.predicateHints(key)) {
              if (keyTemp == head && oneHint.toString() == hint) { //match initial hints and hints from file to tell usefulness
                usfulHintsList = usfulHintsList ++ Seq(oneHint) //add this hint to usfulHintsList
                //println(element(0),usfulHintsList)
                readHintsTempList = readHintsTempList :+ Map(key -> oneHint)
                parsedHintsCount = parsedHintsCount + 1
              }
            }
            //readHints=readHints.addPredicateHints(Map(key->usfulHintsList)) //add this haed->hint:Seq() to readHints
          }
        }
      } else {} //useless hint

    }

    println("selected hint count=" + parsedHintsCount)
    (readHints, readHintsTempList)

  }

  def storeHintsToVerificationHints_score(parsedHintslist: Seq[Seq[String]], readInitialHintsWithID: Map[String, String], originalHints: VerificationHints, rankTreshold: Float) = {
    //store read hints to VerificationHints
    println("---selected hints--")
    var readHints = VerificationHints(Map())
    var readHintsTemp: Map[IExpression.Predicate, VerifHintElement] = Map()
    var readHintsTempList: Seq[Map[IExpression.Predicate, VerifHintElement]] = Seq()
    var parsedHintsCount = 0

    for (element <- parsedHintslist) {
      //println(element)
      if (element(4).toFloat > rankTreshold) { //element(3)==1 means useful, element(4) is score
        val head = element(1).toString
        //element(1) is head
        val hint = readInitialHintsWithID(element(0).toString + ":" + element(1)).toString //InitialHintsWithID ID:head->hint
        for ((key, value) <- originalHints.getPredicateHints()) {
          val keyTemp = key.toString().substring(0, key.toString().indexOf("/"))
          if (head == keyTemp) {
            var usfulHintsList: Seq[VerifHintElement] = Seq()
            for (oneHint <- value) {
              if (keyTemp == head && oneHint.toString() == hint) { //match initial hints and hints from file to tell usefulness
                usfulHintsList = usfulHintsList ++ Seq(oneHint) //add this hint to usfulHintsList
                //println(element(0),usfulHintsList)
                readHintsTempList = readHintsTempList :+ Map(key -> oneHint)
                parsedHintsCount = parsedHintsCount + 1
              }
            }
            //readHints=readHints.addPredicateHints(Map(key->usfulHintsList)) //add this haed->hint:Seq() to readHints
          }
        }
      } else {} //useless hint

    }

    println("selected hint count=" + parsedHintsCount)
    (readHints, readHintsTempList)

  }

  def storeHintsToVerificationHints_topN(parsedHintslist: Seq[Seq[String]], readInitialHintsWithID: Map[String, String], originalHints: VerificationHints, N: Int) = {
    //store read hints to VerificationHints
    println("---selected hints--")
    var readHints = VerificationHints(Map())
    var readHintsTemp: Map[IExpression.Predicate, VerifHintElement] = Map()
    var readHintsTempList: Seq[Map[IExpression.Predicate, VerifHintElement]] = Seq()
    var parsedHintsCount = 0
    for (element <- parsedHintslist.take(N)) {
      //take first N element
      //println(element)
      val head = element(1).toString
      //element(1) is head
      val hint = readInitialHintsWithID(element(0).toString + ":" + element(1)).toString //InitialHintsWithID ID:head->hint
      for ((key, value) <- originalHints.getPredicateHints()) {
        val keyTemp = key.toString().substring(0, key.toString().indexOf("/"))
        if (head == keyTemp) {
          var usfulHintsList: Seq[VerifHintElement] = Seq()
          for (oneHint <- value) {
            if (oneHint.toString() == hint) { //match initial hints and hints from file to tell usefulness
              usfulHintsList = usfulHintsList ++ Seq(oneHint) //add this hint to usfulHintsList
              //println(element(0),usfulHintsList)
              readHintsTempList = readHintsTempList :+ Map(key -> oneHint)
              parsedHintsCount = parsedHintsCount + 1
            }
          }
          //readHints=readHints.addPredicateHints(Map(key->usfulHintsList)) //add this haed->hint:Seq() to readHints
        }
      }


    }

    println("selected hint count=" + parsedHintsCount)
    (readHints, readHintsTempList)

  }

  def readHintsIDFromFile(fileName: String, originalHints: VerificationHints, rank: String = ""): VerificationHints = {
    var parsedHintslist = Seq[Seq[String]]() //store parsed hints
    val f = fileName + ".optimizedHints" //python file
    for (line <- Source.fromFile(f).getLines) {
      var parsedHints = Seq[String]() //store parsed hints
      //parse read file
      var lineTemp = line.toString
      val ID = lineTemp.substring(0, lineTemp.indexOf(":"))
      lineTemp = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length)
      val head = lineTemp.substring(0, lineTemp.indexOf(":"))
      lineTemp = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length)
      val hint = lineTemp.substring(0, lineTemp.indexOf(":"))
      lineTemp = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length)
      val usefulness = lineTemp.substring(0, lineTemp.indexOf(":")) //1=useful,0=useless
      val score = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length) //1=useful,0=useless
      parsedHints = parsedHints :+ ID :+ head :+ hint :+ usefulness :+ score //ID,head,hint,usefulness,score
      //println(parsedHints)
      parsedHintslist = parsedHintslist :+ parsedHints
    }
    println("parsed hints count=" + parsedHintslist.size)

    println("---readInitialHints-----")
    var readInitialHintsWithID: Map[String, String] = Map()
    //val fInitial = "predictedHints/"+fileNameShorter+".initialHints" //read file
    val fInitial = fileName + ".initialHints" //python file
    for (line <- Source.fromFile(fInitial).getLines) {
      var parsedHints = Seq[String]() //store parsed hints
      //parse read file
      var lineTemp = line.toString
      val ID = lineTemp.substring(0, lineTemp.indexOf(":"))
      lineTemp = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length)
      val head = lineTemp.substring(0, lineTemp.indexOf(":"))
      lineTemp = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length)
      val hint = lineTemp
      readInitialHintsWithID = readInitialHintsWithID + (ID + ":" + head -> hint)
    }
    for ((key, value) <- readInitialHintsWithID) { //print initial hints
      println(key, value)
    }
    println("readInitialHints count=" + readInitialHintsWithID.size)

    //store read hints to VerificationHints
    var readHints = VerificationHints(Map())
    var readHintsTempList: Seq[Map[IExpression.Predicate, VerifHintElement]] = Seq()
    if (rank.isEmpty) { //read rank option, no need for rank
      val (readHints_temp, readHintsTempList_temp) = storeHintsToVerificationHints_binary(parsedHintslist, readInitialHintsWithID, originalHints)
      readHints = readHints_temp
      readHintsTempList = readHintsTempList_temp
    } else { //need rank
      //parse rank information
      var lineTemp = rank.toString
      val rankThreshold = lineTemp.substring(lineTemp.indexOf(":") + 1, lineTemp.length).toFloat

      if (rankThreshold > 1) {
        //rank by top n
        println("use top " + rankThreshold.toInt + " hints")
        val (readHints_temp, readHintsTempList_temp) = storeHintsToVerificationHints_topN(parsedHintslist, readInitialHintsWithID, originalHints, rankThreshold.toInt)
        readHints = readHints_temp
        readHintsTempList = readHintsTempList_temp
      }
      if (rankThreshold < 1) {
        //rank by score
        println("use score threshold " + rankThreshold)
        val (readHints_temp, readHintsTempList_temp) = storeHintsToVerificationHints_score(parsedHintslist, readInitialHintsWithID, originalHints, rankThreshold)
        readHints = readHints_temp
        readHintsTempList = readHintsTempList_temp
      }

    }

    //store heads to set
    var heads: Set[IExpression.Predicate] = Set()
    for (value <- readHintsTempList) {
      println(value)
      val tempValue = value.toSeq
      //tempValue.to
      heads = heads + tempValue(0)._1
    }


    for (head <- heads) {
      var hintList: Seq[VerifHintElement] = Seq()
      for (value <- readHintsTempList) {
        //value=Map(head->hint)
        val tempValue = value.toSeq
        if (tempValue(0)._1 == head) {
          //println(hintList)
          hintList = hintList :+ tempValue(0)._2
        }
      }
      readHints = readHints.addPredicateHints(Map(head -> hintList))
    }

    println("----readHints-----")
    for ((key, value) <- readHints.getPredicateHints()) {
      println(key)
      for (v <- value) {
        println(v)
      }
    }

    readHints
  }

  def transformPredicateMapToVerificationHints(originalPredicates:Map[Predicate, Seq[IFormula]]):  VerificationHints ={
    VerificationHints(originalPredicates.mapValues(_.map(VerificationHints.VerifHintInitPred(_))))
  }

  def initialIDForHints(simpHints: VerificationHints): Seq[wrappedHintWithID] = {
    var counter = 0
    val wrappedHintsList = for ((head,hints) <- simpHints.getPredicateHints();oneHint <- hints) yield{
      counter = counter + 1
      wrappedHintWithID(counter, head.name, oneHint.toString)
    }
    wrappedHintsList.toSeq
  }


  def writeHornClausesToFile(file: String, simpClauses: Clauses): Unit = {
    val writer = new PrintWriter(new File(file + ".horn"))
    for (clause <- simpClauses) {
      writer.write(clause.toPrologString + "\n")
    }
    writer.close()
  }


  def writeSMTFormatToFile(simpClauses: Clauses, fileName: String): Unit = {


    //val filename = basename + ".smt2"
    println("write " + fileName + " to smt format file")
    //val out = new java.io.FileOutputStream("trainData/"+fileName+".smt2")
    val out = new java.io.FileOutputStream(fileName + ".smt2") //python path
    Console.withOut(out) {
      val clauseFors =
        for (c <- simpClauses) yield {
          val f = c.toFormula
          // eliminate remaining operators like eps
          Transform2Prenex(EquivExpander(PartialEvaluator(f)))
        }

      val allPredicates =
        HornClauses allPredicates simpClauses

      SMTLineariser("C_VC", "HORN", "unknown",
        List(), allPredicates.toSeq.sortBy(_.name),
        clauseFors)
    }
    out.close

  }


  def getArgumentInfo(argumentList: Array[(IExpression.Predicate, Int)]): ArrayBuffer[argumentInfo] = {
    var argID = 0
    var arguments: ArrayBuffer[argumentInfo] = ArrayBuffer[argumentInfo]()
    for ((arg, i) <- argumentList.zipWithIndex) {
      for ((a, j) <- (0 to arg._2 - 1).zipWithIndex) {
        arguments += new argumentInfo(argID, arg._1, a)
        argID = argID + 1
      }
    }
    arguments
  }

  def getArgumentInfoFromFile(argumentList: Array[(IExpression.Predicate, Int)]): ArrayBuffer[argumentInfo] = {
    val arguments = getArgumentInfo(argumentList)
    val argumentFileName = GlobalParameters.get.fileName + ".arguments"
    if (scala.reflect.io.File(argumentFileName).exists) {
      //read score from .argument file
      for (arg <- arguments; line <- Source.fromFile(argumentFileName).getLines) {
        val parsedLine = line.split(":")
        if (arg.head == parsedLine(1) && ("argument" + arg.index.toString) == parsedLine(2))
          arg.score = parsedLine(3).toInt
      }
    }

    arguments
  }

  def getArgumentBoundForSmt(argumentList: Array[(IExpression.Predicate, Int)], disjunctive: Boolean, simplifiedClauses: Seq[Clause], simpHints: VerificationHints
                             , predGenerator: Dag[DisjInterpolator.AndOrNode[HornPredAbs.NormClause, Unit]] => Either[Seq[(Predicate, Seq[Conjunction])], Dag[(IAtom, HornPredAbs.NormClause)]]): ArrayBuffer[argumentInfo] = {
    val counterexampleMethod =
      if (disjunctive)
        HornPredAbs.CounterexampleMethod.AllShortest
      else
        HornPredAbs.CounterexampleMethod.FirstBestShortest
    val simpPredAbs =
      new simplifiedHornPredAbsForArgumentBounds(simplifiedClauses, //HornPredAbs
        simpHints.toInitialPredicates, predGenerator,
        counterexampleMethod)
    getArgumentBound(argumentList, simpPredAbs.argumentBounds)
  }

  def getArgumentBound(argumentList: Array[(IExpression.Predicate, Int)], argumentBounds: scala.collection.mutable.Map[Predicate, Array[(String, String)]]): ArrayBuffer[argumentInfo] = {
    val arguments = getArgumentInfo(argumentList)
    for ((k, v) <- argumentBounds; arg <- arguments) if (arg.location.toString() == k.toString()) {
      arg.bound = v(arg.index)
    }
    arguments
  }

  def getArgumentOccurrenceInHints(file: String,
                                   argumentList: Array[(IExpression.Predicate, Int)],
                                   positiveHints: VerificationHints,
                                   countOccurrence: Boolean = true): ArrayBuffer[argumentInfo] ={
    val arguments = getArgumentInfo(argumentList)
    if (countOccurrence == true) {
      //get hint info list
      var positiveHintInfoList: ArrayBuffer[hintInfo] = ArrayBuffer[hintInfo]()
      for ((head, hintList) <- positiveHints.getPredicateHints()) {
        for (h <- hintList) h match {
          case VerifHintInitPred(p) => {
            positiveHintInfoList += new hintInfo(p, "VerifHintInitPred", head)
          }
          case VerifHintTplPred(p, _) => {
            positiveHintInfoList += new hintInfo(p, "VerifHintTplPred", head)
          }
          case VerifHintTplPredPosNeg(p, _) => {
            positiveHintInfoList += new hintInfo(p, "VerifHintTplPredPosNeg", head)
          }
          case VerifHintTplEqTerm(t, _) => {
            positiveHintInfoList += new hintInfo(t, "VerifHintTplEqTerm", head)
          }
          case VerifHintTplInEqTerm(t, _) => {
            positiveHintInfoList += new hintInfo(t, "VerifHintTplInEqTerm", head)
          }
          case VerifHintTplInEqTermPosNeg(t, _) => {
            positiveHintInfoList += new hintInfo(t, "VerifHintTplInEqTermPosNeg", head)
          }
          case _ => {}
        }
      }
      //go through all predicates and arguments count occurrence
      for (arg <- arguments) {
        for (hint <- positiveHintInfoList) {
          if (arg.location.equals(hint.head) && ContainsSymbol(hint.expression, IVariable(arg.index))) {
            arg.score = arg.score + 1
            arg.binaryOccurenceLabel = 1
          }
        }
      }

    }
    //normalize score
    //    val argumentIDList=for(arg<-arguments) yield arg.ID
    //    val argumentNameList=for(arg<-arguments) yield arg.location.toString()+":"+"argument"+arg.index
    //    val argumentOccurrence=for(arg<-arguments) yield arg.score
    (arguments)

  }
  def writeArgumentOccurrenceInHintsToFile(file: String,
                               argumentList: Array[(IExpression.Predicate, Int)],
                               positiveHints: VerificationHints,
                               countOccurrence: Boolean = true,writeToFile:Boolean=false): ArrayBuffer[argumentInfo]  = {
    val arguments = getArgumentOccurrenceInHints(file,argumentList,positiveHints,countOccurrence)
    if (writeToFile==true){
      println("Write arguments to file")
      val writer = new PrintWriter(new File(file + ".arguments")) //python path
      for (arg <- arguments) {
        writer.write(arg.ID + ":" + arg.location.toString() + ":" + "argument" + arg.index + ":" + arg.score + "\n")
      }
      writer.close()
    }
    arguments
  }

}

object ArchivedHintSelection {
  def oldGetMinimumPredicateSet(originalPredicates: Map[Predicate, Seq[IFormula]],simplePredicatesGeneratorClauses:Clauses,exceptionalPredGen: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>  //not generate new predicates
    Either[Seq[(Predicate, Seq[Conjunction])],
      Dag[(IAtom, HornPredAbs.NormClause)]],counterexampleMethod: HornPredAbs.CounterexampleMethod.Value): Map[Predicate, Seq[IFormula]]  = {

    //Predicate selection begin
    println("------Predicates selection begin----")
    var PositiveHintsWithID: Seq[wrappedHintWithID] = Seq()
    var NegativeHintsWithID: Seq[wrappedHintWithID] = Seq()
    var optimizedPredicate: Map[Predicate, Seq[IFormula]] = Map()
    var currentPredicate: Map[Predicate, Seq[IFormula]] = originalPredicates
    val startTimeForExtraction = System.currentTimeMillis()
    val mainTimeoutChecker = () => {
      if ((currentTimeMillis - startTimeForExtraction) > GlobalParameters.get.mainTimeout)
        throw lazabs.Main.MainTimeoutException //Main.TimeoutException
    }
    for ((head, preds) <- originalPredicates) {
      var criticalPredicatesSeq: Seq[IFormula] = Seq()
      var redundantPredicatesSeq: Seq[IFormula] = Seq()

      for (p <- preds) {
        //            println("before delete")
        //            println("head", head)
        //            println("predicates", currentPredicate(head)) //key not found
        //            //delete one predicate
        //            println("delete predicate", p)
        val currentPredicateSeq = currentPredicate(head).filter(_ != p) //delete one predicate
        currentPredicate = currentPredicate.filterKeys(_ != head) //delete original head
        currentPredicate = currentPredicate ++ Map(head -> currentPredicateSeq) //add the head with deleted predicate
        //            println("after delete")
        //            println("head", head)
        //            println("predicates", currentPredicate(head))
        //            println("currentPredicate",currentPredicate)

        //try cegar
        val predicateUsefulnessTimeoutChecker = HintsSelection.clonedTimeChecker(GlobalParameters.get.threadTimeout)
        try GlobalParameters.parameters.withValue(predicateUsefulnessTimeoutChecker) {
          println("----------------------------------- CEGAR --------------------------------------")
          new HornPredAbs(simplePredicatesGeneratorClauses,
            currentPredicate,
            exceptionalPredGen, counterexampleMethod).result
          //not timeout
          redundantPredicatesSeq = redundantPredicatesSeq ++ Seq(p)
          //add useless hint to NegativeHintsWithID   //ID:head->hint
          //                for (wrappedHint <- InitialHintsWithID) { //add useless hint to NegativeHintsWithID   //ID:head->hint
          //                  val pVerifHintInitPred="VerifHintInitPred("+p.toString+")"
          //                  if (head.name == wrappedHint.head && wrappedHint.hint == pVerifHintInitPred) {
          //                    NegativeHintsWithID =NegativeHintsWithID++Seq(wrappedHint)
          //                  }
          //                }
          mainTimeoutChecker()
        } catch {
          case lazabs.Main.TimeoutException => { //need new predicate or timeout
            criticalPredicatesSeq = criticalPredicatesSeq ++ Seq(p)
            //add deleted predicate back to curren predicate
            currentPredicate = currentPredicate.filterKeys(_ != head) //delete original head
            currentPredicate = currentPredicate ++ Map(head -> (currentPredicateSeq ++ Seq(p))) //add the head with deleted predicate
            //add useful hint to PositiveHintsWithID
            //                for(wrappedHint<-InitialHintsWithID){
            //                  val pVerifHintInitPred="VerifHintInitPred("+p.toString+")"
            //                  if(head.name.toString()==wrappedHint.head && wrappedHint.hint==pVerifHintInitPred){
            //                    PositiveHintsWithID=PositiveHintsWithID++Seq(wrappedHint)
            //                  }
            //                }
          }
          case _ => {
            throw lazabs.Main.MainTimeoutException
          }
        }
      }
      //store selected predicate
      //          if (!criticalPredicatesSeq.isEmpty) {
      //            optimizedPredicate = optimizedPredicate ++ Map(head -> criticalPredicatesSeq)
      //          }

      optimizedPredicate = optimizedPredicate ++ Map(head -> criticalPredicatesSeq)
      println("current head:", head.toString())
      println("critical predicates:", criticalPredicatesSeq.toString())
      println("redundant predicates", redundantPredicatesSeq.toString())
    }
    optimizedPredicate
  }
}

class VerificationHintsInfo(val initialHints: VerificationHints, val positiveHints: VerificationHints, val negativeHints: VerificationHints)

class ClauseInfo(val simplifiedClause: Clauses, val clausesInCounterExample: Clauses)

class hintInfo(e: IExpression, t: String, h: IExpression.Predicate) {
  val head = h
  val expression = e
  val hintType = t
}

class argumentInfo(id: Int, loc: IExpression.Predicate, ind: Int) {
  val ID = id
  val location = loc
  val index = ind
  var score = 0
  val head = location.toString()
  val headName = location.name
  var bound: Pair[String, String] = ("\"None\"", "\"None\"")
  var binaryOccurenceLabel = 0
}

class simplifiedHornPredAbsForArgumentBounds[CC <% HornClauses.ConstraintClause](iClauses: Iterable[CC],
                                                                                 initialPredicates: Map[Predicate, Seq[IFormula]],
                                                                                 predicateGenerator: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
                                                                                   Either[Seq[(Predicate, Seq[Conjunction])],
                                                                                     Dag[(IAtom, HornPredAbs.NormClause)]], counterexampleMethod: HornPredAbs.CounterexampleMethod.Value = HornPredAbs.CounterexampleMethod.FirstBestShortest) {
  val theories = {
    val coll = new TheoryCollector
    coll addTheory TypeTheory
    for (c <- iClauses)
      c collectTheories coll
    coll.theories
  }
  implicit val sf = new SymbolFactory(theories)
  val relationSymbols =
    (for (c <- iClauses.iterator;
          lit <- (Iterator single c.head) ++ c.body.iterator;
          p = lit.predicate)
      yield (p -> RelationSymbol(p))).toMap

  // make sure that arguments constants have been instantiated
  for (c <- iClauses) {
    val preds = for (lit <- c.head :: c.body.toList) yield lit.predicate
    for (p <- preds.distinct) {
      val rs = relationSymbols(p)
      for (i <- 0 until (preds count (_ == p)))
        rs arguments i
    }
  }
  // translate clauses to internal form
  val (normClauses, relationSymbolBounds) = {
    val rawNormClauses = new LinkedHashMap[NormClause, CC]

    for (c <- iClauses) {
      lazabs.GlobalParameters.get.timeoutChecker()
      rawNormClauses.put(NormClause(c, (p) => relationSymbols(p)), c)
    }

    if (lazabs.GlobalParameters.get.intervals) {
      val res = new LinkedHashMap[NormClause, CC]

      val propagator =
        new IntervalPropagator(rawNormClauses.keys.toIndexedSeq,
          sf.reducerSettings)

      for ((nc, oc) <- propagator.result)
        res.put(nc, rawNormClauses(oc))
      (res.toSeq, propagator.rsBounds)
    } else {
      val emptyBounds =
        (for (rs <- relationSymbols.valuesIterator)
          yield (rs -> Conjunction.TRUE)).toMap
      (rawNormClauses.toSeq, emptyBounds)
    }
  }
  // print argument bounds
  var argumentBounds: scala.collection.mutable.Map[Predicate, Array[Tuple2[String, String]]] = scala.collection.mutable.Map()
  for ((rs, bounds) <- relationSymbolBounds; if (rs.pred.name != "FALSE")) { //don't learn from FALSE predicate
    //println(rs.pred.name + ":")
    var argumentBoundList: Array[Tuple2[String, String]] = Array()
    if (bounds.isTrue) { //FALSE's bounds is true
      for (s <- rs.arguments(0))
        argumentBoundList :+= Tuple2("\"None\"", "\"None\"")
    } else if (bounds.isFalse) {
      for (s <- rs.arguments(0))
        argumentBoundList :+= Tuple2("\"False\"", "\"False\"")
    } else {
      for (s <- rs.arguments(0)) {
        //print("  " + s + ": ")
        val lc = ap.terfor.linearcombination.LinearCombination(s, bounds.order)
        val lowerBound = PresburgerTools.lowerBound(lc, bounds) match {
          case Some(x) => x.toString()
          case _ => "\"None\""
        }
        //print(", ")
        val upperBound = (for (b <- PresburgerTools.lowerBound(-lc, bounds)) yield -b) match {
          case Some(x) => x.toString()
          case _ => "\"None\""
        }
        argumentBoundList :+= Tuple2(lowerBound, upperBound)
        //println()
      }
    }
    argumentBounds(rs.pred) = argumentBoundList
  }
}