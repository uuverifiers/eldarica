/**
 * Copyright (c) 2011-2022 Hossein Hojjat, Filip Konecny, Philipp Ruemmer,
 * Pavle Subotic. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
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

package lazabs
import ap.util.{Debug, Timeout}
import lazabs.art.SearchMethod._
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType
import lazabs.horn.concurrency.DrawHornGraph.HornGraphType
import lazabs.horn.concurrency.HintsSelection.getFileName
import lazabs.horn.concurrency.{CCReader, HintsSelection}
import lazabs.nts._
import lazabs.prover._
import lazabs.viewer._

import java.io.{FileInputStream, InputStream}

object GlobalParameters {
  object InputFormat extends Enumeration {
    val //Scala,
        Nts,
        Prolog, SMTHorn, //UppaalOG, UppaalRG, UppaalRelational, Bip,
        ConcurrentC, AutoDetect = Value
  }

  object Portfolio extends Enumeration {
    val None, Template, General = Value
  }

  val parameters =
    new scala.util.DynamicVariable[GlobalParameters] (new GlobalParameters)

  def get : GlobalParameters = parameters.value

  def withValue[A](p : GlobalParameters)(comp : => A) : A =
    parameters.withValue(p)(comp)
}

class GlobalParameters extends Cloneable {
  //var printHints=VerificationHints(Map())
  var argumentOccurenceLabel=false
  var argumentBoundLabel=false
  var getLabelFromCounterExample=false
  var unionOption=false
  var readTrueLabel=false
  var separateMultiplePredicatesInBody=false
  var withoutGraphJSON=false
  var checkSolvability=false
  var readCost=false
  var rdm=false
  var onlyInitialPredicates=false
  var generateSimplePredicates=false
  var generateTemplates=false
  var moveFile = false
  var maxNode=1000000
  var threadTimeout = 60*60*1000
  var solvabilityTimeout=60*60*1000
  var mainTimeout=60*60*1000
  var extractTemplates=false
  var extractPredicates=false
  var separateByPredicates=false
  var separateByPredicatesBatchSize=200
  var measurePredictedPredicates=false
  var singleMeasurement=false
  var labelSimpleGeneratedPredicates=false
  var varyGeneratedPredicates=false
  var readHints=false
  var readTemplates=false
  var rank=0.0
  var getSMT2=false
  var readSMT2=false
  var getSolvingTime=false
  var getHornGraph=false
  var getAllHornGraph=false
  var hornGraphType:HornGraphType.Value=HornGraphType.hyperEdgeGraph
  var in: InputStream = null
  var fileName = ""
  var funcName = "main"
  var solFileName = ""
  var timeout:Option[Int] = None
  var spuriousness = true
  var searchMethod = DFS
  var drawRTree = false
  //var drawCFG = false
  var absInFile = false
  var lbe = false
  var slicing = true
  var intervals = true
  var prettyPrint = false
  var smtPrettyPrint = false
  var graphPrettyPrint = false
//  var interpolation = false
  var ntsPrint = false
  var printIntermediateClauseSets = false
  var horn = false
  var concurrentC = false
  var global = false
  var disjunctive = false
  var splitClauses : Int = 1
  var displaySolutionProlog = false
  var displaySolutionSMT = false
  var format = GlobalParameters.InputFormat.AutoDetect
  var didIncompleteTransformation = false
  var templateBasedInterpolation = true
  var templateBasedInterpolationType : AbstractionType.Value =
    AbstractionType.RelationalEqs
  var templateBasedInterpolationTimeout = 2000
  var portfolio = GlobalParameters.Portfolio.None
  var templateBasedInterpolationPrint = false
  var cegarHintsFile : String = ""
  var cegarPostHintsFile : String = ""
  var predicateOutputFile : String = ""
  var finiteDomainPredBound : Int = 0
  var arithmeticMode : CCReader.ArithmeticMode.Value =
    CCReader.ArithmeticMode.Mathematical
  var arrayRemoval = false
  var arrayQuantification : Option[Int] = None
  var expandADTArguments = true
  var princess = false
  var staticAccelerate = false
  var dynamicAccelerate = false
  var underApproximate = false
  var template = false
  var dumpInterpolationQuery = false
  var babarew = false
  var log = false
  var debugLog= false
  var logCEX = false
  var logStat = false
  var printHornSimplified = false
  var printHornSimplifiedSMT = false
  var dotSpec = false
  var dotFile : String = null
  var pngNo = true;
  var eogCEX = false;
  var plainCEX = false;
  var simplifiedCEX = false;
  var cexInSMT = false;
  var assertions = false
  var verifyInterpolants = false
  var minePredicates = false
  var mineCounterexamples = false
  var boundsAnalysis = false
  var boundsAnalysisTO = 5000
  var visualizeLowerBound = false
  var timeoutChecker : () => Unit = () => ()

  def needFullSolution = assertions || displaySolutionProlog || displaySolutionSMT
  def needFullCEX = assertions || plainCEX || !pngNo

  def setLogLevel(level : Int) : Unit = level match {
    case x if x <= 0 => { // no logging
      log = false
      logStat = false
      logCEX = false
    }
    case 1 => { // statistics only
      log = false
      logStat = true
      logCEX = false
    }
    case 2 => { // full logging
      log = true
      logStat = true
      logCEX = false
    }
    case x if x >= 3 => { // full logging + detailed counterexamples
      log = true
      logStat = true
      logCEX = true
    }
  }

  protected def copyTo(that : GlobalParameters) = {
    that.in = this.in
    that.fileName = this.fileName
    that.funcName = this.funcName
    that.solFileName = this.solFileName
    that.timeout = this.timeout
    that.spuriousness = this.spuriousness
    that.searchMethod = this.searchMethod
    that.drawRTree = this.drawRTree
    that.absInFile = this.absInFile
    that.lbe = this.lbe
    that.slicing = this.slicing
    that.intervals = this.intervals
    that.prettyPrint = this.prettyPrint
    that.smtPrettyPrint = this.smtPrettyPrint
    that. graphPrettyPrint = this.graphPrettyPrint
    that.ntsPrint = this.ntsPrint
    that.printIntermediateClauseSets = this.printIntermediateClauseSets
    that.horn = this.horn
    that.concurrentC = this.concurrentC
    that.global = this.global
    that.disjunctive = this.disjunctive
    that.splitClauses = this.splitClauses
    that.displaySolutionProlog = this.displaySolutionProlog
    that.displaySolutionSMT = this.displaySolutionSMT
    that.format = this.format
    that.didIncompleteTransformation = this.didIncompleteTransformation
    that.templateBasedInterpolation = this.templateBasedInterpolation
    that.templateBasedInterpolationType = this.templateBasedInterpolationType
    that.templateBasedInterpolationTimeout = this.templateBasedInterpolationTimeout
    that.portfolio = this.portfolio
    that.templateBasedInterpolationPrint = this.templateBasedInterpolationPrint
    that.cegarHintsFile = this.cegarHintsFile
    that.cegarPostHintsFile = this.cegarPostHintsFile
    that.predicateOutputFile = this.predicateOutputFile
    that.finiteDomainPredBound = this.finiteDomainPredBound
    that.arithmeticMode = this.arithmeticMode
    that.arrayRemoval = this.arrayRemoval
    that.expandADTArguments = this.expandADTArguments
    that.princess = this.princess
    that.staticAccelerate = this.staticAccelerate
    that.dynamicAccelerate = this.dynamicAccelerate
    that.underApproximate = this.underApproximate
    that.template = this.template
    that.dumpInterpolationQuery = this.dumpInterpolationQuery
    that.babarew = this.babarew
    that.debugLog=this.debugLog
    that.log = this.log
    that.logCEX = this.logCEX
    that.logStat = this.logStat
    that.printHornSimplified = this.printHornSimplified
    that.printHornSimplifiedSMT = this.printHornSimplifiedSMT
    that.dotSpec = this.dotSpec
    that.dotFile = this.dotFile
    that.pngNo = this.pngNo
    that.eogCEX = this.eogCEX
    that.plainCEX = this.plainCEX
    that.cexInSMT = this.cexInSMT
    that.simplifiedCEX = this.simplifiedCEX
    that.assertions = this.assertions
    that.verifyInterpolants = this.verifyInterpolants
    that.timeoutChecker = this.timeoutChecker
    that.threadTimeout = this.threadTimeout
    that.maxNode = this.maxNode
    that.solvabilityTimeout=this.solvabilityTimeout
    that.mainTimeout=this.mainTimeout
    that.rank = this.rank
    //that.printHints = this.printHints
    that.extractTemplates=this.extractTemplates
    that.extractPredicates=this.extractPredicates
    that.separateByPredicates=this.separateByPredicates
    that.separateByPredicatesBatchSize=this.separateByPredicatesBatchSize
    that.measurePredictedPredicates=this.measurePredictedPredicates
    that.singleMeasurement=this.singleMeasurement
    that.labelSimpleGeneratedPredicates=this.labelSimpleGeneratedPredicates
    that.varyGeneratedPredicates=this.varyGeneratedPredicates
    that.readHints=this.readHints
    that.readTemplates=this.readTemplates
    that.getSMT2=this.getSMT2
    that.readSMT2=this.readSMT2
    that.getSolvingTime=this.getSolvingTime
    that.getHornGraph=this.getHornGraph
    that.getAllHornGraph=this.getAllHornGraph
    that.getLabelFromCounterExample=this.getLabelFromCounterExample
    that.unionOption=this.unionOption
    that.argumentOccurenceLabel=this.argumentOccurenceLabel
    that.argumentBoundLabel=this.argumentBoundLabel
    that.generateSimplePredicates=this.generateSimplePredicates
    that.generateTemplates=this.generateTemplates
    that.onlyInitialPredicates=this.onlyInitialPredicates
    that.checkSolvability=this.checkSolvability
    that.withoutGraphJSON=this.withoutGraphJSON
    that.separateMultiplePredicatesInBody=this.separateMultiplePredicatesInBody
    that.readTrueLabel=this.readTrueLabel
    that.readCost=this.readCost
    that.rdm=this.rdm
    that.moveFile = this.moveFile
    that.minePredicates = this.minePredicates
    that.mineCounterexamples = this.mineCounterexamples
    that.boundsAnalysis = this.boundsAnalysis
    that.boundsAnalysisTO = this.boundsAnalysisTO
    that.visualizeLowerBound = this.visualizeLowerBound

  }

  override def clone : GlobalParameters = {
    val res = new GlobalParameters
    this copyTo res
    res
  }

  def withAndWOTemplates : Seq[GlobalParameters] =
    List({
           val p = this.clone
           p.templateBasedInterpolation = false
           p
         },
         this.clone)

  def generalPortfolioParams : Seq[GlobalParameters] =
    List({
           val p = this.clone
           p.splitClauses = 0
           p.templateBasedInterpolation = false
           p
         },
         this.clone)

  def setupApUtilDebug = {
    val vi = verifyInterpolants
    val as = assertions
    Debug.enabledAssertions.value_= {
      case (_, Debug.AC_INTERPOLATION_IMPLICATION_CHECKS) => vi
      case _ => as
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

object Main {
  def assertions = GlobalParameters.get.assertions

  class MainException(msg : String) extends Exception(msg)
  object TimeoutException extends MainException("timeout")
  object MainTimeoutException extends MainException("mainTimeOut")
  object StoppedException extends MainException("stopped")
  object PrintingFinishedException extends Exception

  def openInputFile {
    val params = GlobalParameters.parameters.value
    import params._
    in = new FileInputStream(fileName)
  }
/*
  def checkInputFile {
    val params = GlobalParameters.parameters.value
    import params._
    if (in == null)
      throw new MainException("Input file missing")
  }
*/
  /*
  def getASTree = {
    val params = GlobalParameters.parameters.value
    import params._
    val lexer = new Lexer(in)
    val parser = new Parser(lexer)
    val tree = parser.parse()
    if(!(tree.value.isInstanceOf[lazabs.ast.ASTree.Sobject]))
      throw new MainException("The input file is invalid")
    //val spa = PointerAnalysis(tree.value.asInstanceOf[lazabs.ast.ASTree.Sobject])
    val so = inline(spa)
    val typ = lazabs.types.TypeCheck(so)
    typ
  }*/

  def main(args: Array[String]) : Unit = doMain(args, false)

  //def main(args: Array[String]) : Unit = lazabs.horn.FatTest(args(0))


  val greeting =
    "Eldarica v2.0.8.\n(C) Copyright 2012-2022 Hossein Hojjat and Philipp Ruemmer"

  def doMain(args: Array[String],
             stoppingCond : => Boolean) : Unit = try {
    val params = new GlobalParameters
    GlobalParameters.parameters.value = params

    // work-around: make the Princess wrapper thread-safe
    lazabs.prover.PrincessWrapper.newWrapper

    import GlobalParameters.InputFormat
    import params._

    def arguments(args: List[String]): Boolean = args match {
      case Nil => true
      //case "-c" :: rest => drawCFG = true; arguments(rest)
      //case "-r" :: rest => drawRTree = true; arguments(rest)
      case "-f" :: rest => absInFile = true; arguments(rest)
      case "-p" :: rest => prettyPrint = true; arguments(rest)
      case "-extractTemplates" :: rest => extractTemplates = true; arguments(rest)
      case "-extractPredicates" :: rest => extractPredicates = true; arguments(rest)
      case "-measurePredictedPredicates" :: rest=> measurePredictedPredicates=true; arguments(rest)
      case "-singleMeasurement" :: rest=> singleMeasurement=true; arguments(rest)
      case "-labelSimpleGeneratedPredicates"::rest => labelSimpleGeneratedPredicates = true; arguments(rest)
      case "-varyGeneratedPredicates":: rest => varyGeneratedPredicates =true; arguments(rest)
      case "-generateSimplePredicates" :: rest => generateSimplePredicates = true; arguments(rest)
      case "-generateTemplates" :: rest => generateTemplates = true; arguments(rest)
      case "-onlyInitialPredicates" :: rest => onlyInitialPredicates = true; arguments(rest)
      case "-moveFile" :: rest => moveFile = true; arguments(rest)
      case "-checkSolvability" :: rest => checkSolvability = true; arguments(rest)
      case "-withoutGraphJSON" :: rest => withoutGraphJSON = true; arguments(rest)
      case "-separateMultiplePredicatesInBody" :: rest => separateMultiplePredicatesInBody = true; arguments(rest)
      case "-readTrueLabel" :: rest => readTrueLabel = true; arguments(rest)
      case "-readCost" :: rest => readCost = true; arguments(rest)
      case "-rdm" :: rest => rdm = true; arguments(rest)
      case "-readHints" :: rest => readHints = true; arguments(rest)
      case "-readTemplates" :: rest => readTemplates = true; arguments(rest)
      case "-getSMT2" :: rest => getSMT2 = true; arguments(rest)
      case "-readSMT2" :: rest => readSMT2 = true; arguments(rest)
      case "-getSolvingTime" :: rest => getSolvingTime = true; arguments(rest)
      case "-debugLog" :: rest => debugLog = true; arguments(rest)
      case "-getLabelFromCounterExample":: rest =>getLabelFromCounterExample = true; arguments(rest)
      case "-getLabelFromCounterExample:union":: rest =>{getLabelFromCounterExample = true; unionOption = true; arguments(rest)}
      case "-argumentOccurenceLabel":: rest =>argumentOccurenceLabel = true; arguments(rest)
      case "-argumentBoundLabel":: rest =>argumentBoundLabel = true; arguments(rest)
      case "-getHornGraph" :: rest => {
        getHornGraph = true
        getAllHornGraph = true
        arguments(rest)
      }
      case "-getHornGraph:monoDirectionLayerGraph" :: rest => {
        getHornGraph = true
        hornGraphType = HornGraphType.monoDirectionLayerGraph
        arguments(rest)
      }
      case "-getHornGraph:biDirectionLayerGraph" :: rest => {
        getHornGraph = true
        hornGraphType = HornGraphType.biDirectionLayerGraph
        arguments(rest)
      }
      case "-getHornGraph:hybridDirectionLayerGraph" :: rest => {
        getHornGraph = true
        hornGraphType = HornGraphType.hybridDirectionLayerGraph
        arguments(rest)
      }
      case "-getHornGraph:clauseRelatedTaskLayerGraph" :: rest => {
        getHornGraph = true
        hornGraphType = HornGraphType.clauseRelatedTaskLayerGraph
        arguments(rest)
      }
      case "-getHornGraph:fineGrainedEdgeTypeLayerGraph" :: rest => {
        getHornGraph = true
        hornGraphType = HornGraphType.fineGrainedEdgeTypeLayerGraph
        arguments(rest)
      }
      case "-getHornGraph:hyperEdgeGraph" :: rest => {
        getHornGraph = true
        hornGraphType = HornGraphType.hyperEdgeGraph
        arguments(rest)
      }
      case "-getHornGraph:equivalentHyperedgeGraph" :: rest => {
        getHornGraph = true
        hornGraphType = HornGraphType.equivalentHyperedgeGraph
        arguments(rest)
      }
      case "-getHornGraph:concretizedHyperedgeGraph" :: rest => {
        getHornGraph = true
        hornGraphType = HornGraphType.concretizedHyperedgeGraph
        arguments(rest)
      }
      case "-pIntermediate" :: rest => printIntermediateClauseSets = true; arguments(rest)
      case "-sp" :: rest => smtPrettyPrint = true; arguments(rest)
      case "-gp" :: rest => graphPrettyPrint = true; arguments(rest)
//      case "-pnts" :: rest => ntsPrint = true; arguments(rest)
      case "-horn" :: rest => horn = true; arguments(rest)
      case "-glb" :: rest => global = true; arguments(rest)
      case "-disj" :: rest => disjunctive = true; arguments(rest)
      case "-sol" :: rest => displaySolutionProlog = true; arguments(rest)
      case "-ssol" :: rest => displaySolutionSMT = true; arguments(rest)

      case "-ints" :: rest => format = InputFormat.Nts; arguments(rest)
      case "-conc" :: rest => format = InputFormat.ConcurrentC; arguments(rest)
      case "-hin" :: rest => format = InputFormat.Prolog; arguments(rest)
      case "-hsmt" :: rest => format = InputFormat.SMTHorn; arguments(rest)
//      case "-uppog" :: rest => format = InputFormat.UppaalOG; arguments(rest)
//      case "-upprg" :: rest => format = InputFormat.UppaalRG; arguments(rest)
//      case "-upprel" :: rest => format = InputFormat.UppaalRelational; arguments(rest)
//      case "-bip" :: rest =>  format = InputFormat.Bip; arguments(rest)

      case "-abstract" :: rest => templateBasedInterpolation = true; arguments(rest)
      case "-abstractPO" :: rest => {
        portfolio = GlobalParameters.Portfolio.Template
        arguments(rest)
      }
      case "-abstract:empty" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.Empty
        arguments(rest)
      }
      case "-abstract:all" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.All
        arguments(rest)}
      case "-abstract:unlabeled" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.Unlabeled
        arguments(rest)}
      case "-abstract:labeled" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.Labeled
        arguments(rest)}
      case "-abstract:predictedCG" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.PredictedCG
        arguments(rest)}
      case "-abstract:predictedCDHG" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.PredictedCDHG
        arguments(rest)}
      case "-abstract:mined" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.Mined
        arguments(rest)}
      case "-abstract:random" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.Random
        arguments(rest)}
      case "-portfolio" :: rest => {
        portfolio = GlobalParameters.Portfolio.General
        arguments(rest)
      }
      case "-abstract:manual" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.Empty
        arguments(rest)
      }
      case "-abstract:term" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.Term
        arguments(rest)
      }
      case "-abstract:oct" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.Octagon
        arguments(rest)
      }
      case "-abstract:relEqs" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.RelationalEqs
        arguments(rest)
      }
      case "-abstract:relIneqs" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.RelationalIneqs
        arguments(rest)
      }
      case "-abstract:learnedTerm" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.LearnedTerm
        arguments(rest)
      }
      case "-abstract:off" :: rest => {
        templateBasedInterpolation = false
        arguments(rest)
      }
      case tTimeout :: rest if (tTimeout.startsWith("-abstractTO:")) =>
        templateBasedInterpolationTimeout =
          (java.lang.Float.parseFloat(tTimeout.drop(12)) * 1000).toInt;
        arguments(rest)
      case _threadTimeout :: rest if (_threadTimeout.startsWith("-absTimeout:")) =>
        threadTimeout =
          (java.lang.Float.parseFloat(_threadTimeout.drop("-absTimeout:".length)) *1000).toInt;
        arguments(rest)
      case _maxNode :: rest if (_maxNode.startsWith("-maxNode:")) =>
        maxNode = java.lang.Integer.parseInt(_maxNode.drop("-maxNode:".length));
        arguments(rest)
      case _separateByPredicates :: rest if (_separateByPredicates.startsWith("-separateByPredicates:")) => {
        separateByPredicates = true;
        separateByPredicatesBatchSize = java.lang.Integer.parseInt(_separateByPredicates.drop("-separateByPredicates:".length))
        arguments(rest)}
      case _solvabilityTimeout :: rest if (_solvabilityTimeout.startsWith("-solvabilityTimeout:")) =>
        solvabilityTimeout =
          (java.lang.Float.parseFloat(_solvabilityTimeout.drop("-solvabilityTimeout:".length))*1000 ).toInt;
        arguments(rest)
      case _mainTimeout :: rest if (_mainTimeout.startsWith("-mainTimeout:")) =>
        mainTimeout =
          (java.lang.Float.parseFloat(_mainTimeout.drop("-mainTimeout:".length)) *1000).toInt;
        arguments(rest)
      case _rank :: rest if (_rank.startsWith("-rank:")) =>
        rank =
          (java.lang.Float.parseFloat(_rank.drop(6))); //parse input string
        arguments(rest)

      case tFile :: rest if (tFile.startsWith("-hints:")) => {
        cegarHintsFile = tFile drop 7
        arguments(rest)
      }
      case tFile :: rest if (tFile.startsWith("-postHints:")) => {
        cegarPostHintsFile = tFile drop 11
        arguments(rest)
      }

      case tFile :: rest if (tFile.startsWith("-pPredicates:")) => {
        predicateOutputFile = tFile drop 13
        arguments(rest)
      }

      case "-pHints" :: rest => templateBasedInterpolationPrint = true; arguments(rest)

      case "-minePredicates" :: rest => minePredicates = true; arguments(rest)

      case "-mineCounterexamples" :: rest => mineCounterexamples = true; arguments(rest)

      case "-boundsAnalysis" :: rest => boundsAnalysis = true; arguments(rest)

      case "-visualizeLowerBound" :: rest => visualizeLowerBound = true; arguments(rest)

      case tTimeout :: rest if (tTimeout.startsWith("-boundsAnalysisTO:")) =>
        boundsAnalysisTO =
          (java.lang.Float.parseFloat(tTimeout.drop(18)) * 1000).toInt;
        arguments(rest)

      case splitMode :: rest if (splitMode startsWith "-splitClauses:") => {
        splitClauses = splitMode.drop(14).toInt
        arguments(rest)
      }


      case arithMode :: rest if (arithMode startsWith "-arithMode:") => {
        arithmeticMode = arithMode match {
          case "-arithMode:math"  => CCReader.ArithmeticMode.Mathematical
          case "-arithMode:ilp32" => CCReader.ArithmeticMode.ILP32
          case "-arithMode:lp64"  => CCReader.ArithmeticMode.LP64
          case "-arithMode:llp64" => CCReader.ArithmeticMode.LLP64
          case _                  =>
            throw new MainException("Unrecognised mode " + arithMode)
        }
        arguments(rest)
      }

      case "-n" :: rest => spuriousness = false; arguments(rest)
//      case "-i" :: rest => interpolation = true; arguments(rest)
      case "-lbe" :: rest => lbe = true; arguments(rest)

      case arrayQuans :: rest if (arrayQuans.startsWith("-arrayQuans:")) =>
        if (arrayQuans == "-arrayQuans:off")
          arrayQuantification = None
        else
          arrayQuantification = Some(arrayQuans.drop(12).toInt)
        arguments(rest)

      case "-noSlicing" :: rest => slicing = false; arguments(rest)
      case "-noIntervals" :: rest => intervals = false; arguments(rest)
      //case "-array" :: rest => arrayRemoval = true; arguments(rest)
      case "-princess" :: rest => princess = true; arguments(rest)
      case "-stac" :: rest => staticAccelerate = true; arguments(rest)
      case "-dynac" :: rest => dynamicAccelerate = true; arguments(rest)
      case "-unap" :: rest => underApproximate = true; arguments(rest)
      case "-tem" :: rest => template = true; arguments(rest)
      case "-dinq" :: rest => dumpInterpolationQuery = true; arguments(rest)
      case "-brew" :: rest => babarew = true; arguments(rest)
/*      case "-bfs" :: rest => searchMethod = BFS; arguments(rest)
      case "-prq" :: rest => searchMethod = PRQ; arguments(rest)
      case "-dfs" :: rest => searchMethod = DFS; arguments(rest)
      case "-rnd" :: rest => searchMethod = RND; arguments(rest)*/
      case tTimeout :: rest if (tTimeout.startsWith("-t:")) =>
        val time = (java.lang.Float.parseFloat(tTimeout.drop(3)) * 1000).toInt
        timeout = Some(time); arguments(rest)
      case mFuncName :: rest if (mFuncName.startsWith("-m:")) => funcName = mFuncName drop 3; arguments(rest)
      case sSolFileName :: rest if (sSolFileName.startsWith("-s:")) => solFileName = sSolFileName.drop(3); arguments(rest)
      case "-log" :: rest => setLogLevel(2); arguments(rest)
      case "-statistics" :: rest => setLogLevel(1); arguments(rest)
      case logOption :: rest if (logOption startsWith "-log:") =>
        setLogLevel((logOption drop 5).toInt); arguments(rest)
      case "-logSimplified" :: rest => printHornSimplified = true; arguments(rest)
      case "-logSimplifiedSMT" :: rest => printHornSimplifiedSMT = true; arguments(rest)
      case "-dot" :: str :: rest => dotSpec = true; dotFile = str; arguments(rest)
      case "-pngNo" :: rest => pngNo = true; arguments(rest)
      case "-dotCEX" :: rest => pngNo = false; arguments(rest)
      case "-eogCEX" :: rest => pngNo = false; eogCEX = true; arguments(rest)
      case "-cex" :: rest => plainCEX = true; arguments(rest)
      case "-scex" :: rest => plainCEX = true; cexInSMT = true; arguments(rest)
      case "-cexSimplified" :: rest => simplifiedCEX = true; arguments(rest)
      case "-assert" :: rest => GlobalParameters.get.assertions = true; arguments(rest)
      case "-verifyInterpolants" :: rest => verifyInterpolants = true; arguments(rest)
      case "-h" :: rest => println(greeting + "\n\nUsage: eld [options] file\n\n" +
          "General options:\n" +
          " -h\t\tShow this information\n" +
          " -assert\tEnable assertions in Eldarica\n" +
          " -log\t\tDisplay progress and found invariants\n" +
          " -debugLog\t\tDisplay debug info\n" +
          " -log:n\t\tDisplay progress with verbosity n (currently 0 <= n <= 3)\n" +
          " -statistics\tDisplay statistics (implied by -log)\n" +
          " -t:time\tSet timeout (in seconds)\n" +
          " -cex\t\tShow textual counterexamples\n" + 
          " -scex\t\tShow textual counterexamples in SMT-LIB format\n" + 
          " -dotCEX\tOutput counterexample in dot format\n" + 
          " -eogCEX\tDisplay counterexample using eog\n" + 
          " -m:func\tUse function func as entry point (default: main)\n" +
          "\n" +
          "Horn engine:\n" +
          " -horn\t\tEnable this engine\n" +
          " -p\t\tPretty Print Horn clauses\n" +
          " -sp\t\tPretty print the Horn clauses in SMT-LIB format\n" +
          " -sol\t\tShow solution in Prolog format\n" +
          " -ssol\t\tShow solution in SMT-LIB format\n" +
          " -disj\t\tUse disjunctive interpolation\n" +
          " -stac\t\tStatic acceleration of loops\n" +
          " -lbe\t\tDisable preprocessor (e.g., clause inlining)\n" +
          " -arrayQuans:n\tIntroduce n quantifiers for each array argument (default: off)\n" +
          " -noSlicing\tDisable slicing of clauses\n" +
          " -noIntervals\tDisable interval analysis\n" +
          " -hints:f\tRead hints (initial predicates and abstraction templates) from a file\n" +
          " -postHints:f\tRead hints for processed clauses from a file\n" +
          " -pHints\tPrint initial predicates and abstraction templates\n" +
          " -pPredicates:f\tOutput predicates computed by CEGAR to a file\n" +
//          " -glb\t\tUse the global approach to solve Horn clauses (outdated)\n" +
	  "\n" +
//          " -abstract\tUse interpolation abstraction for better interpolants (default)\n" +
          " -abstract:t\tInterp. abstraction: off, manual, term, oct,\n" +
          "            \t                     relEqs (default), relIneqs\n" +
          " -abstractTO:t\tTimeout (s) for abstraction search (default: 2.0)\n" +
          " -abstractPO\tRun with and w/o interpolation abstraction in parallel\n" +

          " -portfolio\tRun different standard configurations in parallel\n" +
          " -splitClauses:n\tAggressiveness when splitting disjunctions in clauses\n" +
          "                \t                     (0 <= n <= 2, default: 1)\n" +
          "\n" +
          " -hin\t\tExpect input in Prolog Horn format\n" +
          " -hsmt\t\tExpect input in Horn SMT-LIB format\n" +
          " -ints\t\tExpect input in integer NTS format\n" +
          " -conc\t\tExpect input in C/C++/TA format\n" +
//          " -bip\t\tExpect input in BIP format\n" +
//          " -uppog\t\tExpect UPPAAL file using Owicki-Gries encoding\n" +
//          " -upprg\t\tExpect UPPAAL file using Rely-Guarantee encoding\n" +
//          " -upprel\tExpect UPPAAL file using Relational Encoding\n"
          "\n" +
          "C/C++/TA front-end:\n" +
          " -arithMode:t\t Integer semantics: math (default), ilp32, lp64, llp64\n" +
          " -pIntermediate\t Dump Horn clauses encoding concurrent programs\n"+
          " -extractTemplates\t extract templates training data\n"+
          " -extractPredicates\t extract predicates from CEGAR process\n"+
          " -separateByPredicates\t separate horn graph by predicates\n"+
          " -measurePredictedPredicates\t output predicted predicate measurements\n"+
          " -singleMeasurement\t single measurements for current option\n"+
          " -labelSimpleGeneratedPredicates\t label simple generated predicates by selected predicates\n"+
          " -varyGeneratedPredicates\t vary generated predicates from CEGAR process without change of logic mearnings\n"+
          " -generateSimplePredicates\t generate simple predicates\n"+
          " -generateTemplates\t generate templates\n"+
          " -onlyInitialPredicates\t extract predicates using initial predicates only\n"+
          " -moveFile\t if exception occur, move file to excepion directory\n"+
          " -checkSolvability \t check solvability for different initial predicate settings\n"+
          " -withoutGraphJSON \t don't output JSON file for graph\n"+
          " -separateMultiplePredicatesInBody \t don't output JSON file for graph\n"+
          " -readTrueLabel \t read tru label\n"+
          " -readCost \t read template cost from file\n"+
          " -rdm \t random label initial templates\n"+
          " -absTimeout:time\t set timeout for labeling hints\n"+
          " -solvabilityTimeout:time\t set timeout for solvability\n"+
          " -rank:n\t use top n or score above n ranked hints read from file\n"+
          " -maxNode:n\t if the node number exceeded this number, stop drawing\n"+
          " -getSMT2\t get SMT2 file\n"+
          " -readSMT2\t read SMT2 file without preprocessing\n"+
          " -getSolvingTime\t get Solving time in JSON file\n"+
          " -getLabelFromCounterExample:option\t  Interp. union. predicate occurrence in counter example\n"+
          " -argumentOccurenceLabel\t  argument occurrence in hints\n"+
          " -argumentBoundLabel\t  get argument lower and upper bound\n"+
          " -getHornGraph\t get all types of horn graph file and GNN input\n"+
          " -getHornGraph:t\t Interp. getHornGraph: monoDirectionLayerGraph, biDirectionLayerGraph, hybridDirectionLayerGraph,clauseRelatedTaskLayerGraph, fineGrainedEdgeTypeLayerGraph, hyperEdgeGraph, equivalentHyperedgeGraph, concretizedHyperedgeGraph\n" +
          " -getLabelFromCE \t get label from counter example\n"


          )
          false
      case fn :: rest => fileName = fn;  openInputFile; arguments(rest)
    }

    // Exit early if we showed the help
    if (!arguments(args.toList))
      return

    if (in == null) {
      arguments(List("-h"))
      throw new MainException("no input file given")
      return
    }

    val startTime = System.currentTimeMillis

    timeoutChecker = timeout match {
      case Some(to) => () => {
        //println("time check point", ((System.currentTimeMillis - startTime)/1000).toString+"/"+(to/1000).toString)
        if (System.currentTimeMillis - startTime > to.toLong)
          throw TimeoutException
        if (stoppingCond)
          throw StoppedException
      }
      case None => () => {
        if (stoppingCond)
          throw StoppedException
      }
    }

    GlobalParameters.get.setupApUtilDebug

    if(princess) Prover.setProver(lazabs.prover.TheoremProver.PRINCESS)

    if (format == InputFormat.AutoDetect) {
        // try to guess the file type from the extension
        if (fileName endsWith ".horn")
          format = InputFormat.Prolog
        else if (fileName endsWith ".smt2") {
          format = InputFormat.SMTHorn
        } else if (fileName endsWith ".nts") {
          format = InputFormat.Nts
          // then also choose -horn by default
          horn = true
        }
//        else if (fileName endsWith ".scala")
//          format = InputFormat.Scala
//        else if (fileName endsWith ".bip")
//          format = InputFormat.Bip
//        else if (fileName endsWith ".xml")
//          format = InputFormat.UppaalOG
        else if ((fileName endsWith ".hcc") ||
                 (fileName endsWith ".c") ||
                 (fileName endsWith ".cc") ||
                 (fileName endsWith ".cpp")) {
          format = InputFormat.ConcurrentC
          concurrentC = true
        } else
          throw new MainException ("could not figure out the input format")
    }

    format match {
      case InputFormat.Prolog | InputFormat.SMTHorn //| InputFormat.Bip |
           //InputFormat.UppaalOG | InputFormat.UppaalRG |
           //InputFormat.UppaalRelational
      =>
        // those formats can only be handled in Horn mode
        horn = true
      case _ =>
        // nothing
    }

    if (horn) {

/*      format match {
        case InputFormat.Bip =>
          // BIP mode
//          lazabs.bip.HornBip.apply(fileName)
          return
        case InputFormat.UppaalRelational =>
          // uses iterative relational encoding to solve the system
          lazabs.upp.Relational.apply(fileName, log)
          return
        case _ =>
          // nothing
      }*/
      val (clauseSet, absMap) = try { format match {
        case InputFormat.Prolog =>
          (lazabs.horn.parser.HornReader.apply(fileName), None)
        case InputFormat.SMTHorn =>
          (lazabs.horn.parser.HornReader.fromSMT(fileName), None)
        case InputFormat.Nts =>
          (NtsHorn(NtsWrapper(fileName)), None)
/*        case InputFormat.UppaalOG =>
          lazabs.upp.OwickiGries(fileName, templateBasedInterpolation)
        case InputFormat.UppaalRG =>
          lazabs.upp.RelyGuarantee(fileName, templateBasedInterpolation)
*/
      }
      } catch {
        case t@(TimeoutException | StoppedException) => {
          println("unknown")
          return
        }
      }

      if(prettyPrint) {
        println(HornPrinter(clauseSet))

        //println(clauseSet.map(lazabs.viewer.HornPrinter.printDebug(_)).mkString("\n\n"))
        return
      }

      if(smtPrettyPrint) {
        println(HornSMTPrinter(clauseSet))
        return
      }

      if (extractPredicates) {
        try {
          lazabs.horn.concurrency.TrainDataGeneratorPredicatesSmt2(clauseSet, absMap, global, disjunctive,
            drawRTree, lbe) //generate train data.  clauseSet error may caused by import package
        } catch {
          case x:Any => {
            println(Console.RED + x.toString)
            throw MainTimeoutException
          }
        }
        return
      }
      if (extractTemplates) {
        try {
          lazabs.horn.concurrency.TrainDataGeneratorTemplatesSmt2(clauseSet, absMap, global, disjunctive,
            drawRTree, lbe) //generate train data.  clauseSet error may caused by import package
        } catch {
          case x:Any => {
            println(Console.RED + x.toString)
            throw MainTimeoutException
          }
        }
        return
      }


      if(solFileName != "") {
        val solution = lazabs.horn.parser.HornReader.apply(solFileName)
        return
      }

/*      val uppflag = format match {
        case InputFormat.UppaalOG | InputFormat.UppaalRG => true
        case _ => false
      }*/

      lazabs.horn.Solve(clauseSet, absMap, global, disjunctive,
                        drawRTree, lbe)
        
      return

    } else if (concurrentC) {

      val outStream =
        if (logStat) Console.err else lazabs.horn.bottomup.HornWrapper.NullStream

      Console.withOut(outStream) {
        println(
          "---------------------------- Reading C/C++ file --------------------------------")
      }

      val system = 
        CCReader(new java.io.BufferedReader (
                   new java.io.FileReader(new java.io.File (fileName))),
                 funcName,
                 arithmeticMode)

      if (prettyPrint)
        lazabs.horn.concurrency.ReaderMain.printClauses(system)

      val smallSystem = system.mergeLocalTransitions
      if (prettyPrint) {
        println
        println("After simplification:")
        lazabs.horn.concurrency.ReaderMain.printClauses(smallSystem)
        return
      }

//      if(extractTemplates){
//        val systemGraphs=new lazabs.horn.concurrency.TrainDataGenerator(smallSystem,system) //generate train data by templates
//        return
//      }


      val result = try {
        Console.withOut(outStream) {
          new lazabs.horn.concurrency.VerificationLoop(smallSystem).result
        }
      } catch {
        case TimeoutException => {
          println("timeout")
          throw TimeoutException
        }
        case StoppedException => {
          println("stopped")
          throw StoppedException
        }
      }

      result match {
        case Left(_) =>
          println("SAFE")
        case Right(cex) => {
          println("UNSAFE")
          if (plainCEX) {
            println
            lazabs.horn.concurrency.VerificationLoop.prettyPrint(cex)
          }
        }
      }
//      println
//      println("-----Optimized Hints------")
//      println("!@@@@")
//      printHints.pretyPrintHints()
//      println("@@@@!")
      return
    }

    val (cfg,m) = format match {
      case InputFormat.Nts =>
        val ntsc = NtsCFG(NtsWrapper(fileName),lbe,staticAccelerate)
        (ntsc,Some(Map[Int,String]().empty ++ NtsWrapper.stateNameMap))        
/*      case InputFormat.Scala =>
        checkInputFile
        val ast = getASTree
        if(prettyPrint) {println(ScalaPrinter(ast)); return}
        (MakeCFG(ast,"sc_" + funcName,arrayRemoval,staticAccelerate),None)*/
    }

    //if(drawCFG) {DrawGraph(cfg.transitions.toList,cfg.predicates,absInFile,m); return}

    if(ntsPrint) {
      println(NTSPrinter(cfg))
      return
    }

//    if(timeout.isDefined) Z3Wrapper.setTimeout(timeout)

    /*val rTree = if (!interpolation) MakeRTree(cfg, MakeCFG.getLoops, spuriousness, searchMethod, log)
      else MakeRTreeInterpol(cfg, MakeCFG.getLoops, searchMethod, babarew, dumpInterpolationQuery, dynamicAccelerate, underApproximate, template, log)*/
    //if(drawRTree) DrawGraph(rTree, absInFile)

  } catch {
    case TimeoutException | StoppedException =>{
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/time-out-exception/" + getFileName)
      printError(" timeout", GlobalParameters.get.format)
    }
    case  MainTimeoutException =>{
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/time-out-exception/" + getFileName())
      printError("main timeout", GlobalParameters.get.format)
    }
      // nothing
    case _ : java.lang.OutOfMemoryError =>{
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/out-of-memory/" + getFileName())
      printError("out of memory", GlobalParameters.get.format)
    }
    case _ : java.lang.StackOverflowError =>{
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/stack-overflow/" + getFileName())
      printError("stack overflow", GlobalParameters.get.format)
    }
    case t : Exception =>{
      printError(t.getMessage, GlobalParameters.get.format)
      t.printStackTrace()
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/other-error/" + getFileName())
    }
    case x:Any=>{
      printError("other-error", GlobalParameters.get.format)
      println(Console.RED + x.toString)
      HintsSelection.moveRenameFile(GlobalParameters.get.fileName,"../benchmarks/exceptions/other-error/" + getFileName())
    }


  }

  private def printError(message : String,
                         format : GlobalParameters.InputFormat.Value) : Unit =
    if (message == null)
      println("error")
    else
      println("(error \"" + ap.parser.SMTLineariser.escapeString(message) + "\")")
  
}
