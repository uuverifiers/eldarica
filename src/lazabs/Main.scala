/**
 * Copyright (c) 2011-2020 Hossein Hojjat, Filip Konecny, Philipp Ruemmer,
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

import java.io.{File, FileInputStream, FileNotFoundException, InputStream, PrintWriter}
import java.lang.System.currentTimeMillis

import parser._
import lazabs.art._
import lazabs.art.SearchMethod._
import lazabs.horn.global.HornClause
import lazabs.prover._
import lazabs.viewer._
import lazabs.utils.Inline._
//import lazabs.utils.PointerAnalysis
//import lazabs.cfg.MakeCFG
import lazabs.nts._
import lazabs.horn.parser.HornReader
import lazabs.horn.bottomup.HornPredAbs.RelationSymbol
import lazabs.horn.abstractions.AbsLattice
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType
import lazabs.horn.abstractions.StaticAbstractionBuilderSmtHintsSelection
import lazabs.horn.concurrency.CCReader
import lazabs.horn.abstractions.VerificationHints
import lazabs.horn.concurrency.{VerificationLoop}

import ap.util.Debug

import ap.util.Debug

object GlobalParameters {
  object InputFormat extends Enumeration {
    val //Scala,
        Nts,
        Prolog, SMTHorn, //UppaalOG, UppaalRG, UppaalRelational, Bip,
        ConcurrentC, AutoDetect = Value
  }

  val parameters =
    new scala.util.DynamicVariable[GlobalParameters] (new GlobalParameters)

  def get : GlobalParameters = parameters.value
}

class GlobalParameters extends Cloneable {
  //var printHints=VerificationHints(Map())
  var totalHints=0 //DEBUG
  var threadTimeout = 2000 //debug
  var solvabilityTimeout=2000
  var extractTemplates=false
  var extractPredicates=false
  var readHints=false
  var rank=0.0
  var getSMT2=false
  var getHornGraph=false
  var hornGraphWithHints=false
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
//  var interpolation = false
  var ntsPrint = false
  var printIntermediateClauseSets = false
  var horn = false
  var concurrentC = false
  var global = false
  var disjunctive = false
  var splitClauses = false
  var displaySolutionProlog = false
  var displaySolutionSMT = false
  var format = GlobalParameters.InputFormat.AutoDetect
  var didIncompleteTransformation = false
  var templateBasedInterpolation = true
  var templateBasedInterpolationType : AbstractionType.Value =
    AbstractionType.RelationalEqs
  var templateBasedInterpolationTimeout = 2000
  var templateBasedInterpolationPortfolio = false
  var templateBasedInterpolationPrint = false
  var cegarHintsFile : String = ""
  var cegarPostHintsFile : String = ""
  var predicateOutputFile : String = ""
  var arithmeticMode : CCReader.ArithmeticMode.Value =
    CCReader.ArithmeticMode.Mathematical
  var arrayRemoval = false
  var arrayQuantification : Option[Int] = Some(1)
  var princess = false
  var staticAccelerate = false
  var dynamicAccelerate = false
  var underApproximate = false
  var template = false
  var dumpInterpolationQuery = false
  var babarew = false
  var log = false
  var logCEX = false
  var logStat = false
  var printHornSimplified = false
  var dotSpec = false
  var dotFile : String = null
  var pngNo = true;
  var eogCEX = false;
  var plainCEX = false;
  var assertions = false
  var verifyInterpolants = false
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
    that.templateBasedInterpolationPortfolio = this.templateBasedInterpolationPortfolio
    that.templateBasedInterpolationPrint = this.templateBasedInterpolationPrint
    that.cegarHintsFile = this.cegarHintsFile
    that.cegarPostHintsFile = this.cegarPostHintsFile
    that.predicateOutputFile = this.predicateOutputFile
    that.arithmeticMode = this.arithmeticMode
    that.arrayRemoval = this.arrayRemoval
    that.princess = this.princess
    that.staticAccelerate = this.staticAccelerate
    that.dynamicAccelerate = this.dynamicAccelerate
    that.underApproximate = this.underApproximate
    that.template = this.template
    that.dumpInterpolationQuery = this.dumpInterpolationQuery
    that.babarew = this.babarew
    that.log = this.log
    that.logCEX = this.logCEX
    that.logStat = this.logStat
    that.printHornSimplified = this.printHornSimplified
    that.dotSpec = this.dotSpec
    that.dotFile = this.dotFile
    that.pngNo = this.pngNo
    that.eogCEX = this.eogCEX
    that.plainCEX = this.plainCEX
    that.assertions = this.assertions
    that.verifyInterpolants = this.verifyInterpolants
    that.timeoutChecker = this.timeoutChecker
    //DEBUG
    that.threadTimeout = this.threadTimeout //debug
    that.solvabilityTimeout=this.solvabilityTimeout
    that.rank = this.rank //debug
    //that.printHints = this.printHints //DEBUG
    that.extractTemplates=this.extractTemplates//debug
    that.extractPredicates=this.extractPredicates//debug
    that.readHints=this.readHints
    that.getSMT2=this.getSMT2
    that.getHornGraph=this.getHornGraph
    that.hornGraphWithHints=this.hornGraphWithHints
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
  object StoppedException extends MainException("stopped")

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

    "Eldarica v2.0.4.\n(C) Copyright 2012-2020 Hossein Hojjat and Philipp Ruemmer"

  def doMain(args: Array[String],
             stoppingCond : => Boolean) : Unit = try {
    val params = new GlobalParameters
    GlobalParameters.parameters.value = params

    // work-around: make the Princess wrapper thread-safe
    lazabs.prover.PrincessWrapper.newWrapper

    import params._
    import GlobalParameters.InputFormat

    def arguments(args: List[String]): Boolean = args match {
      case Nil => true
      //case "-c" :: rest => drawCFG = true; arguments(rest)
      //case "-r" :: rest => drawRTree = true; arguments(rest)
      case "-f" :: rest => absInFile = true; arguments(rest)
      case "-p" :: rest => prettyPrint = true; arguments(rest)
      case "-extractTemplates" :: rest => extractTemplates = true; arguments(rest)
      case "-extractPredicates" :: rest => extractPredicates = true; arguments(rest)
      case "-readHints" :: rest => readHints = true; arguments(rest)
      case "-getSMT2" :: rest => getSMT2 = true; arguments(rest)
      case "-getHornGraph" :: rest => getHornGraph = true; arguments(rest)
      case "-hornGraphWithHints" :: rest => hornGraphWithHints = true; arguments(rest)
      case "-pIntermediate" :: rest => printIntermediateClauseSets = true; arguments(rest)
      case "-sp" :: rest => smtPrettyPrint = true; arguments(rest)
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
      case "-abstractPO" :: rest => templateBasedInterpolationPortfolio = true; arguments(rest)
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
      case "-abstract:off" :: rest => {
        templateBasedInterpolation = false
        arguments(rest)
      }
      case tTimeout :: rest if (tTimeout.startsWith("-abstractTO:")) =>
        templateBasedInterpolationTimeout =
          (java.lang.Float.parseFloat(tTimeout.drop(12)) * 1000).toInt;
        arguments(rest)
      case tTimeout :: rest if (tTimeout.startsWith("-absTimeout:")) =>  //debug
        threadTimeout =
          (java.lang.Float.parseFloat(tTimeout.drop(12)) ).toInt;
        arguments(rest)
      case tTimeout :: rest if (tTimeout.startsWith("-solvabilityTimeout:")) =>  //debug
        solvabilityTimeout =
          (java.lang.Float.parseFloat(tTimeout.drop("-solvabilityTimeout:".length)) ).toInt;
        arguments(rest)
      case tTimeout :: rest if (tTimeout.startsWith("-rank:")) =>  //debug
        rank =
          (java.lang.Float.parseFloat(tTimeout.drop(6))); //parse input string
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

      case "-splitClauses" :: rest => splitClauses = true; arguments(rest)

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
      case "-dot" :: str :: rest => dotSpec = true; dotFile = str; arguments(rest)
      case "-pngNo" :: rest => pngNo = true; arguments(rest)
      case "-dotCEX" :: rest => pngNo = false; arguments(rest)
      case "-eogCEX" :: rest => pngNo = false; eogCEX = true; arguments(rest)
      case "-cex" :: rest => plainCEX = true; arguments(rest)
      case "-assert" :: rest => GlobalParameters.get.assertions = true; arguments(rest)
      case "-verifyInterpolants" :: rest => verifyInterpolants = true; arguments(rest)
      case "-h" :: rest => println(greeting + "\n\nUsage: eld [options] file\n\n" +
          "General options:\n" +
          " -h\t\tShow this information\n" +
          " -assert\tEnable assertions in Eldarica\n" +
          " -log\t\tDisplay progress and found invariants\n" + 
          " -log:n\t\tDisplay progress with verbosity n (currently 0 <= n <= 3)\n" + 
          " -statistics\tDisplay statistics (implied by -log)\n" + 
          " -t:time\tSet timeout (in seconds)\n" +
          " -cex\t\tShow textual counterexamples\n" + 
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
          " -arrayQuans:n\tIntroduce n quantifiers for each array argument (default: 1)\n" +
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
          " -splitClauses\tTurn clause constraints into pure inequalities\n" +
          
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
          " -arithMode:t\tInteger semantics: math (default), ilp32, lp64, llp64\n" +
          " -pIntermediate\tDump Horn clauses encoding concurrent programs\n"+
          " -extractTemplates\textract templates training data\n"+
          " -extractPredicates\textract predicates training data\n"+
          " -absTimeout:time\tset timeout for labeling hints\n"+
          " -solvabilityTimeout:time\tset timeout for solvability\n"+
          " -rank:n\tuse top n or score above n ranked hints read from file\n"+
          " -getSMT2\tget SMT2 file\n"+
          " -getHornGraph\tget horn graph file and GNN input\n"+
          " -hornGraphWithHints\tget horn graph file with hints\n"


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
      if(extractTemplates){
        //do selection
        lazabs.horn.TrainDataGeneratorSmt2(clauseSet, absMap, global, disjunctive,
          drawRTree, lbe) //generate train data


        return
      }
      if(extractPredicates){
        //do selection
        lazabs.horn.TrainDataGeneratorPredicatesSmt2(clauseSet, absMap, global, disjunctive,
          drawRTree, lbe) //generate train data.  clauseSet error may caused by import package
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

      if(extractTemplates){
        val systemGraphs=new lazabs.horn.concurrency.TrainDataGenerator(smallSystem,system) //generate train data by templates
        return
      }
      if(extractPredicates){

        val predicateGenerator=new lazabs.horn.concurrency.TrainDataGeneratorPredicate(smallSystem,system) //generate train data by predicates

        return
      }


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
    case TimeoutException | StoppedException =>
      // nothing
    case _ : java.lang.OutOfMemoryError =>
      printError("out of memory", GlobalParameters.get.format)
    case _ : java.lang.StackOverflowError =>
      printError("stack overflow", GlobalParameters.get.format)
    case t : Exception =>
      printError(t.getMessage, GlobalParameters.get.format)
  }

  private def printError(message : String,
                         format : GlobalParameters.InputFormat.Value) : Unit =
    if (message == null)
      println("error")
    else
      println("(error \"" + message.replace("\"", "\"\"\"") + "\")")
  
}
