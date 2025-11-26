/**
 * Copyright (c) 2011-2025 Hossein Hojjat, Filip Konecny, Philipp Ruemmer,
 * Pavle Subotic, Gambhir Sankalp. All rights reserved.
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

import java.io.{InputStream, FileNotFoundException, Reader, FileReader, BufferedReader, File}
import parser._
import lazabs.art._
import lazabs.art.SearchMethod._
import lazabs.prover._
import lazabs.viewer._
import lazabs.utils.Inline._
//import lazabs.utils.PointerAnalysis
//import lazabs.cfg.MakeCFG
import lazabs.nts._
import lazabs.horn.parser.HornReader
import lazabs.horn.abstractions.AbsLattice
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType

import ap.util.Debug
import ap.parameters.Param

object GlobalParameters {
  object InputFormat extends Enumeration {
    val //Scala,
        Nts,
        Prolog, SMTHorn,
        AutoDetect = Value
  }

  object Portfolio extends Enumeration {
    val None, Template, General = Value
  }

  object SymexEngine extends Enumeration {
    val BreadthFirstForward, DepthFirstForward, None = Value
  }

  object SolutionReconstruction extends Enumeration {
    val WP, CEGAR = Value
  }

  val parameters =
    new scala.util.DynamicVariable[GlobalParameters] (new GlobalParameters)

  def get : GlobalParameters = parameters.value

  def withValue[A](p : GlobalParameters)(comp : => A) : A =
    parameters.withValue(p)(comp)
}

class GlobalParameters extends Cloneable {
  var in: Reader = null
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
  var symexEngine = GlobalParameters.SymexEngine.None
  var symexMaxDepth : Option[Int] = None
  var global = false
  var disjunctive = false
  var splitClauses : Int = 1
  var displaySolutionProlog = false
  var displaySolutionSMT = false
  var solutionReconstruction = GlobalParameters.SolutionReconstruction.CEGAR
  var format = GlobalParameters.InputFormat.AutoDetect
  var didIncompleteTransformation = false
  var templateBasedInterpolation = true
  var templateBasedInterpolationType : AbstractionType.Value =
    AbstractionType.RelationalEqs2
  var templateBasedInterpolationTimeout = 2000
  var portfolio = GlobalParameters.Portfolio.None
  var templateBasedInterpolationPrint = false
  var cegarHintsFile : String = ""
  var cegarPostHintsFile : String = ""
  var predicateOutputFile : String = ""
  var finiteDomainPredBound : Int = 0
  var arrayRemoval = false
  var arrayQuantification : Option[Int] = None
  var arrayCloning : Boolean = false
  var expandADTArguments = true
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
  var logPredicates : Set[String] = Set()
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
  var verifySolCEX = false
  var verifyInterpolants = false
  var niaFairSplitting = false // refers to ap.parameters.Param.NonLinearSplitting
  var heapTheory : Param.HeapTheory.Value = Param.HeapTheory.Native
  var minePredicates = false
  var timeoutChecker : () => Unit = () => ()

  def needFullSolution =
    assertions || displaySolutionProlog || displaySolutionSMT || verifySolCEX
  def needFullCEX =
    assertions || plainCEX || !pngNo || verifySolCEX

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
    that.global = this.global
    that.symexEngine = this.symexEngine
    that.disjunctive = this.disjunctive
    that.splitClauses = this.splitClauses
    that.displaySolutionProlog = this.displaySolutionProlog
    that.displaySolutionSMT = this.displaySolutionSMT
    that.solutionReconstruction = this.solutionReconstruction
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
    that.arrayRemoval = this.arrayRemoval
    that.expandADTArguments = this.expandADTArguments
    that.arrayCloning = this.arrayCloning
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
    that.printHornSimplifiedSMT = this.printHornSimplifiedSMT
    that.dotSpec = this.dotSpec
    that.dotFile = this.dotFile
    that.pngNo = this.pngNo
    that.eogCEX = this.eogCEX
    that.plainCEX = this.plainCEX
    that.cexInSMT = this.cexInSMT
    that.simplifiedCEX = this.simplifiedCEX
    that.assertions = this.assertions
    that.verifySolCEX = this.verifySolCEX
    that.verifyInterpolants = this.verifyInterpolants
    that.timeoutChecker = this.timeoutChecker
    that.heapTheory = this.heapTheory
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

  def stdSymexParams : GlobalParameters = {
    val p = this.clone
    p.symexEngine = GlobalParameters.SymexEngine.BreadthFirstForward
    p
  }

  def generalPortfolioParams : Seq[GlobalParameters] =
    List({
           val p = this.clone
           p.splitClauses = 0
           p.templateBasedInterpolation = false
           p
         },
         {
           val p = this.clone
           p.staticAccelerate = true
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
 
  def openInputFile {
    in = Main.getFileStream(fileName)
  }
 
  def setInputToSTDIN {
    format match {
      case GlobalParameters.InputFormat.AutoDetect |
           GlobalParameters.InputFormat.SMTHorn => {
        format = GlobalParameters.InputFormat.SMTHorn
        in = new ap.parser.SMTParsingUtils.SMTCommandTerminator(Console.in)
      }
      case _ => {
        in = Console.in
      }
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

object Main {
  def assertions = GlobalParameters.get.assertions

  class MainException(msg : String) extends Exception(msg)
  object TimeoutException extends MainException("timeout")
  object StoppedException extends MainException("stopped")
  case class FileOrOptionNotFoundException(fileName: String) extends MainException(s"No such file or option: $fileName . Use -h for usage information")
  object PrintingFinishedException extends Exception

  def getFileStream(fileName : String) : Reader = {
    try {
      new BufferedReader(new FileReader(new File(fileName)))
    } catch {
      case _: FileNotFoundException => throw FileOrOptionNotFoundException(fileName)
      case e: Throwable => throw e
    }
  }

  def main(args: Array[String]) : Unit = doMain(args, false)

  //def main(args: Array[String]) : Unit = lazabs.horn.FatTest(args(0))
  

  val greeting =
    "Eldarica v2.2.1\n(C) Copyright 2012-2025 Hossein Hojjat and Philipp Ruemmer"

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
      case "-pIntermediate" :: rest => printIntermediateClauseSets = true; arguments(rest)
      case "-sp" :: rest => smtPrettyPrint = true; arguments(rest)
//      case "-pnts" :: rest => ntsPrint = true; arguments(rest)
      case "-horn" :: rest => horn = true; arguments(rest)
      case "-sym" :: rest =>
        symexEngine = GlobalParameters.SymexEngine.BreadthFirstForward
        arguments(rest)
      case symexOpt :: rest if (symexOpt.startsWith("-sym:")) =>
          symexEngine = symexOpt.drop("-sym:".length) match {
            case "dfs" => GlobalParameters.SymexEngine.DepthFirstForward
            case "bfs" => GlobalParameters.SymexEngine.BreadthFirstForward
            case _ =>
              println("Unknown argument for -sym:, defaulting to bfs.")
              GlobalParameters.SymexEngine.BreadthFirstForward
          }
        arguments(rest)
      case symexDepthOpt :: rest if (symexDepthOpt.startsWith("-symDepth:")) =>
        symexMaxDepth = Some(symexDepthOpt.drop("-symDepth:".length).toInt)
        arguments(rest)
      case "-glb" :: rest => global = true; arguments(rest)
      case "-disj" :: rest => disjunctive = true; arguments(rest)
      case "-sol" :: rest => displaySolutionProlog = true; arguments(rest)
      case "-ssol" :: rest => displaySolutionSMT = true; arguments(rest)

      case "-solutionReconstruction:wp" :: rest =>
        solutionReconstruction = GlobalParameters.SolutionReconstruction.WP;
        arguments(rest)
      case "-solutionReconstruction:cegar" :: rest =>
        solutionReconstruction = GlobalParameters.SolutionReconstruction.CEGAR;
        arguments(rest)

      case "-in" :: rest => setInputToSTDIN; arguments(rest)

      case "-ints" :: rest => format = InputFormat.Nts; arguments(rest)
      case "-hin" :: rest => format = InputFormat.Prolog; arguments(rest)
      case "-hsmt" :: rest => format = InputFormat.SMTHorn; arguments(rest)

      case "-abstract" :: rest => templateBasedInterpolation = true; arguments(rest)
      case "-abstractPO" :: rest => {
        portfolio = GlobalParameters.Portfolio.Template
        arguments(rest)
      }
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
      case "-abstract:relEqs2" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.RelationalEqs2
        arguments(rest)
      }
      case "-abstract:relIneqs" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.RelationalIneqs
        arguments(rest)
      }
      case "-abstract:relIneqs2" :: rest => {
        templateBasedInterpolation = true
        templateBasedInterpolationType = AbstractionType.RelationalIneqs2
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

      case splitMode :: rest if (splitMode startsWith "-splitClauses:") => {
        splitClauses = splitMode.drop(14).toInt
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

      case heapSolver :: rest if (heapSolver.startsWith("-heapSolver:")) =>
        heapSolver match {
          case "-heapSolver:native" =>
            heapTheory = Param.HeapTheory.Native
          case "-heapSolver:array" =>
            heapTheory = Param.HeapTheory.Array
        }
        arguments(rest)

      case "-cloneArrays" :: rest => arrayCloning = true; arguments(rest)
      case "-noSlicing" :: rest => slicing = false; arguments(rest)
      case "-noIntervals" :: rest => intervals = false; arguments(rest)
      case "-fairNIASplitting" :: rest => niaFairSplitting = true; arguments(rest)
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
      case logPredsOption :: rest if (logPredsOption startsWith "-logPreds:") =>
        logPredicates = logPredsOption.drop("-logPreds:".length)
          .split(",").toSet; arguments(rest)
      case "-dot" :: str :: rest => dotSpec = true; dotFile = str; arguments(rest)
      case "-pngNo" :: rest => pngNo = true; arguments(rest)
      case "-dotCEX" :: rest => pngNo = false; arguments(rest)
      case "-eogCEX" :: rest => pngNo = false; eogCEX = true; arguments(rest)
      case "-cex" :: rest => plainCEX = true; arguments(rest)
      case "-scex" :: rest => plainCEX = true; cexInSMT = true; arguments(rest)
      case "-cexSimplified" :: rest => simplifiedCEX = true; arguments(rest)
      case "-assert" :: rest => GlobalParameters.get.assertions = true; arguments(rest)
      case "-verifyInterpolants" :: rest => verifyInterpolants = true; arguments(rest)
      case "-verifySolutions" :: rest => verifySolCEX = true; arguments(rest)
      case "-h" :: rest => println(greeting + "\n\nUsage: eld [options] file\n\n" +
          "General options:\n" +
          " -h                Show this information\n" +
          " -in               Read from standard input (defaults to Horn SMT format)\n" +
          " -assert           Enable debugging assertions. This implies -verifySolutions\n" +
          " -verifySolutions  Generate and verify (but do not output) models and proofs\n" +
          " -log:n            Display progress based on verbosity level n (0 <= n <= 3)\n" +
          "                     1: Statistics only\n" +
          "                     2: Invariants included\n" +
          "                     3: Includes counterexamples\n" +
          " -statistics       Equivalent to -log:1; displays statistics only\n" +
          " -log              Equivalent to -log:2; displays progress and invariants\n" +
          " -t:time           Set timeout (in seconds)\n" +
          " -cex              Show textual counterexamples\n" +
          " -scex             Show textual counterexamples in SMT-LIB format\n" +
          " -dotCEX           Output counterexample in dot format\n" +
          " -eogCEX           Display counterexample using eog\n" +
          " -m:func           Use function func as entry point (default: main)\n" +
          "\n" +
          "Horn engine:\n" +
          " -horn             Enable this engine\n" +
          " -p                Pretty Print Horn clauses\n" +
          " -sp               Pretty print the Horn clauses in SMT-LIB format\n" +
          " -sol              Show solution in Prolog format\n" +
          " -ssol             Show solution in SMT-LIB format\n" +
          " -logSimplified    Show clauses after preprocessing in Prolog format\n" +
          " -logSimplifiedSMT Show clauses after preprocessing in SMT-LIB format\n" +
          " -disj             Use disjunctive interpolation\n" +
          " -stac             Static acceleration of loops\n" +
          " -lbe              Disable preprocessor (e.g., clause inlining)\n" +
          " -arrayQuans:n     Introduce n quantifiers for each array argument\n" +
          "                     (default: off)\n" +
          " -cloneArrays      Use separate array theories for independent arrays\n" +
          " -noSlicing        Disable slicing of clauses\n" +
          " -noIntervals      Disable interval analysis\n" +
          " -hints:f          Read hints (initial predicates and abstraction templates)\n" +
          "                     from a file\n" +
          " -postHints:f      Read hints for processed clauses from a file\n" +
          " -pHints           Print initial predicates and abstraction templates\n" +
          " -pPredicates:f    Output predicates computed by CEGAR to a file\n" +
          " -logPreds:<preds> Log only predicates containing the specified substrings,\n" +
          "                     separated by commas. E.g., -logPreds=p1,p2 logs any\n" +
          "                     predicate with 'p1' or 'p2' in its name\n" +
          " -sym              Use symbolic execution with the default engine (bfs)\n" +
          " -sym:x            Use symbolic execution where x : {dfs, bfs}\n" +
          "                     {dfs: depth-first forward, bfs: breadth-first forward}\n" +
          " -symDepth:n       Set a max depth for symbolic execution (underapproximate)\n" +
//          " -glb\t\tUse the global approach to solve Horn clauses (outdated)\n" +
//	  "\n" +
//          " -abstract\tUse interpolation abstraction for better interpolants (default)\n" +
          " -abstract:t       Interp. abstraction: off, manual, term, oct,\n" +
          "                     relEqs, relIneqs, relEqs2 (default), relIneqs2\n" +
          " -abstractTO:t     Timeout (s) for abstraction search (default: 2.0)\n" +
          " -abstractPO       Run with and w/o interpolation abstraction in parallel\n" +
          " -portfolio        Run different standard configurations in parallel\n" +
          " -splitClauses:n   Aggressiveness when splitting disjunctions in clauses\n" +
          "                     (0 <= n <= 2, default: 1)\n" +
          
          "\n" +
          " -hin              Expect input in Prolog Horn format\n" +
          " -hsmt             Expect input in Horn SMT-LIB format\n" +
          " -ints             Expect input in integer NTS format\n"
          )
          false
      case arg :: _ if arg.startsWith("-") =>
        arguments(List("-h"))
        throw new MainException(s"unrecognized option '$arg'")
      case fn :: rest => fileName = fn;  openInputFile; arguments(rest)
    }

    // Exit early if we showed the help
    if (!arguments(args.toList))
      return

    if (in == null) {
      arguments(List("-h"))
      throw new MainException("no input file given")
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
        } else
          throw new MainException ("could not figure out the input format")
    }

    format match {
      case InputFormat.Prolog | InputFormat.SMTHorn
      =>
        // those formats can only be handled in Horn mode
        horn = true
      case _ =>
        // nothing
    }
    
    if (horn) {
      
      val (clauseSet, absMap) = try { format match {
        case InputFormat.Prolog =>
          (lazabs.horn.parser.HornReader.apply(in), None)
        case InputFormat.SMTHorn =>
          (lazabs.horn.parser.HornReader.fromSMT(in), None)
        case InputFormat.Nts =>
          (NtsHorn(NtsWrapper(in)), None)
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

      if(solFileName != "") {
        val solStream = getFileStream(solFileName)
        val solution = lazabs.horn.parser.HornReader.apply(solStream)
        return
      }

      try {
        lazabs.horn.Solve(clauseSet, absMap, global, disjunctive,
                          drawRTree, lbe)
      } catch {
        case PrintingFinishedException => // nothing more to do
      }
        
      return
    }

    val (cfg,m) = format match {
      case InputFormat.Nts =>
        val ntsc = NtsCFG(NtsWrapper(in), lbe, staticAccelerate)
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
      println("(error \"" + ap.parser.SMTLineariser.escapeString(message) + "\")")
  
}
