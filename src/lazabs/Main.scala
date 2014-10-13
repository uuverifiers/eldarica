/**
 * Copyright (c) 2011-2014 Hossein Hojjat, Filip Konecny, Philipp Ruemmer,
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

import java.io.{FileInputStream,InputStream,FileNotFoundException}
import parser._
import lazabs.art._
import lazabs.art.SearchMethod._
import lazabs.prover._
import lazabs.viewer._
import lazabs.utils.Inline._
import lazabs.utils.PointerAnalysis
import lazabs.cfg.MakeCFG
import lazabs.nts._
import lazabs.horn.parser.HornReader
import lazabs.horn.bottomup.HornPredAbs.RelationSymbol
import lazabs.horn.abstractions.AbsLattice
import lazabs.horn.abstractions.StaticAbstractionBuilder.AbstractionType

object GlobalParameters {
  object InputFormat extends Enumeration {
    val Nts, Scala,
        Prolog, SMTHorn, UppaalOG, UppaalRG, UppaalRelational, Bip,
        AutoDetect = Value
  }

  val parameters =
    new scala.util.DynamicVariable[GlobalParameters] (new GlobalParameters)

  def get : GlobalParameters = parameters.value
}

class GlobalParameters {
  var in: InputStream = null
  var fileName = ""
  var funcName = "sc_main"
  var solFileName = ""
  var timeout:Option[Int] = None
  var spuriousness = true
  var searchMethod = DFS
  var drawRTree = false
  var drawCFG = false
  var absInFile = false
  var lbe = false
  var prettyPrint = false
  var smtPrettyPrint = false  
  var interpolation = false
  var ntsPrint = false
  var horn = false
  var global = false
  var disjunctive = false
  var displaySolutionProlog = false
  var displaySolutionSMT = false
  var format = GlobalParameters.InputFormat.AutoDetect
  var templateBasedInterpolation = false
  var templateBasedInterpolationType : AbstractionType.Value = AbstractionType.RelationalEqs
  var templateBasedInterpolationTimeout = 2000
  var cegarHintsFile : String = ""
  var arrayRemoval = false
  var princess = false
  var staticAccelerate = false
  var dynamicAccelerate = false
  var underApproximate = false
  var template = false
  var dumpInterpolationQuery = false
  var babarew = false
  var log = false
  var printHornSimplified = false
  var dotSpec = false
  var dotFile : String = null
  var pngNo = true;
  var assertions = false
  var timeoutChecker : () => Unit = () => ()
}


object Main {
  def assertions = GlobalParameters.get.assertions

  class MainException(msg : String) extends Exception(msg)

  def openInputFile {
    val params = GlobalParameters.parameters.value
    import params._
    in = new FileInputStream(fileName)
  }
  def checkInputFile {
    val params = GlobalParameters.parameters.value
    import params._
    if (in == null)
      throw new MainException("Input file missing")
  }
  def getASTree = {
    val params = GlobalParameters.parameters.value
    import params._
    val lexer = new Lexer(in)
    val parser = new Parser(lexer)
    val tree = parser.parse()
    if(!(tree.value.isInstanceOf[lazabs.ast.ASTree.Sobject]))
      throw new MainException("The input file is invalid")
    val spa = PointerAnalysis(tree.value.asInstanceOf[lazabs.ast.ASTree.Sobject])
    val so = inline(spa)
    val typ = lazabs.types.TypeCheck(so)
    typ
  }

  def main(args: Array[String]) : Unit = doMain(args, false)

  //def main(args: Array[String]) : Unit = lazabs.horn.FatTest(args(0))
  

  val greeting =
    "Eldarica, 2014-08-20. (C) Copyright 2012-2014 Hossein Hojjat and Philipp Ruemmer"

  def doMain(args: Array[String],
             stoppingCond : => Boolean) : Unit = {
    val params = new GlobalParameters
    GlobalParameters.parameters.value = params

    import params._
    import GlobalParameters.InputFormat

    def arguments(args: List[String]): Unit = args match {
      case Nil =>
      case "-c" :: rest => drawCFG = true; arguments(rest)
      case "-r" :: rest => drawRTree = true; arguments(rest)
      case "-f" :: rest => absInFile = true; arguments(rest)
      case "-p" :: rest => prettyPrint = true; arguments(rest)
      case "-sp" :: rest => smtPrettyPrint = true; arguments(rest)
      case "-pnts" :: rest => ntsPrint = true; arguments(rest)
      case "-horn" :: rest => horn = true; arguments(rest)
      case "-glb" :: rest => global = true; arguments(rest)
      case "-disj" :: rest => disjunctive = true; arguments(rest)
      case "-sol" :: rest => displaySolutionProlog = true; arguments(rest)
      case "-ssol" :: rest => displaySolutionSMT = true; arguments(rest)

      case "-ints" :: rest => format = InputFormat.Nts; arguments(rest)
      case "-hin" :: rest => format = InputFormat.Prolog; arguments(rest)
      case "-hsmt" :: rest => format = InputFormat.SMTHorn; arguments(rest)
      case "-uppog" :: rest => format = InputFormat.UppaalOG; arguments(rest)
      case "-upprg" :: rest => format = InputFormat.UppaalRG; arguments(rest)
      case "-upprel" :: rest => format = InputFormat.UppaalRelational; arguments(rest)
      case "-bip" :: rest =>  format = InputFormat.Bip; arguments(rest)

      case "-abstract" :: rest => templateBasedInterpolation = true; arguments(rest)
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
      case tTimeout :: rest if (tTimeout.startsWith("-abstractTO:")) =>
        templateBasedInterpolationTimeout =
          (java.lang.Float.parseFloat(tTimeout.drop(12)) * 1000).toInt;
        arguments(rest)

      case tFile :: rest if (tFile.startsWith("-hints:")) => {
        cegarHintsFile = tFile drop 7
        arguments(rest)
      }

      case "-n" :: rest => spuriousness = false; arguments(rest)
      case "-i" :: rest => interpolation = true; arguments(rest)
      case "-lbe" :: rest => lbe = true; arguments(rest)
      case "-array" :: rest => arrayRemoval = true; arguments(rest)
      case "-princess" :: rest => princess = true; arguments(rest)
      case "-stac" :: rest => staticAccelerate = true; arguments(rest)
      case "-dynac" :: rest => dynamicAccelerate = true; arguments(rest)
      case "-unap" :: rest => underApproximate = true; arguments(rest)
      case "-tem" :: rest => template = true; arguments(rest)
      case "-dinq" :: rest => dumpInterpolationQuery = true; arguments(rest)
      case "-brew" :: rest => babarew = true; arguments(rest)
      case "-bfs" :: rest => searchMethod = BFS; arguments(rest)
      case "-prq" :: rest => searchMethod = PRQ; arguments(rest)
      case "-dfs" :: rest => searchMethod = DFS; arguments(rest)
      case "-rnd" :: rest => searchMethod = RND; arguments(rest)
      case tTimeout :: rest if (tTimeout.startsWith("-t:")) =>
        val time = (java.lang.Float.parseFloat(tTimeout.drop(3)) * 1000).toInt
        timeout = Some(time); arguments(rest)
      case mFuncName :: rest if (mFuncName.startsWith("-m:")) => funcName = "sc_" + mFuncName.drop(3); arguments(rest)
      case sSolFileName :: rest if (sSolFileName.startsWith("-s:")) => solFileName = sSolFileName.drop(3); arguments(rest)
      case "-log" :: rest => log = true; arguments(rest)
      case "-logSimplified" :: rest => printHornSimplified = true; arguments(rest)
      case "-dot" :: str :: rest => dotSpec = true; dotFile = str; arguments(rest)
      case "-pngNo" :: rest => pngNo = true; arguments(rest)
      case "-dotCEX" :: rest => pngNo = false; arguments(rest)
      case "-assert" :: rest => GlobalParameters.get.assertions = true; arguments(rest)
      case "-h" :: rest => println(greeting + "\n\nUsage: lazabs [options] file\n\n" +
          "General options:\n" +
          " -h\t\tShow this information\n" +
          " -assert\tEnable assertions in Eldarica\n" +
          " -log\t\tDisplay progress and found invariants\n" + 
          " -t:time\tSet timeout (in seconds)\n" +
          " -dotCEX\tShow counterexample using dot\n" + 
          "\n" +
          "Horn engine:\n" +
          " -horn\t\tEnable this engine\n" + 
          " -p\t\tPretty Print Horn clauses\n" +
          " -sp\t\tPretty print the Horn clauses in SMT-LIB format\n" + 
          " -sol\t\tShow solution in Prolog format\n" + 
          " -ssol\t\tShow solution in SMT-LIB format\n" + 
          " -disj\t\tUse disjunctive interpolation\n" +
          " -stac\t\tStatic acceleration of loops\n" +
          " -lbe\t\tDisable inlining of linear Horn clauses\n" +
          " -hints:f\tRead initial predicates and abstraction templates from a file\n" +
          " -glb\t\tUse the global approach to solve Horn clauses (outdated)\n" +
	  "\n" +
          " -abstract\tUse interpolation abstraction for better interpolants\n" +
          " -abstract:t\tAbstraction type: term, oct, relEqs (default), relIneqs\n" +
          " -abstractTO:t\tTimeout (s) for abstraction search (default: 2.0)\n" +
          
          "\n" +
          " -hin\t\tExpect input in Prolog Horn format\n" +  
          " -hsmt\t\tExpect input in Horn SMT-LIB format\n" +
          " -ints\t\tExpect input in integer NTS format\n" +
          " -bip\t\tExpect input in BIP format\n" +
          " -uppog\t\tExpect UPPAAL file using Owicki-Gries encoding\n" +
          " -upprg\t\tExpect UPPAAL file using Rely-Guarantee encoding\n" +
          " -upprel\tExpect UPPAAL file using Relational Encoding\n" + 
          "\n" +
          "Standard CEGAR engine (partly obsolete):\n" +
          " -c\t\tDraw control flow graph\n" +
          " -r\t\tDraw reachability\n" +
          " -f\t\tWrite abstraction information in file\n" +
          " -m:func\tConsider the function func instead of main\n" +
          " -p\t\tPretty Print\n" +
          " -ints\t\tInput a file in NTS format\n" +
          " -pnts\t\tPrint the CFG in NTS format\n" +
          " -n\t\tDo not check the counter examples for spuriousness\n" +
          " -i\t\tUse interpolation\n" +
          " -lbe\t\tUse large block encoding for NTS files\n" +
          " -array\t\tRemove array operations\n" +          
          " -princess\tUse Princess as theorem prover\n" +
          " -stac\t\tStatic acceleration of loops\n" +
          " -dynac\t\tDynamic acceleration of loops\n" +
          " -unap\t\tUnder approximation of loops in dynamic acceleration\n" +
          " -dinq\t\tDump interpolation query\n" + 
          " -brew\t\tRewrites bapa formulae into Presburger formulae\n" +          
          " -bfs\t\tUse Breadth-first search\n" +
          " -dfs\t\tUse Depth-first search\n" +
          " -prq\t\tUse Priority queue search\n" +
          " -rnd\t\tUse random search\n")
      case fn :: rest => fileName = fn;  openInputFile; arguments(rest)
    }
    
    arguments(args.toList)

    if (in == null)
      throw new MainException("no input file given")

    val startTime = System.currentTimeMillis

    timeoutChecker = timeout match {
      case Some(to) => () => {
        if (System.currentTimeMillis - startTime > to.toLong)
          throw new Exception("timeout")
        if (stoppingCond)
          throw new Exception("stopped")
      }
      case None => () => {
        if (stoppingCond)
          throw new Exception("stopped")
      }
    }
    
    if(princess) Prover.setProver(lazabs.prover.TheoremProver.PRINCESS)

    if (format == InputFormat.AutoDetect) {
        // try to guess the file type from the extension
        if (fileName endsWith ".horn")
          format = InputFormat.Prolog
        else if (fileName endsWith ".smt2")
          format = InputFormat.SMTHorn
        else if (fileName endsWith ".nts") {
          format = InputFormat.Nts
          // then also choose -horn by default
          horn = true         
        } else if (fileName endsWith ".scala")
          format = InputFormat.Scala
        else if (fileName endsWith ".bip")
          format = InputFormat.Bip
        else if (fileName endsWith ".xml")
          format = InputFormat.UppaalOG
        else
          throw new Exception ("could not figure out the input format")
    }

    format match {
      case InputFormat.Prolog | InputFormat.SMTHorn | InputFormat.Bip |
           InputFormat.UppaalOG | InputFormat.UppaalRG |
           InputFormat.UppaalRelational =>
        // those formats can only be handled in Horn mode
        horn = true
      case _ =>
        // nothing
    }

    if (horn) {
      
      format match {
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
      }

      val (clauseSet, absMap) = format match {
        case InputFormat.Prolog =>
          (lazabs.horn.parser.HornReader.apply(fileName), None)
        case InputFormat.SMTHorn =>
          (lazabs.horn.parser.HornReader.fromSMT(fileName), None)
        case InputFormat.UppaalOG =>
          lazabs.upp.OwickiGries(fileName, templateBasedInterpolation)
        case InputFormat.UppaalRG =>
          lazabs.upp.RelyGuarantee(fileName, templateBasedInterpolation)
        case InputFormat.Nts =>
          (NtsHorn(NtsWrapper(fileName)), None)
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
        val solution = lazabs.horn.parser.HornReader.apply(solFileName)
        return
      }

      val uppflag = format match {
        case InputFormat.UppaalOG | InputFormat.UppaalRG => true
        case _ => false
      }

      if (log) Console.withErr(Console.out) {
        lazabs.horn.Solve(clauseSet, absMap, global, disjunctive,
                          (uppflag, templateBasedInterpolation), drawRTree, lbe, log)
      } else {
        lazabs.horn.Solve(clauseSet, absMap, global, disjunctive,
                          (uppflag, templateBasedInterpolation), drawRTree, lbe, log)
      }
        
      return
    }

    val (cfg,m) = format match {
      case InputFormat.Nts =>
        val ntsc = NtsCFG(NtsWrapper(fileName),lbe,staticAccelerate)
        (ntsc,Some(Map[Int,String]().empty ++ NtsWrapper.stateNameMap))
      case InputFormat.Scala =>
        checkInputFile
        val ast = getASTree
        if(prettyPrint) {println(ScalaPrinter(ast)); return}
        (MakeCFG(ast,funcName,arrayRemoval,staticAccelerate),None)
    }

    if(drawCFG) {DrawGraph(cfg.transitions.toList,cfg.predicates,absInFile,m); return}

    if(ntsPrint) {
      println(NTSPrinter(cfg))
      return
    }

    if(timeout.isDefined) Z3Wrapper.setTimeout(timeout)

    val rTree = if (!interpolation) MakeRTree(cfg, MakeCFG.getLoops, spuriousness, searchMethod, log)
      else MakeRTreeInterpol(cfg, MakeCFG.getLoops, searchMethod, babarew, dumpInterpolationQuery, dynamicAccelerate, underApproximate, template, log)
    if(drawRTree) DrawGraph(rTree, absInFile)
  }
  
}
