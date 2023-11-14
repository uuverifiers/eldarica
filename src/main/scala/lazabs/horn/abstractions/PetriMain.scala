/**
 * Copyright (c) 2011-2017 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.abstractions

import scala.collection.mutable.{LinkedHashSet, HashMap => MHashMap,
                                 ArrayBuffer, HashSet => MHashSet}
import scala.io.StdIn

import ap.parser._
import ap.util.CmdlParser
import lazabs.horn.bottomup.{HornClauses, HornPredAbs,
                             TemplateInterpolator, DagInterpolator, Util}

import ap.SimpleAPI
import SimpleAPI.ProverStatus

object PetriMain {

  //////////////////////////////////////////////////////////////////////////////
  // System options

  var filename : String = null
  var globalOrthogonalSpace = true
  var accelerateSingleActions = true
  var accelerateIncreasingCycles = true
  var controlGroups = 2

  //////////////////////////////////////////////////////////////////////////////

  def main(args: Array[String]) : Unit = {
    ap.util.Debug enableAllAssertions true

    // Handle command-line options
    import CmdlParser._

    for (a <- args) a match {
      case Opt("h", _) | Opt("help", _) => {
        println("Eldarica-P - The Unbounded Petri Analyser")
        println("(Build 2014-01-29)")
        println("(c) Philipp Rümmer, 2014")
        println
        println("Based on:")
        println("Eldarica, http://lara.epfl.ch/w/eldarica")
        println("Princess, http://www.philipp.ruemmer.org/princess.shtml")
        println
        println("General use:")
        println("  java -jar eldarica-p.jar <options> <filename.net>")
        println
        println("If no filename is specified, inputs are read from stdin.")
        println
        println("Options:")
        println(" -interpolationAbstractions=<options>")
        println("     where <options> is a comma-separate list of")
        println("       globalOrthogonalSpace")
        println("       accelerateSingleActions")
        println("       accelerateIncreasingCycles")
        println("     default: all")
        println(" -controlGroups=<number>")
        println("     maximum number of control groups to handle explicitly")
        println("     default: 2")

        System exit 1
      }

      case ValueOpt("interpolationAbstractions", values) => {
        globalOrthogonalSpace = false
        accelerateSingleActions = false
        accelerateIncreasingCycles = false
        for (v <- values split ",") v match {
          case ""                           => // nothing
          case "globalOrthogonalSpace"      => globalOrthogonalSpace = true
          case "accelerateSingleActions"    => accelerateSingleActions = true
          case "accelerateIncreasingCycles" => accelerateIncreasingCycles = true
          case v => {
            println("Unrecognised interpolation abstraction: " + v)
            System exit 1
          }
        }
      }

      case ValueOpt("controlGroups", IntVal(num)) =>
        controlGroups = num

      case Opt(_, _) => {
        println("Unrecognised option: " + a)
        System exit 1
      }

      case a => filename = a
      
    }

    System exit (
      if (filename == null) {
        println("Reading Petri net from stdin ... ")
        (new PetriMain).result
      } else {
        println("Reading Petri net from " + filename + " ... ")
        Console.withIn(new java.io.BufferedReader (
                         new java.io.FileReader(new java.io.File (filename)))) {
          (new PetriMain).result
        }
      }
    )
  }  

}

class PetriMain {

  import HornClauses._
  import IExpression._

  val PlaceRef     = """(\p{Alnum}+)""".r
  val PlaceRefNum  = """(\p{Alnum}+)\*([0-9]+)""".r
  val Transition   = """ *tr +(\p{Alnum}+) +\[\] +([\p{Alnum}* ]*)->([\p{Alnum}* ]*) *""".r
  val Place        = """ *pl +(\p{Alnum}+) +\( *([0-9]+) *\) *""".r
  val FinalPlace   = """ *final +(\p{Alnum}+) +\( *([0-9]+) *\) *""".r
  val StateFormula = """ *finalConfiguration(.*)""".r

  
  val (places, transitions, initialValues, finalConfig) = {
    val places        = new LinkedHashSet[String]
    val transitions   = new LinkedHashSet[(Seq[String], Seq[String])]
    val initialValues = new MHashMap[String, Int]
    val finalValues   = new MHashMap[String, Int]
    var finalConfig : IFormula = null

    var str = StdIn.readLine
    while (str != null) {
      str match {
        case Transition(name, preStr, postStr) => {
          val prePlaces =
            (for (place <- (preStr.trim split " +").iterator;
                  p <- place match {
                    case "" =>
                      Iterator.empty
                    case PlaceRef(name) =>
                      Iterator single name
                    case PlaceRefNum(name, num) =>
                      for (_ <- (0 until num.toInt).iterator) yield name
                  }) yield p).toList
  
          val postPlaces =
            (for (place <- (postStr.trim split " +").iterator;
                  p <- place match {
                    case "" =>
                      Iterator.empty
                    case PlaceRef(name) =>
                      Iterator single name
                    case PlaceRefNum(name, num) =>
                      for (_ <- (0 until num.toInt).iterator) yield name
                  }) yield p).toList
  
          places ++= prePlaces
          places ++= postPlaces
  
          transitions += ((prePlaces, postPlaces))
        }
  
        case Place(name, num) => {
          places += name.trim
          initialValues += (name.trim -> num.toInt)
        }
  
        case FinalPlace(name, num) => {
          places += name.trim
          finalValues += (name.trim -> num.toInt)
        }
  
        case StateFormula(iFor) => {
          var forStr = iFor
          while ((forStr count (_ == '(')) > (forStr count (_ == ')')))
            forStr = forStr + " " + StdIn.readLine

          forStr = forStr.trim
          if (forStr.isEmpty)
            forStr = "true"

          // parse the formula
          val env = new Environment[Unit, Sort, Unit, Unit, Sort]
          for (p <- places.toList.reverse)
            env.pushVar(p, Sort.Integer)
          
          val reader = new java.io.StringReader(forStr)
          finalConfig =
            ApParser2InputAbsy.parseExpression(reader, env) match {
              case f : IFormula => f
              case _ => throw new Exception(
                          "Expected formula, not " + forStr)
            }
        }

        case x if (x.trim.isEmpty) =>
          // nothing
  
        case x =>
          println("Ignoring line: " + x)
      }
  
      str = StdIn.readLine
    }

    if (finalConfig == null)
      finalConfig =
        and(for ((p, i) <- places.iterator.zipWithIndex;
                 if (finalValues contains p))
            yield (v(i) === finalValues(p)))

    // make sure that may of initial values contains all places
    for (p <- places)
      initialValues.getOrElseUpdate(p, 0)

    (places.toList, transitions.toList,
     initialValues.toMap, finalConfig)
  }

  println("" + places.size + " places, " +
          transitions.size + " transitions")

//  println(places)
//  println(transitions)
//  println(initialValues)

  val placeIndex = places.iterator.zipWithIndex.toMap

  //////////////////////////////////////////////////////////////////////////////

  println

  val selectedControlSets = if (PetriMain.controlGroups > 0) {

  println("Computing control groups ...")

  val controlSets : Seq[Seq[String]] = {
    val controlCandidates = new LinkedHashSet[String]
    controlCandidates ++= places
  
    for ((p, v) <- initialValues)
      if (v > 1)
        controlCandidates -= p
  
    for ((pre, post) <- transitions.iterator;
         pset <- Iterator(pre, post);
         p <- pset.iterator)
      if ((pset count (_ == p)) > 1)
        controlCandidates -= p
  
    val oneInitPlaces =
      (for (p <- controlCandidates.iterator;
            if (initialValues(p) == 1))
       yield p).toList
  
//    println(controlCandidates.toList)
//    println(oneInitPlaces)
  
      if (oneInitPlaces.isEmpty)
        List()
      else SimpleAPI.withProver { p =>
        import p._
    
        val sets = new ArrayBuffer[Seq[String]]

        try { withTimeout(15000) {
    
        val flags = createBooleanVariables(places.size)
        for (p <- places)
          if (!(controlCandidates contains p))
            !! (!flags(placeIndex(p)))
    
        !! (or(for (p <- oneInitPlaces.iterator)
               yield (flags(placeIndex(p)) & and(
                        for (q <- oneInitPlaces.iterator; if (p != q))
                        yield !flags(placeIndex(q))
                      ))))
    
        val sums = Array.fill(transitions.size)(i(0))
    
        for (p <- controlCandidates) {
          var thenFor : IFormula = true
          var elseFor : IFormula = true
    
          for (((pre, post), transNum) <- transitions.iterator.zipWithIndex)
            (pre contains p, post contains p) match {
              case (true, false) => {
                val const = createConstant
                sums(transNum) = sums(transNum) +++ const
                thenFor = thenFor &&& (const === -1)
                elseFor = elseFor &&& (const === 0)
              }
              case (false, true) => {
                val const = createConstant
                sums(transNum) = sums(transNum) +++ const
                thenFor = thenFor &&& (const === 1)
                elseFor = elseFor &&& (const === 0)
              }
              case _ => // nothing
            }
    
          !! (IFormulaITE(flags(placeIndex(p)), thenFor, elseFor))
        }
    
        !! (and(for (t <- sums.iterator) yield (t === 0)))
    
        while (??? == ProverStatus.Sat) {
          var enabledPlaces = (for ((f, i) <- flags.iterator.zipWithIndex;
                                    if (eval(f))) yield i).toList
    
          // can this control set be maximised?
          scope {
            for ((f, i) <- flags.iterator.zipWithIndex;
                 if (enabledPlaces contains i))
              !! (f)
    
            var cont = true
            while (cont) {
              cont = false
    
              !! (or(for (p <- controlCandidates.iterator;
                          i = placeIndex(p);
                          if (!(enabledPlaces contains i)))
                       yield flags(i)))
    
              if (??? == ProverStatus.Sat) {
                cont = true
    
                val newEnabledPlaces =
                  (for ((f, i) <- flags.iterator.zipWithIndex;
                        if (eval(f))) yield i).toList
                for (i <- newEnabledPlaces diff enabledPlaces)
                  !! (flags(i))
    
                enabledPlaces = newEnabledPlaces
              }
            }
          }
    
          sets += (for (i <- enabledPlaces) yield places(i))
    
          !! (or(for ((f, i) <- flags.iterator.zipWithIndex;
                      if (!(enabledPlaces contains i))) yield f))
        }
    
        }} catch {
          case SimpleAPI.TimeoutException => println("T/O")
        }

        sets.toList
      }
    }

//  println(controlSets)

    val coveredStates = new MHashSet[String]
    var predNum = 1

    val selectedControlSets = {
      for (cset <- controlSets sortBy { s => -s.size };
           if (// cset.size > 1 &&
               // predNum * cset.size <= 3 * places.size &&
               !(cset exists coveredStates))) yield {
        coveredStates ++= cset
        predNum = predNum * cset.size
        cset
      }
    }.toList take PetriMain.controlGroups

    for (s <- selectedControlSets)
      println(s mkString ", ")

    selectedControlSets

  } else {
    List()
  }

  val controlPlaces = selectedControlSets.flatten
  val dataPlaces = places diff controlPlaces
  val dataPlaceIndex = dataPlaces.iterator.zipWithIndex.toMap
  val controlPlaceIndex = controlPlaces.iterator.zipWithIndex.toMap

  println("Data places:")
  println(dataPlaces mkString ", ")

  //////////////////////////////////////////////////////////////////////////////

  println
  print("Encoding as Horn clauses ... ")

  val invPredSeq = {
    def controlStates(pls : List[Seq[String]])
                     : Iterator[List[String]] = pls match {
      case List() =>
        Iterator single List()
      case pset :: remPls =>
        for (suffix <- controlStates(remPls);
             p <- pset.iterator) yield p :: suffix
    }

    (for (ps <- controlStates(selectedControlSets))
     yield (ps, new Predicate ("inv_" + (ps mkString "_"),
                               dataPlaces.size))).toList
  }

  val invPred = invPredSeq.toMap
  val placeCounters =
    for (p <- dataPlaces.toList) yield new ConstantTerm (p)
  val controlPlaceCounters =
    for (p <- controlPlaces.toList) yield new ConstantTerm (p)

  val counterFor =
    ((dataPlaces.iterator zip placeCounters.iterator) ++
     (controlPlaces.iterator zip controlPlaceCounters.iterator)).toMap

  //////////////////////////////////////////////////////////////////////////////

  val initClause = {
    val cPlaces =
      for (cset <- selectedControlSets)
      yield (cset find { p => initialValues(p) == 1}).get
      
    IAtom(invPred(cPlaces),
          for (p <- dataPlaces.toList)
            yield i(initialValues(p))) :- true
  }
  
  //////////////////////////////////////////////////////////////////////////////

  val (transitionClauses, actionVectors) =
    (for ((pre, post) <- transitions.iterator;
          (preCPlaces, prePred) <- invPredSeq.iterator;
          if (pre forall { p =>
              (preCPlaces.iterator zip selectedControlSets.iterator) forall {
                case (q, pset) => !(pset contains p) || p == q
              }})) yield {
 
       val postCPlaces =
         (for ((p, pset) <-
                 preCPlaces.iterator zip selectedControlSets.iterator) yield {
            if (pre contains p) (post filter (pset contains _)).head else p
          }).toList
 
       val values = Array.fill(dataPlaces.size)(0)
 
       for (p <- pre)
         for (ind <- dataPlaceIndex get p)
           values(ind) = values(ind) - 1
 
       val constraint =
         and(for ((c, value) <- placeCounters.iterator zip values.iterator)
             yield geqZero(c +++ value))
 
       for (p <- post)
         for (ind <- dataPlaceIndex get p)
           values(ind) = values(ind) + 1
 
       val postValues =
         (for ((c, value) <- placeCounters.iterator zip values.iterator)
          yield (c +++ value)).toList
 
       (IAtom(invPred(postCPlaces), postValues) :- (
         IAtom(prePred, placeCounters), constraint),
        values.toList)
     }).toList.unzip

  //////////////////////////////////////////////////////////////////////////////

  val assertionClauses = {
    val substList = for (p <- places) yield i(counterFor(p))

    val configToCheck =
      VariableSubstVisitor(finalConfig, (substList, -substList.size))

    for ((cPlaces, pred) <- invPredSeq.iterator) yield {
      val controlConstraint =
        and(for ((p, pset) <-
                   cPlaces.iterator zip selectedControlSets.iterator;
                 q <- pset.iterator)
            yield (counterFor(q) === (if (p == q) 1 else 0)))

      false :- (
        IAtom(pred, placeCounters map (i(_))),
        configToCheck,
        controlConstraint)
    }
  }.toList

  //////////////////////////////////////////////////////////////////////////////

/*  println(initClause)
  for (c <- transitionClauses)
    println(c)
  for (c <- assertionClauses)
    println(c) */

  println("" + (1 + transitionClauses.size + assertionClauses.size) + " clauses")

  println
  println("Solving ...")

  //////////////////////////////////////////////////////////////////////////////

/*  val initialPredicates =
                    Map(globalPred -> (for (j <- 0 until placeCounters.size;
                                            o <- List(0, 1))
                                       yield (v(j) === o))) */

  val predAbs =
    new HornPredAbs(List(initClause) ++ transitionClauses ++ assertionClauses,
                    Map(), // initialPredicates,
                    if (PetriMain.accelerateSingleActions ||
                        PetriMain.accelerateIncreasingCycles ||
                        PetriMain.globalOrthogonalSpace)
                      TemplateInterpolator.interpolatingPredicateGenCEXAbsPetri(
                        actionVectors,
                        PetriMain.accelerateSingleActions,
                        PetriMain.accelerateIncreasingCycles,
                        PetriMain.globalOrthogonalSpace)
                    else
                      DagInterpolator.interpolatingPredicateGenCEXAndOr _
                    )
  
  println
  val result =
  predAbs.result match {
    case Right(cex) => {
      println("REACHABLE")
//      Util.show(for (p <- cex) yield p._1, "horn-cex")
      (cex map (_._1)).prettyPrint

      0
    }
    case Left(solution) => {
      println("UNREACHABLE")
      println
      println("Inductive invariant:")
      val inv =
        and(for (places <- selectedControlSets.iterator)
            yield (sum(for (p <- places.iterator)
                       yield i(counterFor(p))) === 1)) &&&
        and(for ((cPlaces, pred) <- invPredSeq.iterator)
            yield (or(for (p <- cPlaces.iterator)
                      yield (counterFor(p) === 0)) |||
                   VariableSubstVisitor(solution.getOrElse(pred, true),
                                        (placeCounters map (i(_)),
                                         -placeCounters.size))))
      PrincessLineariser.printExpression((new Simplifier)(inv))
      println

      1
    }
  }

}
