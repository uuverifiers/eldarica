/**
 * Copyright (c) 2011-2020 Philipp Ruemmer. All rights reserved.
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

package lazabs.horn.concurrency

import ap.parser._
import ap.util.Seqs
import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import lazabs.{GlobalParameters, ParallelComputation}
import lazabs.horn.bottomup.{DagInterpolator, HornClauses, HornPredAbs, HornWrapper, Util}
import lazabs.horn.abstractions.{AbsLattice, AbstractionRecord, LoopDetector, StaticAbstractionBuilder, VerificationHints}
import lazabs.horn.bottomup.DisjInterpolator.AndOrNode
import lazabs.horn.concurrency.HintsSelection.{initialIDForHints, writeHintsWithIDToFile}
import lazabs.horn.bottomup.TemplateInterpolator
import lazabs.horn.preprocessor.DefaultPreprocessor

import scala.concurrent.TimeoutException
import scala.collection.mutable.{ArrayBuffer, LinkedHashSet, HashSet => MHashSet}

object VerificationLoop {

  import HornClauses.Clause
  import ParametricEncoder._

  abstract sealed class CEXStep(val newStates : Seq[IAtom])
  case class CEXInit     (_newStates : Seq[IAtom],
                          clauses : Seq[Clause])             extends CEXStep(_newStates)
  case class CEXLocalStep(_newStates : Seq[IAtom],
                          processIndex : Int,
                          clause : Clause)                   extends CEXStep(_newStates)
  case class CEXCommStep (_newStates : Seq[IAtom],
                          channel : CommChannel,
                          senderIndex : Int,
                          senderClause : Clause,
                          receiverIndex : Int,
                          receiverClause : Clause)           extends CEXStep(_newStates)
  case class CEXBarrierStep(_newStates : Seq[IAtom],
                            barrier : Barrier,
                            clauses : Seq[(Int, Clause)])    extends CEXStep(_newStates)
  case class CEXTimeElapse(_newStates : Seq[IAtom],
                           delay : (Int, Int))               extends CEXStep(_newStates)

  type Counterexample = Seq[CEXStep]

  //////////////////////////////////////////////////////////////////////////////

  def prettyPrint(cex : Counterexample) : Unit = {
    val colWidth = ((for (step <- cex.iterator; a <- step.newStates.iterator)
                     yield (SimpleAPI pp a).size).max + 2) max 10
    val totalWidth = cex.head.newStates.size * colWidth

    def toColWidth(s : String) = {
      val shortened = s take (colWidth - 2)
      ((" " * ((colWidth - shortened.size)/2)) + s).padTo(colWidth, ' ')
    }

    def asColumns(strs : Seq[IAtom]) =
      println((for (x <- strs) yield toColWidth(SimpleAPI pp x)) mkString "")

    def inColumns(data : Map[Int, Seq[String]]) = {
      val cols = (for ((c, _) <- data) yield c).max + 1
      val rows = (for ((_, lines) <- data) yield lines.size).max
      for (row <- 0 until rows) {
        for (col <- 0 until cols) (data get col) match {
          case None => print(" " * colWidth)
          case Some(line) => print(toColWidth(line(row)))
        }
        println
      }
    }

    var lastStates : Seq[IAtom] = null

    for (step <- cex) {
      println("-" * totalWidth)
      step match {
        case CEXInit(states, _) => {
          println("Init:")
          asColumns(states)
        }
        case CEXLocalStep(states, index, _) =>
          inColumns(Map(
            index -> List("  |  ",
                          "  |  ",
                          "  V  ",
                          SimpleAPI pp states(index))
          ))
        case CEXCommStep(states, channel, senderIndex, _, receiverIndex, _) =>
          inColumns(Map(
            senderIndex ->   List("|",
                                  "" + channel + "!",
                                  "|",
                                  "V",
                                  SimpleAPI pp states(senderIndex)),
            receiverIndex -> List("|",
                                  "" + channel + "?",
                                  "|",
                                  "V",
                                  SimpleAPI pp states(receiverIndex))
          ))
        case CEXBarrierStep(states, barrier, clauses) =>
          inColumns(
            (for ((ind, _) <- clauses.iterator) yield {
               if (lastStates != null && lastStates(ind) == states(ind))
                 ind -> List("", "" + barrier, "", "", "")
               else
                 ind -> List("|",
                             "" + barrier,
                             "|",
                             "V",
                             SimpleAPI pp states(ind))
             }).toMap
          )
        case CEXTimeElapse(_, (delayNum, delayDenom)) =>
          println("Delay: " + (delayNum.toDouble / delayDenom.toDouble))
      }

      lastStates = step.newStates
    }
    println("-" * totalWidth)
    println("Final:")
    asColumns(cex.last.newStates)
    println("-" * totalWidth)
  }

  private def diagonalInvariants(n : Int) : Seq[Seq[Int]] =
    for (i <- 0 until n)
    yield ((List tabulate n) { j => if (i == j) 1 else 0 })

}

////////////////////////////////////////////////////////////////////////////////

class VerificationLoop(system : ParametricEncoder.System,
                       initialInvariants : Seq[Seq[Int]] = null) {

  import VerificationLoop._
  import ParametricEncoder._
  import VerificationHints._
  import HornClauses.{Clause, FALSE}
  import Util._

  val result = {
    val processNum = system.processes.size

    var invariants : Seq[Seq[Int]] =
      initialInvariants match {
        case null =>
          diagonalInvariants(processNum)
        case invs => {
          assert(invs forall { v => v.size == processNum &&
                                    (v forall (_ >= 0)) &&
                                    ((v zip system.processes) forall {
                                      case (s, (_, Singleton)) => s <= 1
                                      case _                   => true
                                    }) })
          invs
        }
      }

    var res : Either[Unit, Counterexample] = null

    while (res == null) {

    println
    println("Using invariants " + (invariants mkString ", "))
    println

    val encoder =  new ParametricEncoder (system, invariants)

    ////////////////////////////////////////////////////////////////////////////

    if (GlobalParameters.get.printIntermediateClauseSets) {
      val basename = GlobalParameters.get.fileName
      val suffix =
        (for (inv <- invariants) yield (inv mkString "_")) mkString "--"
      val filename = basename + "-" + suffix + ".smt2"

      println
      println("Writing Horn clauses to " + filename)

      val out = new java.io.FileOutputStream(filename)
      Console.withOut(out) {
        val clauseFors =
          for (c <- encoder.allClauses) yield {
            val f = c.toFormula
            // eliminate remaining operators like eps
            Transform2Prenex(EquivExpander(PartialEvaluator(f)))
          }

        val allPredicates =
          HornClauses allPredicates encoder.allClauses

        SMTLineariser("C_VC", "HORN", "unknown",
                      List(), allPredicates.toSeq.sortBy(_.name),
                      clauseFors)
      }
      out.close
    }

    ////////////////////////////////////////////////////////////////////////////

    println

    val preprocessor = new DefaultPreprocessor
    val (simpClauses, simpHints, backTranslator) =
      Console.withErr(Console.out) {
        preprocessor.process(encoder.allClauses, encoder.globalHints)
      }

    val params =
      if (GlobalParameters.get.templateBasedInterpolationPortfolio)
        GlobalParameters.get.withAndWOTemplates
      else
        List()

      //Select hints by Edarica
      import lazabs.horn.concurrency.HintsSelection
      //HintsSelection.tryAndTestSelecton(encoder,simpHints,simpClauses)



      //Initial hints ID and store to file
      //val InitialHintsWithID=initialIDForHints(encoder.globalHints) //ID:head->hint
      //Call python to select hints

      //No hints selection
      var optimizedHints=HintsSelection.sortHints(simpHints) //if there is no readHints flag, use simpHints

      if(GlobalParameters.get.readHints==true){
        //Read selected hints from file (NNs)
        println("simpHints:")
        simpHints.pretyPrintHints()
        optimizedHints=HintsSelection.readHintsIDFromFile(GlobalParameters.get.fileName,simpHints,rank="rank:"+GlobalParameters.get.rank.toString)
        // inconsistency between encoder.globalHints and simpHints
      }

      //get smt
      if(GlobalParameters.get.getSMT2==true){
        HintsSelection.writeSMTFormatToFile(encoder.allClauses,"regression-tests/smt-graph/")  //write smt2 format to file
        println(encoder.allClauses)
      }
      //get horn clauses
      if(GlobalParameters.get.getHornGraph==true){
        //val InitialHintsWithID=initialIDForHints(optimizedHints) //ID:head->hint
        //val fileName = GlobalParameters.get.fileName.substring(GlobalParameters.get.fileName.lastIndexOf("/") + 1)
        //writeHintsWithIDToFile(InitialHintsWithID, fileName, "initial")//write hints and their ID to file

        DrawHornGraph.writeHornClausesGraphToFile(GlobalParameters.get.fileName,simpClauses,optimizedHints) //write horn graph and gn input to file

        //val argumentList=(for (p <- HornClauses.allPredicates(simpClauses)) yield (p, p.arity)).toList
        //HintsSelection.writeArgumentScoreToFile(GlobalParameters.get.fileName,argumentList,optimizedHints,countOccurrence = false)
        sys.exit()
      }



      ////debug/////
    val predAbsResult = ParallelComputation(params) {
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
              loopDetector hints2AbstractionRecord optimizedHints

            println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

            AbstractionRecord.mergeMaps(Map(), hintsAbstractionMap)//autoAbstractionMap

          }

        TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
          abstractionMap,
          GlobalParameters.get.templateBasedInterpolationTimeout) //if abstract:off still generate hints?
      } else {
        DagInterpolator.interpolatingPredicateGenCEXAndOr _
      }

      println("-------------------Test optimized hints---------------------------------")
      println
      println(
         "----------------------------------- CEGAR --------------------------------------")
      if(GlobalParameters.get.templateBasedInterpolation==false){
        val exceptionalPredGen: Dag[AndOrNode[HornPredAbs.NormClause, Unit]] =>
          Either[Seq[(Predicate, Seq[Conjunction])],
            Dag[(IAtom, HornPredAbs.NormClause)]] =
          (x: Dag[AndOrNode[HornPredAbs.NormClause, Unit]]) =>
            //throw new RuntimeException("interpolator exception")
            throw lazabs.Main.TimeoutException

        new HornPredAbs(simpClauses,
          Map(),//need Map[Predicate, Seq[IFormula]]
          exceptionalPredGen).result
      }else{
        println("Use hints:")
        optimizedHints.pretyPrintHints()

        new HornPredAbs(simpClauses,
          optimizedHints.toInitialPredicates,//need Map[Predicate, Seq[IFormula]]
          interpolator).result
      }

    }

    ////////////////////////////////////////////////////////////////////////////

    predAbsResult match {
      case Right(rawCEX) => {
        if (GlobalParameters.get.log)
          println("Not solvable")

        val cex = backTranslator translate rawCEX
        HornWrapper.verifyCEX(cex, encoder.allClauses)

        // check whether the counterexample is good enough to
        // reconstruct a genuine counterexample to system correctness
        if (cex.subdagIterator forall {
              case DagNode((_, clause), List(1), _) =>
                (encoder.symmetryTransitions contains clause) ||
                (encoder.localTransitions exists (_._1 == clause)) ||
                (encoder.sendReceiveTransitions exists (_._1 == clause)) ||
                (encoder.timeElapseTransitions contains clause) ||
                (encoder.assertionTransitions exists (_._1 == clause)) ||
                (encoder.barrierTransitions exists (_._1 == clause))
              case DagNode((_, clause), List(), DagEmpty) =>
                (encoder.initTransitions exists (_._1 == clause))
              case _ =>
                false
            }) {

          import system.globalVarNum

          //////////////////////////////////////////////////////////////////////

          var currentStates : Array[IAtom] = null

          def findModifiedIndexes(newStates : Seq[IAtom]) : (List[Int], List[IAtom]) = {
            val remaining = new ArrayBuffer[(IAtom, Int)]
            val unmatched = new ArrayBuffer[IAtom]
            remaining ++= currentStates.iterator.zipWithIndex
            for (a@IAtom(p, pArgs) <- newStates) {
              val i = remaining indexWhere {
                case (IAtom(q, qArgs), _) =>
                  p == q && (pArgs drop globalVarNum) == (qArgs drop globalVarNum)
              }
              if (i >= 0)
                remaining remove i
              else
                unmatched += a
            }
            ((remaining.iterator map (_._2)).toList, unmatched.toList)
          }

          def updateGlobalVars(newGlobalVars : Seq[ITerm]) : Unit =
            for (i <- 0 until currentStates.size) {
              val IAtom(p, args) = currentStates(i)
              currentStates(i) = IAtom(p, newGlobalVars ++ (args drop globalVarNum))
            }

          //////////////////////////////////////////////////////////////////////

          val cexTrace =
            (for ((atom@IAtom(globalPred, _), clause) <- cex.iterator.toSeq.reverse;
                   if (globalPred != HornClauses.FALSE &&
                       !(encoder.symmetryTransitions contains clause))) yield {
               val localAtoms = encoder decodeLocalStates atom

               val res =
               (for ((_, systemClauses) <-
                      encoder.initTransitions find (_._1 == clause)) yield {
                  assert((systemClauses.size == localAtoms.size) &&
                         ((systemClauses.iterator zip localAtoms.iterator) forall {
                            case (Clause(IAtom(a, _), _, _), IAtom(b, _)) => a == b
                          }))
                  currentStates = localAtoms.toArray
                  CEXInit(localAtoms, systemClauses)

                }) orElse (

                for ((_, systemClause@Clause(IAtom(headP, _), _, _)) <-
                      encoder.localTransitions find (_._1 == clause)) yield {

                  findModifiedIndexes(localAtoms) match {

                    case (Seq(), Seq()) => {

                      // we need to find out which of the local states are
                      // modified by which transition (clause)
    
                      val preIndex = SimpleAPI.withProver { p =>
                        import p._
                        import IExpression._
    
                        val pre = createFunction("pre", 2)
                        val post = createFunction("post", 2)
                        val preIndex, postIndex = createConstant
    
                        for ((IAtom(_, args), i) <-
                               currentStates.iterator.zipWithIndex;
                             (v, j) <- args.iterator.zipWithIndex)
                          !! (pre(i, j) === v)
                        for ((IAtom(_, args), i) <-
                               localAtoms.iterator.zipWithIndex;
                             (v, j) <- args.iterator.zipWithIndex)
                          !! (post(i, j) === v)
    
                        val (Clause(IAtom(headP, headArgs),
                                    List(IAtom(bodyP, bodyArgs)),
                                    constraint),
                             newConsts) = systemClause.refresh
                        addConstants(newConsts)

                        !! (or(for ((IAtom(`bodyP`, _), j) <-
                                      currentStates.iterator.zipWithIndex)
                               yield (preIndex === j)))
    
                        !! (or(for ((IAtom(`headP`, _), j) <-
                                      localAtoms.iterator.zipWithIndex)
                               yield (postIndex === j)))

                        !! (constraint)

                        for ((e, j) <- bodyArgs.iterator.zipWithIndex)
                          !! (pre(preIndex, j) === e)
                        for ((e, j) <- headArgs.iterator.zipWithIndex)
                          !! (post(postIndex, j) === e)
    
                        ???
                        assert(??? == ProverStatus.Sat)
    
                        eval(preIndex)
                      }

                      updateGlobalVars(localAtoms.head.args take globalVarNum)
                      CEXLocalStep(currentStates.toList, preIndex.intValueSafe, systemClause)
                    }

                    case (List(index), List(newState@IAtom(_, newArgs))) => {
                      currentStates(index) = newState
                      updateGlobalVars(newArgs take globalVarNum)

                      CEXLocalStep(currentStates.toList, index, systemClause)
                    }
                  }

                }) orElse (

                for ((_, (sendClause@Clause(IAtom(newSendP, _),
                                            List(IAtom(oldSendP, _)), _),
                          receiveClause@Clause(IAtom(newRecP, _),
                                               List(IAtom(oldRecP, _)), _),
                          commChannel)) <-
                      encoder.sendReceiveTransitions find (_._1 == clause)) yield {

                  // right now we assume exactly two states were
                  // modified; this is not always the case.
                  // TODO: generalise

                  val (List(index1, index2),
                       List(newState1@IAtom(newP1, newArgs1),
                            newState2@IAtom(newP2, _))) =
                    findModifiedIndexes(localAtoms)

                  assert(oldSendP != oldRecP &&
                         Set(newSendP, newRecP) == Set(newP1, newP2))

                  val (senderIndex, receiverIndex) =
                    if (oldSendP == currentStates(index1).pred)
                      (index1, index2)
                    else
                      (index2, index1)

                  updateGlobalVars(newArgs1 take globalVarNum)

                  if (newSendP == newP1) {
                    currentStates(senderIndex) = newState1
                    currentStates(receiverIndex) = newState2
                    CEXCommStep(currentStates.toList, commChannel,
                                senderIndex, sendClause,
                                receiverIndex, receiveClause)
                  } else {
                    currentStates(senderIndex) = newState2
                    currentStates(receiverIndex) = newState1
                    CEXCommStep(currentStates.toList, commChannel,
                                senderIndex, sendClause,
                                receiverIndex, receiveClause)
                  }

                }) orElse (

                for ((_, (barrierClauses, barrier)) <-
                      encoder.barrierTransitions find (_._1 == clause)) yield {

                  // we need to find out which of the local states are
                  // modified by which transition (clause)

                  val clauseIndexes = SimpleAPI.withProver { p =>
                    import p._
                    import IExpression._

                    val pre = createFunction("pre", 2)
                    val post = createFunction("post", 2)
                    val preIndex, postIndex = createConstants(barrierClauses.size)

                    for ((IAtom(_, args), i) <-
                           currentStates.iterator.zipWithIndex;
                         (v, j) <- args.iterator.zipWithIndex)
                      !! (pre(i, j) === v)
                    for ((IAtom(_, args), i) <-
                           localAtoms.iterator.zipWithIndex;
                         (v, j) <- args.iterator.zipWithIndex)
                      !! (post(i, j) === v)

                    for (((c, d), clause@Clause(IAtom(headP, _), List(IAtom(bodyP, _)), _)) <-
                           (preIndex.iterator zip postIndex.iterator) zip
                             barrierClauses.iterator) {

                      !! (or(for ((IAtom(`bodyP`, _), j) <-
                                    currentStates.iterator.zipWithIndex)
                             yield (c === j)))

                      !! (or(for ((IAtom(`headP`, _), j) <-
                                    localAtoms.iterator.zipWithIndex)
                             yield (d === j)))

                      val (Clause(IAtom(_, headArgs), List(IAtom(_, bodyArgs)),
                                  constraint),
                           newConsts) = clause.refresh
                      addConstants(newConsts)

                      !! (constraint)
                      for ((e, j) <- bodyArgs.iterator.zipWithIndex)
                        !! (pre(c, j) === e)
                      for ((e, j) <- headArgs.iterator.zipWithIndex)
                        !! (post(d, j) === e)
                    }

                    !! (distinct(preIndex))
                    !! (distinct(postIndex))

                    ???
                    assert(??? == ProverStatus.Sat)

                    (for (((c, d), clause) <-
                            (preIndex.iterator zip postIndex.iterator) zip
                              barrierClauses.iterator) yield {
                       val oldIndex = eval(c).intValueSafe
                       val newIndex = eval(d).intValueSafe
                       currentStates(oldIndex) = localAtoms(newIndex)
                       (oldIndex, clause)
                     }).toList
                  }

                  CEXBarrierStep(currentStates.toList, barrier, clauseIndexes)

                }) orElse (

                for (_ <-
                     encoder.timeElapseTransitions find (_ == clause)) yield {

                  val oldGlobal = currentStates(0).args take globalVarNum
                  val newGlobal = localAtoms.head.args take globalVarNum
                  val delay = system.timeSpec match {
                    case NoTime => {
                      assert(false)
                      (-1, 1)
                    }
                    case DiscreteTime(index) =>
                      (newGlobal(index).asInstanceOf[IIntLit].value.intValueSafe -
                       oldGlobal(index).asInstanceOf[IIntLit].value.intValueSafe, 1)
                    case ContinuousTime(num, denom) =>
                      (newGlobal(num).asInstanceOf[IIntLit].value.intValueSafe -
                       oldGlobal(num).asInstanceOf[IIntLit].value.intValueSafe,
                       oldGlobal(denom).asInstanceOf[IIntLit].value.intValueSafe)
                  }

                  updateGlobalVars(newGlobal)
                  CEXTimeElapse(currentStates.toList, delay)

                }) getOrElse {

                  throw new Exception("Could not recognise the clause: " + clause)

                }

               assert(currentStates.toSet == localAtoms.toSet)

               res

             }).toList

        
          if (GlobalParameters.get.log) {
            println
            prettyPrint(cexTrace)
            println
          }

          res = Right(cexTrace)

        } else {

          // we have to refine the chosen invariant schema
          val processes =
            (for ((atom@IAtom(globalPred, _), _) <- cex.iterator;
                  if (globalPred != FALSE);
                  localAtom <- (encoder decodeLocalStates atom).iterator) yield {
              val IAtom(pred, args) = localAtom
              val processIndex = system.localPredsSet indexWhere (_ contains pred)
              system.processes(processIndex) match {
                case (_, Singleton) => (processIndex, 0)
                case (_, Infinite)  => (processIndex, args(system.globalVarNum))
              }
             }).toSet

          if (GlobalParameters.get.log) {
            println
            println("Raw counterexample:")
            (cex map (_._1)).prettyPrint

            println
            println("Involved processes:")
            for ((process, id) <- processes) {
              print("Process index: " + process)
              system.processes(process) match {
                case (_, Singleton) => println
                case (_, Infinite)  => println(", id: " + id)
              }
            }
          } else {
            println("Unsat, trying again with higher precision ...")
          }

          invariants =
          (invariants indexWhere { inv =>
             processes forall { case (i, _) => inv(i) > 0 } }) match {
            case -1 => {
              // merge two invariants
              val relevantInvs = invariants filter { inv =>
                processes exists { case (i, _) => inv(i) > 0 } } sortBy (_.sum)
              assert(relevantInvs.size >= 2)

              val newInv = for ((a, b) <- relevantInvs(0) zip relevantInvs(1))
                           yield (a + b)

              List(newInv) ++ (for (inv <- invariants;
                                    if (inv != relevantInvs(0) && inv != relevantInvs(1)))
                               yield inv)
            }
            case invIndex =>
              // increase arity of this invariant
              val oldInv = invariants(invIndex)

              val infProcesses = processes filter {
                case (i, _) => system.processes(i)._2 == Infinite }
              assert(!infProcesses.isEmpty)
              val (chosenProcess, _) =
                (for ((ind, ids) <- infProcesses groupBy (_._1);
                      if (oldInv(ind) < ids.size))
                 yield (ind, ids.size)).toSeq maxBy (_._2)

              val newInv = oldInv.updated(chosenProcess, oldInv(chosenProcess) + 1)

              invariants.updated(invIndex, newInv)
          }

        }

//        cex.prettyPrint
      }

      case Left(rawSol) => {
        if (GlobalParameters.get.log) {
          println("Solution:")
          val solution = backTranslator translate rawSol
          HornWrapper.verifySolution(solution, encoder.allClauses)

          for ((p, f) <- solution)
            println("" + p + ": " + f)
          println
        }
        res = Left(())
      }
    }

    }

    res
  }

}
