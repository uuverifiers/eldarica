package lazabs.horn.concurrency

import lazabs.GlobalParameters
import lazabs.horn.abstractions.StaticAbstractionBuilder
import lazabs.horn.bottomup.{HornPredAbs, TemplateInterpolator}
import lazabs.horn.preprocessor.HornPreprocessor
import lazabs.horn.preprocessor.HornPreprocessor._


object HintsSelection{

  def tryAndTestSelecton(encoder:ParametricEncoder,simpHints:VerificationHints,simpClauses:Clauses):VerificationHints = {


    //println("\n------ DEBUG-Select critical hints begin -------------")
    import HornPreprocessor.{VerifHintElement, VerificationHints,
      EmptyVerificationHints, BackTranslator,InitPredicateVerificationHints}

    import ap.parser._
    import IExpression._
    import scala.collection.{Set => GSet}
    import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
      LinkedHashSet, ArrayBuffer}
    import lazabs.horn.bottomup.HornClauses
    import lazabs.horn.global._

    import scala.concurrent.duration._
    import scala.concurrent.{Await, Future}
    import scala.util.control.Breaks._
    import scala.concurrent.ExecutionContext.Implicits.global
    import java.lang.System.currentTimeMillis
    //import java.util.concurrent.TimeoutException
    import lazabs.Main

    import lazabs.horn.concurrency.GraphTranslator

    val timeOut=GlobalParameters.get.threadTimeout //timeout
    //    val numberOfHeads=simpHints.numberOfHeads
    //    println("NumberOfHeads:"+numberOfHeads)
    //    println("Loop begins")
    //    var criticalHeadsList : GSet[IExpression.Predicate] = GSet()
    //    var redundantHeadsList : GSet[IExpression.Predicate]=  GSet()
    //    var currentHeads = VerificationHints(simpHints.getPredicateHints())
    //    for((oneHintKey,oneHintValue)<-simpHints.getPredicateHints){
    //
    //      println("Try ro delete head:")
    //      println(oneHintKey)
    //      //println(oneHintValue)
    //
    //      val currentHint = currentHeads.filterNotPredicates(GSet(oneHintKey))
    //      println("Current heads:")
    //      currentHint.printHints()
    //      val predAbsResult = ParallelComputation(params) {
    //
    //        val interpolator = if (GlobalParameters.get.templateBasedInterpolation)
    //                                 Console.withErr(Console.out) {
    //          val builder =
    //            new StaticAbstractionBuilder(
    //              simpClauses,
    //              GlobalParameters.get.templateBasedInterpolationType)
    //          val autoAbstractionMap =
    //            builder.abstractions mapValues (TemplateInterpolator.AbstractionRecord(_))
    //
    //          val abstractionMap =
    //            if (encoder.globalPredicateTemplates.isEmpty) {
    //              autoAbstractionMap
    //            } else {
    //              val loopDetector = builder.loopDetector
    //
    //              print("Using interpolation templates provided in program: ")
    //
    //
    //              //////////////////////////////////////////DEBUG/////////////////////
    //
    //              val hintsAbstractionMap =
    //                loopDetector hints2AbstractionRecord currentHint
    //                //DEBUG
    //
    //              println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")
    //
    //              TemplateInterpolator.AbstractionRecord.mergeMaps(
    //                autoAbstractionMap, hintsAbstractionMap)
    //            }
    //
    //          TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
    //            abstractionMap,
    //            GlobalParameters.get.templateBasedInterpolationTimeout)
    //        } else {
    //          DagInterpolator.interpolatingPredicateGenCEXAndOr _
    //        }
    //
    //        println
    //        println(
    //           "----------------------------------- CEGAR --------------------------------------")
    //        val deadline = timeOut.seconds.fromNow
    //        //val timeout = Future{Thread.sleep(20*1000)} // 20 seconds
    //        val threadCEGAR = new Thread {
    //            override def run {
    //              new HornPredAbs(simpClauses,// loop
    //                currentHint.toInitialPredicates,
    //                interpolator).result
    //                // custom behavior here
    //            }
    //        }
    //        threadCEGAR.start
    //        threadCEGAR.join(timeOut*1000)
    //        if(!deadline.hasTimeLeft){
    //          println("Timeout")
    //          threadCEGAR.stop()
    //          println("Add a critical head")
    //          criticalHeadsList=criticalHeadsList ++ GSet(oneHintKey)
    //        }
    //        if(deadline.hasTimeLeft){
    //          println("Add a redundant head")
    //          //redundantHints.add(GSet(oneHintKey))
    //          redundantHeadsList=redundantHeadsList ++ GSet(oneHintKey)
    //          println("Delete the redundant head")
    //          currentHeads=currentHeads.filterNotPredicates(GSet(oneHintKey))
    //        }
    //
    //      }
    //    }

    val criticalHeads=simpHints
    //val criticalHeads = currentHeads
    //println("numberOfCriticalHeads:"+criticalHeads.numberOfHeads())
    //println("Current heads:")
    //criticalHeads.printHints()
    //println("-----------------------------------Heads selection end ------------------------------------")
    val emptyHints=VerificationHints(Map())
    var criticalHints = simpHints
    var optimizedHints=VerificationHints(Map()) // store final selected heads and hints


    if(simpHints.isEmpty || lazabs.GlobalParameters.get.templateBasedInterpolation==false) {
      println("simpHints is empty or abstract:off")
      return simpHints}
    else{
      println("-------------------------Hints selection begins------------------------------------------")
      for((oneHintKey,oneHintValue)<-criticalHeads.getPredicateHints()){ //loop for head
        println("Head:"+oneHintKey)
        println(oneHintValue)
        var criticalHintsList:Seq[VerifHintElement]=Seq()
        var redundantHintsList:Seq[VerifHintElement]=Seq()
        var currentHintsList = criticalHeads.getValue(oneHintKey) //extract hints in this head

        for(oneHint<-criticalHeads.getValue(oneHintKey)){ //loop for every hint in one head
          println("Current hints:")
          criticalHints.pretyPrintHints()
          val beforeDeleteHints = currentHintsList //record hint list before the hint is deleted
          currentHintsList = currentHintsList.filter(_ != oneHint) //delete one hint from hint list
          println("Try to delete: \n" + oneHintKey+" \n"+ oneHint)

          criticalHints=criticalHints.filterNotPredicates(GSet(oneHintKey)) //delete the head
          if(!currentHintsList.isEmpty){
            criticalHints= criticalHints.addPredicateHints(Map(oneHintKey->currentHintsList)) //add head with one hint deleted
          }
          println("After delete:\n")
          criticalHints.pretyPrintHints()

          val startTime = currentTimeMillis

          val toParams = GlobalParameters.get.clone
          toParams.timeoutChecker = () => {
            if ((currentTimeMillis - startTime)> timeOut*1000) //timeout milliseconds
              throw lazabs.Main.TimeoutException //Main.TimeoutException
          }

          try {
            GlobalParameters.parameters.withValue(toParams) {
              val interpolator =
                Console.withErr(Console.out) {
                  val builder =
                    new StaticAbstractionBuilder(
                      simpClauses,
                      GlobalParameters.get.templateBasedInterpolationType)
                  //     val autoAbstractionMap =
                  //       builder.abstractions mapValues (TemplateInterpolator.AbstractionRecord(_))

                  val abstractionMap =
                  {
                    val loopDetector = builder.loopDetector

                    print("Using interpolation templates provided in program: ")


                    val hintsAbstractionMap =
                      loopDetector hints2AbstractionRecord criticalHints //emptyHints
                    //DEBUG

                    println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

                    TemplateInterpolator.AbstractionRecord.mergeMaps(
                      Map(), hintsAbstractionMap) //autoAbstractionMap
                  }

                  TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
                    abstractionMap,
                    GlobalParameters.get.templateBasedInterpolationTimeout)
                }

              println
              println(
                "----------------------------------- CEGAR --------------------------------------")

              new HornPredAbs(simpClauses, // loop
                criticalHints.toInitialPredicates, //emptyHints
                interpolator).result

              // no timeout ...
              println("Delete a redundant hint:\n"+oneHintKey+"\n"+oneHint)
              redundantHintsList=redundantHintsList ++ Seq(oneHint)
            }
          } catch {// ,... Main.TimeoutException
            case lazabs.Main.TimeoutException =>
              println("Add a critical hint\n"+oneHintKey+"\n"+oneHint)
              criticalHintsList = criticalHintsList ++ Seq(oneHint)
              criticalHints=criticalHints.filterNotPredicates(GSet(oneHintKey))
              criticalHints=criticalHints.addPredicateHints(Map(oneHintKey->beforeDeleteHints))
          }

          /*

          val deadline = timeOut.seconds.fromNow //record time begin
          val threadCEGAR = new Thread { //new thread
            override def run {
              val predAbsResult = ParallelComputation(params) {

                val interpolator = if (GlobalParameters.get.templateBasedInterpolation)
                  Console.withErr(Console.out) {
                    val builder =
                      new StaticAbstractionBuilder(
                        simpClauses,
                        GlobalParameters.get.templateBasedInterpolationType)
                    val autoAbstractionMap =
                      builder.abstractions mapValues (TemplateInterpolator.AbstractionRecord(_))

                    val abstractionMap =
                      if (encoder.globalPredicateTemplates.isEmpty) {
                        autoAbstractionMap
                      } else {
                        val loopDetector = builder.loopDetector

                        print("Using interpolation templates provided in program: ")


                        //////////////////////////////////////////DEBUG/////////////////////

                        val hintsAbstractionMap =
                          loopDetector hints2AbstractionRecord criticalHints //emptyHints
                        //DEBUG

                        println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

                        TemplateInterpolator.AbstractionRecord.mergeMaps(
                          Map(), hintsAbstractionMap) //autoAbstractionMap
                      }

                    TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
                      abstractionMap,
                      GlobalParameters.get.templateBasedInterpolationTimeout)
                  } else {
                  DagInterpolator.interpolatingPredicateGenCEXAndOr _
                }

                println
                println(
                  "----------------------------------- CEGAR --------------------------------------")

                new HornPredAbs(simpClauses,// loop
                  criticalHints.toInitialPredicates, //emptyHints
                  interpolator).result

              }
            }
          }
          threadCEGAR.start
          threadCEGAR.join(timeOut*1000)
          //threadCEGAR.stop()
          if (threadCEGAR.isAlive) {threadCEGAR.interrupt()}
          */

          println
          //          if(!deadline.hasTimeLeft){ //if timeout
          //            println("Timeout")
          //            threadCEGAR.stop()
          //            println("Add a critical hint\n"+oneHintKey+"\n"+oneHint)
          //            criticalHintsList = criticalHintsList ++ Seq(oneHint)
          //            criticalHints=criticalHints.filterNotPredicates(GSet(oneHintKey))
          //            criticalHints=criticalHints.addPredicateHints(Map(oneHintKey->beforeDeleteHints))
          //
          //          }else{
          //            println("Delete a redundant hint:\n"+oneHintKey+"\n"+oneHint)
          //            redundantHintsList=redundantHintsList ++ Seq(oneHint)
          //            //currentHintsList=currentHintsList.filter(_ != oneHint)
          //            //println("Current hints:\n"+oneHintKey+currentHintsList)
          //          }

          println("Current head:"+oneHintKey)
          println
          println("criticalHintsList"+criticalHintsList)
          println
          println("redundantHintsList"+redundantHintsList)
          println("---------------------------------------------------------------")
          //optimizedHints=optimizedHints.addPredicateHints(Map(oneHintKey->criticalHintsList))

        }
        if(!criticalHintsList.isEmpty){ //add critical hints in one head to optimizedHints map
          optimizedHints=optimizedHints.addPredicateHints(Map(oneHintKey->criticalHintsList))
        }
      }
      //optimizedHints=criticalHints

      println("\n------------DEBUG-Select critical hints end-------------------------")
      println("\nsimpHints Hints:")
      simpHints.pretyPrintHints()
      println("\nOptimized Hints:")
      println("!@@@@")
      optimizedHints.pretyPrintHints()
      println("@@@@!")
      println("timeout:"+GlobalParameters.get.threadTimeout)
      GlobalParameters.get.printHints=optimizedHints
      return optimizedHints

    }

  }

  def neuralNetworkSelection(encoder:ParametricEncoder,simpHints:VerificationHints,simpClauses:Clauses):VerificationHints = {
    //write redundant hints to JSON

    //call NNs

    //read predicted hints from JSON

    //write to optimized Hints

    val optimizedHints=simpHints
    return optimizedHints
  }


}
