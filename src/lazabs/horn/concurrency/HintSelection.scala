package lazabs.horn.concurrency
import java.io.{File, PrintWriter}

import ap.terfor.preds.Predicate
import ap.terfor._
import ap.parser._
import lazabs.GlobalParameters
import lazabs.horn.abstractions.StaticAbstractionBuilder
import lazabs.horn.bottomup.{HornPredAbs, TemplateInterpolator}
import lazabs.horn.preprocessor.HornPreprocessor
import lazabs.horn.preprocessor.HornPreprocessor._


object HintsSelection{

  def tryAndTestSelecton(encoder:ParametricEncoder,simpHints:VerificationHints,simpClauses:Clauses,file:String):VerificationHints = {
    val fileName=file.substring(file.lastIndexOf("/")+1)

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

    //val timeOut=GlobalParameters.get.threadTimeout //timeout
    val timeOut=10
    val criticalHeads=simpHints
    //val criticalHeads = currentHeads
    //println("numberOfCriticalHeads:"+criticalHeads.numberOfHeads())
    //println("Current heads:")
    //criticalHeads.printHints()
    //println("-----------------------------------Heads selection end ------------------------------------")
    val emptyHints=VerificationHints(Map())
    var criticalHints = simpHints
    var optimizedHints=VerificationHints(Map()) // store final selected heads and hints
    var InitialHintsWithID=initialIDForHints(simpHints)
    var PositiveHintsWithID=Map("initialKey"->"")
    var NegativeHintsWithID=Map("initialKey"->"")


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
            criticalHints= criticalHints.addPredicateHints(Map(oneHintKey->currentHintsList)) //add head with one hint back
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

              // not timeout ...
              println("Delete a redundant hint:\n"+oneHintKey+"\n"+oneHint)
              redundantHintsList=redundantHintsList ++ Seq(oneHint)

              for((key,value)<-InitialHintsWithID){ //add useless hint to NegativeHintsWithID
                val tempkey=key.toString.substring(key.toString.indexOf(":")+1,key.toString().lastIndexOf(":"))
                if(oneHintKey.toString()==tempkey && value.toString==oneHint.toString){
                  NegativeHintsWithID++= Map(key->value)
                }
              }


            }
          } catch {// ,... Main.TimeoutException
            //time out
            case lazabs.Main.TimeoutException =>
              println("Add a critical hint\n"+oneHintKey+"\n"+oneHint)
              criticalHintsList = criticalHintsList ++ Seq(oneHint)
              criticalHints=criticalHints.filterNotPredicates(GSet(oneHintKey))
              criticalHints=criticalHints.addPredicateHints(Map(oneHintKey->beforeDeleteHints))
              for((key,value)<-InitialHintsWithID){ //add useful hint to PositiveHintsWithID
                val tempkey=key.toString.substring(key.toString.indexOf(":")+1,key.toString().lastIndexOf(":"))
                if(oneHintKey.toString()==tempkey && value.toString==oneHint.toString){
                  PositiveHintsWithID++= Map(key->value)
                }
              }
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


      writeHintsWithIDToFile(InitialHintsWithID,fileName,"initial")//write hints and their ID to file
      writeHintsWithIDToFile(PositiveHintsWithID,fileName,"positive")
      writeHintsWithIDToFile(NegativeHintsWithID,fileName,"negative")

      return optimizedHints

    }

  }
  def writeHintsWithIDToFile(hints:Map[String,String],fileName:String,hintType:String){
    val tempHints=hints-"initialKey"
    if(hintType=="initial"){
      val writer = new PrintWriter(new File("trainData/"+fileName+".initialHints"))
      for((key,value)<-tempHints){
        writer.write(key+value+"\n")
      }
      writer.close()
    }
    if(hintType=="positive"){
      val writer = new PrintWriter(new File("trainData/"+fileName+".positiveHints"))
      for((key,value)<-tempHints){
        writer.write(key+value+"\n")
      }
      writer.close()
    }
    if(hintType=="negative"){
      val writer = new PrintWriter(new File("trainData/"+fileName+".negativeHints"))
      for((key,value)<-tempHints){
        writer.write(key+value+"\n")
      }
      writer.close()
    }

  }

  def initialIDForHints(simpHints:VerificationHints): Map[String,String] ={
    var HintsIDMap=Map("initialKey"->"")
    var counter=0

    for((head,templateList)<-simpHints.getPredicateHints()) { //loop for head
      val temphead=head.toString().substring(0,head.toString().lastIndexOf("/")) //delete /number after main

      for(oneHint <- templateList) { //loop for every template in the head
        HintsIDMap ++= Map(counter.toString+":"+head.toString()+":"->oneHint.toString) //map(hint->ID)
        counter=counter+1
      }
    }
    HintsIDMap=HintsIDMap-"initialKey"
    return HintsIDMap

  }


  def neuralNetworkSelection(encoder:ParametricEncoder,simpHints:VerificationHints,simpClauses:Clauses):VerificationHints = {
    //write redundant hints to JSON

    //call NNs

    //read predicted hints from JSON

    //write to optimized Hints

    val optimizedHints=simpHints
    return optimizedHints
  }
  def readHintsFromJSON(fileName:String):VerificationHints = {

    //Read JSON
    import scala.io.Source
    import scala.util.parsing.json._
    val fname = "JSON/"+fileName+".json"

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
      case None           => println("observations JSON invalid")
      case Some(elements:Map[String,List[String]]) => {
        //println(elements)
        for((key,list)<-elements){
          println(key+"/"+list.length)
          for(value<-list){
            println(" " +value)
          }

        }


      }
    }

    //JSON to Map[IExpression.Predicate, Seq[VerifHintElement]
    //VerifHintInitPred
    //VerifHintTplPred
    //VerifHintTplEqTerm
    var optimizedHints=VerificationHints(Map())
    val head="main1"
    val arity=1
    val h=new IExpression.Predicate(head,arity)
    val h1=new IExpression.Predicate("main2",2)


    val Term="_0,10000"
    val predicate="_3 + -1 * _4) >= 0"
    val element=VerifHintTplEqTerm(new IConstant(new ConstantTerm("sss")),10000)
//    val element1=VerifHintInitPred(IFomula())
    var hintList:Seq[VerifHintElement]=Seq()
    hintList= hintList ++ Seq(element)
    hintList= hintList ++ Seq(element)



    optimizedHints=optimizedHints.addPredicateHints(Map(h->hintList))
    optimizedHints=optimizedHints.addPredicateHints(Map(h1->hintList))
    println("input template:")
    optimizedHints.pretyPrintHints()


    return optimizedHints
  }
  def readHintsIDFromJSON(fileName:String,originalHints:VerificationHints):VerificationHints = {
//    for((key,value)<-originalHints){
//      for(v<-value){
//      }
//    }


    var readHints=VerificationHints(Map())

    return readHints
  }

  def printHornClauses(system : ParametricEncoder.System,file:String): Unit ={
    println("Write horn to file")
    println(file.substring(file.lastIndexOf("/")+1))
    val fileName=file.substring(file.lastIndexOf("/")+1)
    val writer = new PrintWriter(new File("trainData/"+fileName+".horn"))
    for ((p, r) <- system.processes) {
      r match {
        case ParametricEncoder.Singleton =>
        case ParametricEncoder.Infinite =>
          println("  Replicated thread:")
      }
      for ((c, sync) <- p) {
        val prefix = "    " + c.toPrologString
        //print(prefix + (" " * ((50 - prefix.size) max 2)))
        writer.write(prefix + (" " * ((50 - prefix.size) max 2))+"\n")
        sync match {
          case ParametricEncoder.Send(chan) =>
            println("chan_send(" + chan + ")")
          case ParametricEncoder.Receive(chan) =>
            println("chan_receive(" + chan + ")")
          case ParametricEncoder.NoSync =>
            println
        }
      }
    }
    if (!system.assertions.isEmpty) {
      println
      //println("Assertions:")
      writer.write("Assertions:\n")
      for (c <- system.assertions)
        //println("  " + c.toPrologString)
        writer.write("  " + c.toPrologString + "\n")
    }

    writer.close()
  }


}
