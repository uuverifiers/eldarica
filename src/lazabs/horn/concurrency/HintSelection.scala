package lazabs.horn.concurrency

import ap.terfor.preds.Predicate
import ap.terfor._
import ap.parser.{IExpression, _}
import lazabs.GlobalParameters
import lazabs.horn.abstractions.{AbstractionRecord, StaticAbstractionBuilder, VerificationHints}
import lazabs.horn.bottomup.{DagInterpolator, HornClauses, HornPredAbs, TemplateInterpolator}
import lazabs.horn.concurrency.ParametricEncoder.{Infinite, Singleton}

import scala.collection.immutable.ListMap
import scala.io.Source
import scala.collection.mutable.Seq
import java.io.{File, FileWriter, PrintWriter}

import ap.parser._
import lazabs.horn.abstractions.VerificationHints._
import lazabs.horn.preprocessor.HornPreprocessor.Clauses

object HintsSelection{

  def tryAndTestSelecton(encoder:ParametricEncoder,simpHints:VerificationHints,simpClauses:Clauses,file:String,InitialHintsWithID:Map[String,String]):VerificationHints = {
    val fileName=file.substring(file.lastIndexOf("/")+1)

    //println("\n------ DEBUG-Select critical hints begin -------------")

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
    //val timeOut=10
    val criticalHeads=simpHints
    //val criticalHeads = currentHeads
    //println("numberOfCriticalHeads:"+criticalHeads.numberOfHeads())
    //println("Current heads:")
    //criticalHeads.printHints()
    //println("-----------------------------------Heads selection end ------------------------------------")
    val emptyHints=VerificationHints(Map())
    var criticalHints = simpHints
    var optimizedHints=VerificationHints(Map()) // store final selected heads and hints
    //val InitialHintsWithID=initialIDForHints(simpHints)
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
                            loopDetector hints2AbstractionRecord criticalHints //emptyHints
                          //DEBUG

                          println(hintsAbstractionMap.keys.toSeq sortBy (_.name) mkString ", ")

                          AbstractionRecord.mergeMaps(Map(), hintsAbstractionMap) //autoAbstractionMap
                        }

                      TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
                        abstractionMap,
                        GlobalParameters.get.templateBasedInterpolationTimeout)
                    }else {
                    DagInterpolator.interpolatingPredicateGenCEXAndOr _
                  }

                  println
                  println(
                    "----------------------------------- CEGAR --------------------------------------")

                  new HornPredAbs(simpClauses, // loop
                    criticalHints.toInitialPredicates, //emptyHints
                    interpolator).result

                  // not timeout ...
                  println("Delete a redundant hint:\n" + oneHintKey + "\n" + oneHint)
                  redundantHintsList = redundantHintsList ++ Seq(oneHint)

                  for ((key, value) <- InitialHintsWithID) { //add useless hint to NegativeHintsWithID
                    val tempkey = key.toString.substring(key.toString.indexOf(":") + 1, key.toString.length)
                    val oneHintKeyTemp = oneHintKey.toString().substring(0, oneHintKey.toString().indexOf("/"))
                    if (oneHintKeyTemp == tempkey && value.toString == oneHint.toString) {
                      NegativeHintsWithID ++= Map(key -> value)
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
                val tempkey=key.toString.substring(key.toString.indexOf(":")+1,key.toString.length)
                val oneHintKeyTemp=oneHintKey.toString().substring(0,oneHintKey.toString().indexOf("/"))
                if(oneHintKeyTemp==tempkey && value.toString==oneHint.toString){
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
      //println("\nsimpHints Hints:")
      //simpHints.pretyPrintHints()
      println("\nOptimized Hints:")
      println("!@@@@")
      optimizedHints.pretyPrintHints()
      println("@@@@!")
      println("timeout:"+GlobalParameters.get.threadTimeout)
      //GlobalParameters.get.printHints=optimizedHints


      if(optimizedHints.isEmpty){

      }else{//only write to file when optimized hint is not empty
        writeHintsWithIDToFile(InitialHintsWithID,fileName,"initial")//write hints and their ID to file
        writeHintsWithIDToFile(PositiveHintsWithID,fileName,"positive")
        writeHintsWithIDToFile(NegativeHintsWithID,fileName,"negative")
      }


      return optimizedHints

    }

  }
  def writeHintsWithIDToFile(hints:Map[String,String],fileName:String,hintType:String){
    val tempHints=hints-"initialKey"
    if(hintType=="initial"){
      //val writer = new PrintWriter(new File("trainData/"+fileName+".initialHints"))
      val writer = new PrintWriter(new File("../trainData/"+fileName+".initialHints")) //python path
      for((key,value)<-tempHints){
        writer.write(key+":"+value+"\n")
      }
      writer.close()
    }
    if(hintType=="positive"){
      //val writer = new PrintWriter(new File("trainData/"+fileName+".positiveHints"))
      val writer = new PrintWriter(new File("../trainData/"+fileName+".positiveHints")) //python path
      for((key,value)<-tempHints){
        writer.write(key+":"+value+"\n")
      }
      writer.close()
    }
    if(hintType=="negative"){
      //val writer = new PrintWriter(new File("trainData/"+fileName+".negativeHints"))
      val writer = new PrintWriter(new File("../trainData/"+fileName+".negativeHints")) //python path
      for((key,value)<-tempHints){
        writer.write(key+":"+value+"\n")
      }
      writer.close()
    }

  }

  def initialIDForHints(simpHints:VerificationHints): Map[String,String] ={
    //var HintsIDMap=Map("initialKey"->"")
    var HintsIDMap:Map[String,String]=Map()
    var counter=0

    for((head)<-simpHints.getPredicateHints().keys.toList) { //loop for head
      val temphead=head.toString().substring(0,head.toString().lastIndexOf("/")) //delete /number after main


      for(oneHint <- simpHints.getValue(head)) { //loop for every template in the head
        HintsIDMap ++= Map(counter.toString+":"+temphead.toString()->oneHint.toString) //map(ID:head->hint)
        counter=counter+1
      }
    }
    //HintsIDMap=HintsIDMap-"initialKey"

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
  def storeHintsToVerificationHints_binary(parsedHintslist:Seq[Seq[String]],readInitialHintsWithID:Map[String,String],originalHints:VerificationHints) ={
    //store read hints to VerificationHints
    println("---selected hints--")
    var readHints=VerificationHints(Map())
    var readHintsTemp:Map[IExpression.Predicate,VerifHintElement]=Map()
    var readHintsTempList:Seq[Map[IExpression.Predicate,VerifHintElement]]=Seq()
    var parsedHintsCount=0

    for(element<-parsedHintslist){
      //println(element)
      if(element(3).toFloat.toInt==1){ //element(3)==1 means useful, element(4) is score
      val head=element(1).toString//element(1) is head
      val hint=readInitialHintsWithID(element(0).toString+":"+element(1)).toString //InitialHintsWithID ID:head->hint
        for((key,value)<-originalHints.getPredicateHints()){
          val keyTemp=key.toString().substring(0,key.toString().indexOf("/"))
          if(head==keyTemp){
            var usfulHintsList:Seq[VerifHintElement]=Seq()
            for(oneHint<-originalHints.getValue(key)){
              if(keyTemp==head && oneHint.toString()==hint){ //match initial hints and hints from file to tell usefulness
                usfulHintsList=usfulHintsList ++ Seq(oneHint)//add this hint to usfulHintsList
                //println(element(0),usfulHintsList)
                readHintsTempList=readHintsTempList:+Map(key->oneHint)
                parsedHintsCount=parsedHintsCount+1
              }
            }
            //readHints=readHints.addPredicateHints(Map(key->usfulHintsList)) //add this haed->hint:Seq() to readHints
          }
        }
      }else{ }//useless hint

    }

    println("selected hint count="+parsedHintsCount)
    (readHints,readHintsTempList)

  }

  def storeHintsToVerificationHints_score(parsedHintslist:Seq[Seq[String]],readInitialHintsWithID:Map[String,String],originalHints:VerificationHints,rankTreshold:Float) ={
    //store read hints to VerificationHints
    println("---selected hints--")
    var readHints=VerificationHints(Map())
    var readHintsTemp:Map[IExpression.Predicate,VerifHintElement]=Map()
    var readHintsTempList:Seq[Map[IExpression.Predicate,VerifHintElement]]=Seq()
    var parsedHintsCount=0

    for(element<-parsedHintslist){
      //println(element)
      if(element(4).toFloat>rankTreshold){ //element(3)==1 means useful, element(4) is score
        val head=element(1).toString//element(1) is head
      val hint=readInitialHintsWithID(element(0).toString+":"+element(1)).toString //InitialHintsWithID ID:head->hint
        for((key,value)<-originalHints.getPredicateHints()){
          val keyTemp=key.toString().substring(0,key.toString().indexOf("/"))
          if(head==keyTemp){
            var usfulHintsList:Seq[VerifHintElement]=Seq()
            for(oneHint<-value){
              if(keyTemp==head && oneHint.toString()==hint){ //match initial hints and hints from file to tell usefulness
                usfulHintsList=usfulHintsList ++ Seq(oneHint)//add this hint to usfulHintsList
                //println(element(0),usfulHintsList)
                readHintsTempList=readHintsTempList:+Map(key->oneHint)
                parsedHintsCount=parsedHintsCount+1
              }
            }
            //readHints=readHints.addPredicateHints(Map(key->usfulHintsList)) //add this haed->hint:Seq() to readHints
          }
        }
      }else{ }//useless hint

    }

    println("selected hint count="+parsedHintsCount)
    (readHints,readHintsTempList)

  }

  def storeHintsToVerificationHints_topN(parsedHintslist:Seq[Seq[String]],readInitialHintsWithID:Map[String,String],originalHints:VerificationHints,N:Int) ={
    //store read hints to VerificationHints
    println("---selected hints--")
    var readHints=VerificationHints(Map())
    var readHintsTemp:Map[IExpression.Predicate,VerifHintElement]=Map()
    var readHintsTempList:Seq[Map[IExpression.Predicate,VerifHintElement]]=Seq()
    var parsedHintsCount=0
      for(element<-parsedHintslist.take(N)){//take first N element
      //println(element)
      val head=element(1).toString//element(1) is head
      val hint=readInitialHintsWithID(element(0).toString+":"+element(1)).toString //InitialHintsWithID ID:head->hint
        for((key,value)<-originalHints.getPredicateHints()){
          val keyTemp=key.toString().substring(0,key.toString().indexOf("/"))
          if(head==keyTemp){
            var usfulHintsList:Seq[VerifHintElement]=Seq()
            for(oneHint<-value){
              if(oneHint.toString()==hint){ //match initial hints and hints from file to tell usefulness
                usfulHintsList=usfulHintsList ++ Seq(oneHint)//add this hint to usfulHintsList
                //println(element(0),usfulHintsList)
                readHintsTempList=readHintsTempList:+Map(key->oneHint)
                parsedHintsCount=parsedHintsCount+1
              }
            }
            //readHints=readHints.addPredicateHints(Map(key->usfulHintsList)) //add this haed->hint:Seq() to readHints
          }
        }


    }

    println("selected hint count="+parsedHintsCount)
    (readHints,readHintsTempList)

  }
  def readHintsIDFromFile(fileName:String,originalHints:VerificationHints,rank:String=""):VerificationHints = {
    val fileNameShorter=fileName.substring(fileName.lastIndexOf("/"),fileName.length) //get file name
    var parsedHintslist=Seq[Seq[String]]() //store parsed hints

    //val f = "predictedHints/"+fileNameShorter+".optimizedHints" //read file
    val f = "../predictedHints/"+fileNameShorter+".optimizedHints" //python file
    for (line <- Source.fromFile(f).getLines) {
      var parsedHints=Seq[String]() //store parsed hints
      //parse read file
      var lineTemp=line.toString
      val ID=lineTemp.substring(0,lineTemp.indexOf(":"))
      lineTemp=lineTemp.substring(lineTemp.indexOf(":")+1,lineTemp.length)
      val head=lineTemp.substring(0,lineTemp.indexOf(":"))
      lineTemp=lineTemp.substring(lineTemp.indexOf(":")+1,lineTemp.length)
      val hint=lineTemp.substring(0,lineTemp.indexOf(":"))
      lineTemp=lineTemp.substring(lineTemp.indexOf(":")+1,lineTemp.length)
      val usefulness=lineTemp.substring(0,lineTemp.indexOf(":")) //1=useful,0=useless
      val score=lineTemp.substring(lineTemp.indexOf(":")+1,lineTemp.length) //1=useful,0=useless
      parsedHints= parsedHints:+ID:+head:+hint:+usefulness:+score //ID,head,hint,usefulness,score
      //println(parsedHints)
      parsedHintslist=parsedHintslist:+parsedHints
    }
    println("parsed hints count="+parsedHintslist.size)

    println("---readInitialHints-----")
    var readInitialHintsWithID:Map[String,String]=Map()
    //val fInitial = "predictedHints/"+fileNameShorter+".initialHints" //read file
    val fInitial = "../predictedHints/"+fileNameShorter+".initialHints"//python file
    for (line <- Source.fromFile(fInitial).getLines) {
      var parsedHints=Seq[String]() //store parsed hints
      //parse read file
      var lineTemp=line.toString
      val ID=lineTemp.substring(0,lineTemp.indexOf(":"))
      lineTemp=lineTemp.substring(lineTemp.indexOf(":")+1,lineTemp.length)
      val head=lineTemp.substring(0,lineTemp.indexOf(":"))
      lineTemp=lineTemp.substring(lineTemp.indexOf(":")+1,lineTemp.length)
      val hint=lineTemp
      readInitialHintsWithID=readInitialHintsWithID+(ID+":"+head->hint)
    }
    for ((key,value)<-readInitialHintsWithID){ //print initial hints
      println(key,value)
    }
    println("readInitialHints count="+readInitialHintsWithID.size)

    //store read hints to VerificationHints
    var readHints=VerificationHints(Map())
    var readHintsTempList:Seq[Map[IExpression.Predicate,VerifHintElement]]=Seq()
    if(rank.isEmpty){ //read rank option, no need for rank
      val (readHints_temp,readHintsTempList_temp)=storeHintsToVerificationHints_binary(parsedHintslist,readInitialHintsWithID,originalHints)
      readHints=readHints_temp
      readHintsTempList=readHintsTempList_temp
    }else{ //need rank
      //parse rank information
      var lineTemp=rank.toString
      val rankThreshold=lineTemp.substring(lineTemp.indexOf(":")+1,lineTemp.length).toFloat

      if(rankThreshold>1){//rank by top n
        println("use top "+ rankThreshold.toInt+" hints")
        val (readHints_temp,readHintsTempList_temp)=storeHintsToVerificationHints_topN(parsedHintslist,readInitialHintsWithID,originalHints,rankThreshold.toInt)
        readHints=readHints_temp
        readHintsTempList=readHintsTempList_temp
      }
      if(rankThreshold<1){//rank by score
        println("use score threshold "+ rankThreshold)
        val (readHints_temp,readHintsTempList_temp)=storeHintsToVerificationHints_score(parsedHintslist,readInitialHintsWithID,originalHints,rankThreshold)
        readHints=readHints_temp
        readHintsTempList=readHintsTempList_temp
      }

    }

    //store heads to set
    var heads:Set[IExpression.Predicate]=Set()
    for(value<-readHintsTempList){
      println(value)
      val tempValue=value.toSeq
      //tempValue.to
      heads=heads+tempValue(0)._1
    }



    for (head<-heads){
      var hintList:Seq[VerifHintElement]=Seq()
      for(value<-readHintsTempList){//value=Map(head->hint)
        val tempValue=value.toSeq
        if(tempValue(0)._1==head){
          //println(hintList)
          hintList=hintList:+tempValue(0)._2
        }
      }
      readHints=readHints.addPredicateHints(Map(head->hintList))
    }

    println("----readHints-----")
    for ((key,value)<-readHints.getPredicateHints()){
      println(key)
      for(v<-value){
        println(v)
      }
    }




    return readHints
  }

  def writeHornClausesToFile(system : ParametricEncoder.System,file:String): Unit ={
    println("Write horn to file")
    println(file.substring(file.lastIndexOf("/")+1))
    val fileName=file.substring(file.lastIndexOf("/")+1)
    //val writer = new PrintWriter(new File("trainData/"+fileName+".horn"))
    val writer = new PrintWriter(new File("../trainData/"+fileName+".horn")) //python path
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

  def writeSMTFormatToFile(encoder:ParametricEncoder): Unit ={


      val basename = GlobalParameters.get.fileName
//      val suffix =
//        (for (inv <- invariants) yield (inv mkString "_")) mkString "--"
//      val filename = basename + "-" + suffix + ".smt2"
    println(basename.substring(basename.lastIndexOf("/")+1))
    val fileName=basename.substring(basename.lastIndexOf("/")+1)
    //val filename = basename + ".smt2"

      println
      println("Writing Horn clauses to " + fileName)

      //val out = new java.io.FileOutputStream("trainData/"+fileName+".smt2")
      val out = new java.io.FileOutputStream("../trainData/"+fileName+".smt2") //python path
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


}




