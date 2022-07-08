package lazabs.horn.concurrency

import lazabs.GlobalParameters
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.concurrency.DrawHornGraph.addQuotes
import lazabs.horn.concurrency.HintsSelection.detectIfAJSONFieldExists
import play.api.libs.json.{JsSuccess, JsValue, Json}

import java.io.{File, PrintWriter}

object TemplateSelectionUtils{

  def outputPrologFile(normalizedClauses:Seq[Clause],typeName:String="normalized"): Unit ={
    val writerGraph = new PrintWriter(new File(GlobalParameters.get.fileName + "."+typeName+".prolog"))
    for (c<-normalizedClauses)
      writerGraph.write(c.toPrologString+"\n")
    writerGraph.close()
  }

  def writeGNNInputFieldToJSONFile(fieldName: String, fiedlContent: Arrays, writer: PrintWriter, lastFiledFlag: Boolean): Unit = {
    fiedlContent match {
      case StringArray(x) => writeOneField(fieldName, x, writer)
      case IntArray(x) => writeOneField(fieldName, x, writer)
      case PairArray(x) => writeOneField(fieldName, x, writer)
      case TripleArray(x) => writeOneField(fieldName, x, writer)
      case PairStringArray(x)=> writePairStringArrayField(fieldName, x, writer)
    }
    if (lastFiledFlag == false)
      writer.write(",\n")
    else
      writer.write("\n")
  }

  sealed abstract class Arrays
  case class StringArray(x: Array[String]) extends Arrays
  case class IntArray(x: Array[Int]) extends Arrays
  case class PairArray(x: Array[Pair[Int, Int]]) extends Arrays
  case class PairStringArray(x: Array[Pair[String, String]]) extends Arrays
  case class TripleArray(x: Array[Triple[Int, Int, Int]]) extends Arrays

  def writeOneField(fieldName: String, fiedlContent: Array[Pair[Int, Int]], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write("[")
      writer.write(p._1.toString)
      writer.write(",")
      writer.write(p._2.toString)
      writer.write("]")
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }
  def writePairStringArrayField(fieldName: String, fiedlContent: Array[Pair[String, String]], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write("[")
      writer.write(p._1)
      writer.write(",")
      writer.write(p._2)
      writer.write("]")
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }
  def writeOneField(fieldName: String, fiedlContent: Array[Triple[Int, Int, Int]], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write("[")
      writer.write(p._1.toString)
      writer.write(",")
      writer.write(p._2.toString)
      writer.write(",")
      writer.write(p._3.toString)
      writer.write("]")
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }

  def writeOneField(fieldName: String, fiedlContent: Array[Int], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write(p.toString)
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }

  def writeOneField(fieldName: String, fiedlContent: Array[String], writer: PrintWriter): Unit = {
    writer.write(addQuotes(fieldName))
    writer.write(":")
    writer.write("[")
    val filedSize = fiedlContent.size - 1
    for ((p, i) <- fiedlContent.zipWithIndex) {
      writer.write(addQuotes(p.toString))
      if (i < filedSize)
        writer.write(",")
    }
    writer.write("]")
  }
  def readOneJSONFieldToMap(fieldName:String,fileName:String,json_data: JsValue,fields:Map[String,String]): Map[String,String] ={
    try{
      val stRelationalEqs= (json_data \ fieldName).validate[Array[String]] match {
        case JsSuccess(st,_)=> st
      }
      fields++Map(fieldName->stRelationalEqs.head)
    } catch {
      case _=> fields
    }
  }
  def readJSONFieldToMap(solvingTimeFileName:String,fieldNames:Seq[String]=Seq("RelationalEqs","Term","Octagon","RelationalIneqs","splitClauses")): Map[String,String] ={
    var fields:Map[String,String]=Map()
    val json_content = scala.io.Source.fromFile(solvingTimeFileName).mkString
    val json_data = Json.parse(json_content)
    //println("json_data",json_data)
    for (f<-fieldNames)
      fields=readOneJSONFieldToMap(fieldName = f,fileName = solvingTimeFileName,json_data=json_data,fields = fields)
    fields
  }

  def writeSolvingTimeToJSON(solvingTimeFileName:String,fields:Map[String,String]): Unit ={
    val writer = new PrintWriter(new File(solvingTimeFileName))
    writer.write("{\n")
    var lastFiledFlag= false
    for (f<-fields)
      writeGNNInputFieldToJSONFile(f._1, StringArray(Array[String](f._2)), writer, lastFiledFlag)
    lastFiledFlag = true
    writeGNNInputFieldToJSONFile("dummyFiled", StringArray(Array[String]()), writer, lastFiledFlag)
    writer.write("}")
    writer.close()
  }



}

