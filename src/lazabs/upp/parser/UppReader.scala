/**
 * Copyright (c) 2011-2014 Hossein Hojjat. All rights reserved.
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

package lazabs.upp.parser

import scala.xml._
import scala.xml.factory.XMLLoader
import javax.xml.parsers.SAXParser
import lazabs.ast.ASTree._
import lazabs.upp.UppAst._
import lazabs.types._
import lazabs.nts._
import lazabs.cfg._
import lazabs.horn.global._


object UppReader {
  // Do not validate the DTD, takes too much time
  object MyXML extends XMLLoader[Elem] {
    override def parser: SAXParser = {
      val f = javax.xml.parsers.SAXParserFactory.newInstance()
      f.setNamespaceAware(false)
      f.setFeature("http://apache.org/xml/features/disallow-doctype-decl", true);
      f.newSAXParser()
    }
  }

  /**
   * global integer variables
   */
  var globalIntVars = List[String]()

  def flattenArray(l: Label): Label = l match {
    case Assume(p) => Assume(flattenArray(p))
    case Assign(lhs@Variable(n,_), rhs) =>
      nonConstIndices(rhs).toList match {
        case Nil => l
        case (ScArray(Some(Variable(arrName,_)),Some(NumericalConst(aLength))),index) :: Nil =>
          (0 until aLength.intValue).map{i =>
            Sequence(
              Assume(lazabs.ast.ASTree.Equality(index,NumericalConst(i))),
              Assign(lhs,flattenArray(rhs,Map(index->i)))
            )
          }.reduceLeft[Label](Choice(_,_))
        case _ =>
          throw new Exception("Currently only one non-constant array index is allowed in an expression")
      }
    case Assign(ScArray(Some(an1),_),ScArray(Some(an2),_)) =>
      throw new Exception("Assignment to array")
    case Assign(ArraySelect(array@ScArray(Some(Variable(arrName,_)),Some(NumericalConst(aLength))),index), rhs) =>
      (0 until aLength.intValue).map{i => 
        Sequence(
          Assume(lazabs.ast.ASTree.Equality(index,NumericalConst(i))),
          Assign(Variable("upp_" + i + "_" + arrName.drop(4)).stype(IntegerType()),flattenArray(rhs,Map(index->i)))
        )
      }.reduceLeft[Label](Choice(_,_))
    case _ =>
      println(l)
      throw new Exception("Unsupported label in control flow graph " + lazabs.viewer.ScalaPrinter(l))
  }
  
  def funcToHornCls(f: FunctionDefinition): (String,String,List[Variable],Seq[HornClause]) = f match {
    case FunctionDefinition(funcName, params, t, body, None) =>
      val to = CFGVertex(FreshCFGStateId.apply) // the end state
      val (start,trans,_,vm) = MakeCFG.makeCFG(body,to,List(),List((globalIntVars.toSet ++ params.map(_.name)).map(Variable(_).stype(IntegerType()))))
      val cfg = CFGTransform(CFG(start,trans.map{x => 
          (x._1,x._2.map(adj => CFGAdjacent(flattenArray(adj.label), adj.to)))
        }
        ,Map(),Map(),vm,Map.empty,Map.empty,None),false,false)
      //lazabs.viewer.DrawGraph(cfg.transitions.toList,cfg.predicates,false,None)
      //Console.readLine
      val nts = lazabs.viewer.NTSPrinter.toNtsSub(cfg,funcName)
      ((funcName + start.getId),(funcName + to.getId),(nts.vars), NtsHorn(Nts("uppaal",List(),List(nts))))
  }
  
  /**
   * gets non-const array indexes
   */
  def nonConstIndices(e: Expression): Map[ScArray,Expression] = e match {
    case ArraySelect(ScArray(_,_),NumericalConst(_)) =>
      Map()
    case ArraySelect(arr@ScArray(_,_),index) =>
      Map(arr->index)
    case TernaryExpression(op, e1, e2, e3) =>
      val first = nonConstIndices(e1)
      val second = nonConstIndices(e2)
      val third = nonConstIndices(e3)
      first ++ second ++ third
    case BinaryExpression(e1, op, e2) =>
      val first = nonConstIndices(e1)
      val second = nonConstIndices(e2)
      first ++ second
    case UnaryExpression(op, e) =>
      nonConstIndices(e)
    case _ =>
      Map()
  }  
  
  /**
   * converts array accesses to flatten variables
   * @param instantiate indicates what to replace for non-const indices
   */
  def flattenArray(e: Expression, instantiate: Map[Expression,Int] = Map.empty) : Expression = e match {
    case ArraySelect(ScArray(Some(Variable(arrName,_)),_),NumericalConst(constIndex)) =>
      Variable("upp_" + constIndex + "_" + arrName.drop(4)).stype(IntegerType())
    case ArraySelect(ScArray(Some(Variable(arrName,_)),_),index) =>
      instantiate.get(index) match {
        case Some(c) => Variable("upp_" + c + "_" + arrName.drop(4)).stype(IntegerType())
        case None => throw new Exception("non-const indices")
      }
    case TernaryExpression(op, e1, e2, e3) =>
      TernaryExpression(op, flattenArray(e1,instantiate), flattenArray(e2,instantiate), flattenArray(e2,instantiate)).stype(e.stype)
    case BinaryExpression(e1, op, e2) =>
      BinaryExpression(flattenArray(e1,instantiate), op, flattenArray(e2,instantiate)).stype(e.stype)
    case UnaryExpression(op, e) =>
      UnaryExpression(op, flattenArray(e,instantiate)).stype(e.stype)
    case v@Variable(name,None) => v
    case v@Variable(name,Some(_)) => v
    case NumericalConst(_) => e
    case BoolConst(_) => e
    case _ =>
      println("Expression not supported in flattening " + e)
      e
  }

  def readAutomaton(template: NodeSeq): UppAutomaton = {
    val name = (template \ "name").text
    val initial = UppVertex((template \ "init" \ "@ref").text)
    var states = Set[UppVertex]()
    var errors = Set[UppVertex]()
    var trans = Map[UppVertex,Set[UppTransition]]().empty

    val localClocks = (for (VarDeclaration(cl, ClassType("clock"), _) <- UppCParser((template \ "declaration").text)) 
      yield "upp_" + name + "_" + cl.drop(4))

    val localIntVars: List[String] = UppCParser((template \ "declaration").text).map {_ match {
      case VarDeclaration(v, IntegerType(), _) => List("upp_" + name + "_" + v.drop(4))
      case VarDeclaration(v, ClassType(ct), _) if (ct != "chan" && ct != "clock") => List("upp_" + name + "_" + v.drop(4))
      case VarDeclaration(arr, ArrayType(IntegerType(), IntegerType()), ScArray(None, Some(NumericalConst(size)))) => (0 until size.intValue).map(i => ("upp_" + i + "_" + arr.drop(4))).toList
      case _ => List()
    }}.flatten
    
    var invariants = Map[UppVertex,Expression]().empty

    for(location <- template \ "location") {
      val id = UppVertex((location \ "@id").text)
      states += id
      if((location \ "name").text == "ERROR")
        errors += id
      if ((location \ "label" \ "@kind").text == "invariant")
        invariants += (id -> (lazabs.utils.Manip.substitute(UppCParser.parseBooleanExpr((location \ "label").text),
                (localClocks ++ localIntVars).map(l => (
                    Variable("upp_" + l.split("_").last).stype(IntegerType()),
                    Variable("upp_" + name + "_" + l.split("_").last).stype(IntegerType())
                )).toMap
        )))
    }

    for(transition <- template \ "transition") {
      val source = (transition \ "source" \ "@ref").text
      val target = (transition \ "target" \ "@ref").text
      var action: Option[UppSynchAction] = None
      var assign: Either[List[Expression],FunctionCall] = Left(List())
      var guard: Expression = BoolConst(true)
      
      for(label <- transition \ "label") {
        (label \ "@kind").text match {

          case "synchronisation" =>
            action = if(label.text.takeRight(1) == "!") 
              Some(UppSendAction("upp_" + label.text.dropRight(1))) 
                else 
              Some(UppReceiveAction("upp_" + label.text.dropRight(1)))

          case "assignment" =>
            assign = UppCParser.parseAssignAction(label.text) match {
              case Left(assignList) => Left(assignList.map(a => flattenArray(lazabs.utils.Manip.substitute(a,
                (localClocks ++ localIntVars).map{ l => (
                  Variable("upp_" + l.split("_").last).stype(IntegerType()),
                  Variable("upp_" + name + "_" + l.split("_").last).stype(IntegerType())
                )}.toMap))))
              case r@Right(_) => r
            }

          case "guard" =>
            val renamedGuard = lazabs.utils.Manip.substitute(UppCParser.parseBooleanExpr(label.text),
              (localClocks ++ localIntVars).map(l => (
                  Variable("upp_" + l.split("_").last).stype(IntegerType()),
                  Variable("upp_" + name + "_" + l.split("_").last).stype(IntegerType()))).toMap)
            val flattenGuard = flattenArray(renamedGuard)
            if(guard == BoolConst(true))
              guard = flattenGuard
            else 
              guard = Conjunction(flattenGuard, guard)             
        }
      }
      trans += UppVertex(source) -> (trans.getOrElse(UppVertex(source),Set()) + UppTransition(UppVertex(target),action,assign,guard))
    }

    var i = 0
    val stateToNum = states.map{st =>
      i = i + 1
      (st,i - 1)
    }.toMap

    UppAutomaton(name,localClocks,localIntVars,initial,errors,states,invariants,trans,stateToNum)
  }

  def apply(fileName: String): Uppaal = {
    val nseq: NodeSeq = MyXML.loadFile(fileName)
    val systems: NodeSeq = nseq \ "system"
    var clocks = List[String]()
    var channels = List[String]()
    var globalFunctions = Map[String,(String,String,List[Variable],Seq[HornClause])]()

    UppCParser((nseq \ "declaration").text).foreach{_ match {
      case VarDeclaration(cl, ClassType("clock"), _) => clocks ::= cl
      case VarDeclaration(ch, ClassType("chan"), _) => channels ::= ch
      case VarDeclaration(v, ClassType(_), _) => globalIntVars ::= v
      case VarDeclaration(v, IntegerType(), _) => globalIntVars ::= v
      case VarDeclaration(arr, ArrayType(IntegerType(), IntegerType()), ScArray(None, Some(NumericalConst(size)))) =>
        globalIntVars :::= (0 until size.intValue).map(i => ("upp_" + i + "_" + arr.drop(4))).toList
      case fast@FunctionDefinition(funcName, params, t, body, None) =>
        globalFunctions += (funcName -> funcToHornCls(fast))
      case _ =>
    }}

    val automata = (nseq \ "template") map { template =>
      UppCParser((template \ "declaration").text).foreach {
        case fast@FunctionDefinition(funcName, params, t, body, None) =>
          globalFunctions += funcName -> funcToHornCls(fast)
        case _ =>
      }
      readAutomaton(template)
    }

    val automatonToNum = automata.map(_.name).zipWithIndex.toMap
    Uppaal(clocks,channels,globalIntVars,globalFunctions,automata,automatonToNum)
  }
}
