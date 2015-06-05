/**
 * Copyright (c) 2015 Philipp Ruemmer. All rights reserved.
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


import ap.basetypes.IdealInt
import ap.parser._
import concurrentC._
import concurrentC.Absyn._

import lazabs.horn.bottomup.HornClauses

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer, Buffer,
                                 Stack}

object CCReader {
  class ParseException(msg : String) extends Exception(msg)
  class TranslationException(msg : String) extends Exception(msg)

  import IExpression._

  private abstract sealed class CCExpr {
    def toTerm : ITerm
    def toFormula : IFormula
  }
  private case class CCIntTerm(t : ITerm) extends CCExpr {
    def toTerm : ITerm = t
    def toFormula : IFormula = !eqZero(t)
  }
  private case class CCFormula(f : IFormula) extends CCExpr {
    def toTerm : ITerm = ite(f, 1, 0)
    def toFormula : IFormula = f
  }
}

class CCReader {

  import CCReader._

  def apply(input : java.io.Reader) : (ParametricEncoder.System,
                                       Seq[HornClauses.Clause]) = {
    def entry(parser : concurrentC.parser) = parser.pProgram
    val prog = parseWithEntry(input, entry _)
    println(printer print prog)
    translateProgram(prog)
    (ParametricEncoder.System(processes.toList,
                              globalVars.size,
                              None,
                              ParametricEncoder.NoTime,
                              List()),
     assertions.toList)
  }

  /**
   * Parse starting at an arbitrarily specified entry point
   */
  private def parseWithEntry[T](input : java.io.Reader,
                                entry : (parser) => T) : T = {
    val l = new Yylex(new ap.parser.Parser2InputAbsy.CRRemover2 (input))
    val p = new parser(l)
    
    try { entry(p) } catch {
      case e : Exception =>
        throw new ParseException(
             "At line " + String.valueOf(l.line_num()) +
             ", near \"" + l.buff() + "\" :" +
             "     " + e.getMessage())
    }
  }

  private val printer = new PrettyPrinterNonStatic

  //////////////////////////////////////////////////////////////////////////////

  import IExpression._
  import HornClauses.Clause

  private val globalVars = new ArrayBuffer[ConstantTerm]
  private val globalVarsInit = new ArrayBuffer[CCExpr]

  private def globalVarIndex(name : String) : Option[Int] =
    (globalVars indexWhere (_.name == name)) match {
      case -1 => None
      case i  => Some(i)
    }

  private def lookupVar(name : String) : Int =
    (globalVars indexWhere (_.name == name)) match {
      case -1 =>
        (localVars indexWhere (_.name == name)) match {
          case -1 =>
            throw new TranslationException(
                        "Symbol " + name + " is not declared")
          case i => i + globalVars.size
        }
      case i  => i
    }

  private val localVars = new ArrayBuffer[ConstantTerm]
  private val localFrameStack = new Stack[Int]

  private def pushLocalFrame =
    localFrameStack push localVars.size
  private def popLocalFrame =
    localVars reduceToSize localFrameStack.pop

  private def allFormalVars : Seq[ITerm] =
    globalVars.toList ++ localVars.toList

  //////////////////////////////////////////////////////////////////////////////

  private val channels = new MHashMap[String, ParametricEncoder.CommChannel]

  //////////////////////////////////////////////////////////////////////////////

  private val processes =
    new ArrayBuffer[(ParametricEncoder.Process, ParametricEncoder.Replication)]

  private val assertions = new ArrayBuffer[Clause]

  //////////////////////////////////////////////////////////////////////////////

  /** Implicit conversion so that we can get a Scala-like iterator from a
    * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  private def translateProgram(prog : Program) : Unit = {
    // first collect all declarations

    val globalVarSymex = Symex.apply

    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
      decl match {
        case decl : Global =>
          collectVarDecls(decl.dec_, true, globalVarSymex)

        case decl : Chan =>
          for (name <- decl.chan_def_.asInstanceOf[AChan].listident_) {
            if (channels contains name)
              throw new TranslationException(
                "Channel " + name + " is already declared")
            channels.put(name, new ParametricEncoder.CommChannel(name))
          }

        case _ =>
          // nothing
      }

    globalVarsInit ++= globalVarSymex.getValues

    // then translate the threads
    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
      decl match {
        case decl : Athread =>
          decl.thread_def_ match {
            case thread : SingleThread => {
              val translator = new ThreadTranslator(thread.ident_)
              translator translate thread.compound_stm_
              processes += ((translator.toProcess, ParametricEncoder.Singleton))
            }
          }

        case _ =>
          // nothing
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def collectVarDecls(dec : Dec,
                              global : Boolean,
                              values : Symex) : Unit = dec match {
    case decl : Declarators => {
      // just assume that the type is int for the time being

      for (initDecl <- decl.listinit_declarator_) initDecl match {
        case initDecl : OnlyDecl => {
          val c = new ConstantTerm(getName(initDecl.declarator_))
          (if (global) globalVars else localVars) += c
          values addValue CCIntTerm(c)
        }
        case initDecl : InitDecl => {
          val c = new ConstantTerm(getName(initDecl.declarator_))
          val initValue = initDecl.initializer_ match {
            case init : InitExpr => values eval init.exp_
          }
          (if (global) globalVars else localVars) += c
          values addValue initValue
        }
      }
    }
    case _ : NoDeclarator =>
      // nothing
  }

  private def getName(decl : Declarator) : String = decl match {
    case decl : NoPointer => getName(decl.direct_declarator_)
  }

  private def getName(decl : Direct_declarator) : String = decl match {
    case decl : Name => decl.ident_
    case decl : ParenDecl => getName(decl.declarator_)
  }

  //////////////////////////////////////////////////////////////////////////////

  private object Symex {
    def apply = {
      val values = new ArrayBuffer[CCExpr]
      for (t <- allFormalVars)
        values += CCIntTerm(t)
      new Symex(values)
    }
  }

  private class Symex private (values : Buffer[CCExpr]) {
    var assertionExprs = List[CCExpr]()

    def addValue(t : CCExpr) =
      values += t

    def getValue(name : String) =
      values(lookupVar(name))
    def setValue(name : String, t : CCExpr) =
      values(lookupVar(name)) = t

    def getValues : Seq[CCExpr] =
      values.toList
    def getValuesAsTerms : Seq[ITerm] =
      for (expr <- values.toList) yield expr.toTerm

    def asAtom(pred : Predicate) =
      IAtom(pred, getValuesAsTerms take pred.arity)

    def asLValue(exp : Exp) : String = exp match {
      case exp : Evar => exp.ident_
      case exp =>
        throw new TranslationException(
                    "Can only handle assignments to variables, not " +
                    (printer print exp))
    }

    def eval(exp : Exp) : CCExpr = exp match {
      case exp : Ecomma => {
        eval(exp.exp_1)
        eval(exp.exp_2)
      }
      case exp : Eassign => {
        val lhs = eval(exp.exp_1).toTerm
        val rhs = eval(exp.exp_2).toTerm
        val newVal = CCIntTerm(exp.assignment_op_ match {
          case _ : Assign    => rhs
          case _ : AssignMul => lhs * rhs
//          case _ : AssignDiv.    Assignment_op ::= "/=" ;
//          case _ : AssignMod.    Assignment_op ::= "%=" ;
          case _ : AssignAdd => lhs + rhs
          case _ : AssignSub => lhs - rhs
//          case _ : AssignLeft.   Assignment_op ::= "<<=" ;
//          case _ : AssignRight.  Assignment_op ::= ">>=" ;
//          case _ : AssignAnd.    Assignment_op ::= "&=" ;
//          case _ : AssignXor.    Assignment_op ::= "^=" ;
//          case _ : AssignOr.     Assignment_op ::= "|=" ;
        })
        setValue(asLValue(exp.exp_1), newVal)
        newVal
      }
      case exp : Econdition =>
        (eval(exp.exp_1), eval(exp.exp_2), eval(exp.exp_3)) match {
          case (cond, CCFormula(s), CCFormula(t)) =>
            CCFormula(ite(cond.toFormula, s, t))
          case (cond, left, right) =>
            CCIntTerm(ite(cond.toFormula, left.toTerm, right.toTerm))
        }
      case exp : Elor =>
        CCFormula(eval(exp.exp_1).toFormula | eval(exp.exp_2).toFormula)
      case exp : Eland =>
        CCFormula(eval(exp.exp_1).toFormula & eval(exp.exp_2).toFormula)
//      case exp : Ebitor.      Exp6  ::= Exp6 "|" Exp7;
//      case exp : Ebitexor.    Exp7  ::= Exp7 "^" Exp8;
//      case exp : Ebitand.     Exp8  ::= Exp8 "&" Exp9;
      case exp : Eeq =>
        CCFormula(eval(exp.exp_1).toTerm === eval(exp.exp_2).toTerm)
      case exp : Eneq =>
        CCFormula(eval(exp.exp_1).toTerm =/= eval(exp.exp_2).toTerm)
      case exp : Elthen =>
        CCFormula(eval(exp.exp_1).toTerm < eval(exp.exp_2).toTerm)
      case exp : Egrthen =>
        CCFormula(eval(exp.exp_1).toTerm > eval(exp.exp_2).toTerm)
      case exp : Ele =>
        CCFormula(eval(exp.exp_1).toTerm <= eval(exp.exp_2).toTerm)
      case exp : Ege =>
        CCFormula(eval(exp.exp_1).toTerm >= eval(exp.exp_2).toTerm)
//      case exp : Eleft.       Exp11 ::= Exp11 "<<" Exp12;
//      case exp : Eright.      Exp11 ::= Exp11 ">>" Exp12;
      case exp : Eplus =>
        CCIntTerm(eval(exp.exp_1).toTerm + eval(exp.exp_2).toTerm)
      case exp : Eminus =>
        CCIntTerm(eval(exp.exp_1).toTerm - eval(exp.exp_2).toTerm)
      case exp : Etimes =>
        CCIntTerm(eval(exp.exp_1).toTerm * eval(exp.exp_2).toTerm)
//      case exp : Ediv.        Exp13 ::= Exp13 "/" Exp14;
//      case exp : Emod.        Exp13 ::= Exp13 "%" Exp14;
//      case exp : Etypeconv.   Exp14 ::= "(" Type_name ")" Exp14;
      case exp : Epreinc => {
        val newVal = CCIntTerm(eval(exp.exp_).toTerm + 1)
        setValue(asLValue(exp.exp_), newVal)
        newVal
      }
      case exp : Epredec => {
        val newVal = CCIntTerm(eval(exp.exp_).toTerm - 1)
        setValue(asLValue(exp.exp_), newVal)
        newVal
      }
      case exp : Epreop => {
        val oldVal = eval(exp.exp_)
        exp.unary_operator_ match {
//          case _ : Address.     Unary_operator ::= "&" ;
//          case _ : Indirection. Unary_operator ::= "*" ;
          case _ : Plus       => oldVal
          case _ : Negative   => CCIntTerm(-oldVal.toTerm)
//          case _ : Complement.  Unary_operator ::= "~" ;
          case _ : Logicalneg => CCFormula(~oldVal.toFormula)
        }
      }
//      case exp : Ebytesexpr.  Exp15 ::= "sizeof" Exp15;
//      case exp : Ebytestype.  Exp15 ::= "sizeof" "(" Type_name ")";
//      case exp : Earray.      Exp16 ::= Exp16 "[" Exp "]" ;
//      case exp : Efunk.       Exp16 ::= Exp16 "(" ")";
      case exp : Efunkpar =>
        if ((printer print exp.exp_) == "assert" && !exp.listexp_.isEmpty) {
          assertionExprs = eval(exp.listexp_.head) :: assertionExprs
          CCFormula(true)
        } else {
          throw new TranslationException(
                      "Cannot handle function " + (printer print exp.exp_))
        }
//      case exp : Eselect.     Exp16 ::= Exp16 "." Ident;
//      case exp : Epoint.      Exp16 ::= Exp16 "->" Ident;
      case exp : Epostinc => {
        val oldVal = eval(exp.exp_)
        setValue(asLValue(exp.exp_), CCIntTerm(oldVal.toTerm + 1))
        oldVal
      }
      case exp : Epostdec => {
        val oldVal = eval(exp.exp_)
        setValue(asLValue(exp.exp_), CCIntTerm(oldVal.toTerm - 1))
        oldVal
      }
      case exp : Evar =>
        getValue(exp.ident_)
      case exp : Econst =>
        eval(exp.constant_)
//      case exp : Estring.     Exp17 ::= String;
    }

    def eval(constant : Constant) : CCExpr = constant match {
//      case constant : Efloat.        Constant ::= Double;
//      case constant : Echar.         Constant ::= Char;
//      case constant : Eunsigned.     Constant ::= Unsigned;
//      case constant : Elong.         Constant ::= Long;
//      case constant : Eunsignlong.   Constant ::= UnsignedLong;
//      case constant : Ehexadec.      Constant ::= Hexadecimal;
//      case constant : Ehexaunsign.   Constant ::= HexUnsigned;
//      case constant : Ehexalong.     Constant ::= HexLong;
//      case constant : Ehexaunslong.  Constant ::= HexUnsLong;
      case constant : Eoctal =>
        CCIntTerm(IdealInt(constant.octal_, 8))
//      case constant : Eoctalunsign.  Constant ::= OctalUnsigned;
//      case constant : Eoctallong.    Constant ::= OctalLong;
//      case constant : Eoctalunslong. Constant ::= OctalUnsLong;
//      case constant : Ecdouble.      Constant ::= CDouble;
//      case constant : Ecfloat.       Constant ::= CFloat;
//      case constant : Eclongdouble.  Constant ::= CLongDouble;
      case constant : Eint =>
        CCIntTerm(i(constant.integer_))
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private class ThreadTranslator(prefix : String) {

    private val clauses = new ArrayBuffer[(Clause, ParametricEncoder.Synchronisation)]

    def toProcess = clauses.toList

    private def output(c : Clause) : Unit =
      clauses += ((c, ParametricEncoder.NoSync))

    private var locationCounter = 0
    def newPred : Predicate = {
      val res = new Predicate(prefix + locationCounter, allFormalVars.size)
      locationCounter = locationCounter + 1
      res
    }

    def translate(compound : Compound_stm) : Unit = {
      val entry = newPred
      output(Clause(IAtom(entry, globalVarsInit.toList map (_.toTerm)),
                    List(), true))
      translate(compound, entry, newPred)
    }

    def translate(stm : Stm,
                  entry : Predicate,
                  exit : Predicate) : Unit = stm match {
//      case stm : LabelS.   Stm ::= Labeled_stm ;
      case stm : CompS =>
        translate(stm.compound_stm_, entry, exit)
      case stm : ExprS => {
        val entryAtom = IAtom(entry, allFormalVars)
        val exprSymex = Symex.apply
        stm.expression_stm_ match {
          case _ : SexprOne => // nothing
          case stm : SexprTwo => exprSymex eval stm.exp_
        }
        output(Clause(exprSymex asAtom exit, List(entryAtom), true))

        import HornClauses._
        for (a <- exprSymex.assertionExprs)
          assertions += (a.toFormula :- entryAtom)
      }
//      case stm : SelS.     Stm ::= Selection_stm ;
      case stm : IterS =>
        translate(stm.iter_stm_, entry, exit)
//      case stm : JumpS.    Stm ::= Jump_stm ;
    }

    def translate(dec : Dec, entry : Predicate) : Predicate = {
      val entryAtom = IAtom(entry, allFormalVars)
      val decSymex = Symex.apply
      collectVarDecls(dec, false, decSymex)
      val exit = newPred
      output(Clause(decSymex asAtom exit, List(entryAtom), true))
      exit
    }

    def translate(compound : Compound_stm,
                  entry : Predicate,
                  exit : Predicate) : Unit = compound match {
      case compound : ScompOne => {
        val vars = allFormalVars
        output(Clause(IAtom(exit, vars), List(IAtom(entry, vars)), true))
      }
      case compound : ScompTwo => {
        val stmsIt = compound.liststm_.iterator
        var prevPred = entry
        while (stmsIt.hasNext) {
          val stm = stmsIt.next
          val nextPred = if (stmsIt.hasNext) newPred else exit
          translate(stm, prevPred, nextPred)
          prevPred = nextPred
        }
      }

      case compound : ScompThree => {
        pushLocalFrame

        var prevPred = entry
        for (dec <- compound.listdec_)
          prevPred = translate(dec, prevPred)

        val lastAtom = IAtom(prevPred, allFormalVars)

        popLocalFrame

        output(Clause(IAtom(exit, allFormalVars), List(lastAtom), true))
      }

      case compound : ScompFour => {
        pushLocalFrame

        var prevPred = entry
        for (dec <- compound.listdec_)
          prevPred = translate(dec, prevPred)

        val stmsIt = compound.liststm_.iterator
        while (stmsIt.hasNext) {
          val stm = stmsIt.next
          val nextPred = if (stmsIt.hasNext) newPred else exit
          translate(stm, prevPred, nextPred)
          prevPred = nextPred
        }

        popLocalFrame
      }
    }

    def translate(stm : Iter_stm,
                  entry : Predicate,
                  exit : Predicate) : Unit = stm match {
      case stm : SiterOne => {
        val first = newPred
        val entryAtom = IAtom(entry, allFormalVars)
        val condSymex = Symex.apply
        val cond = (condSymex eval stm.exp_).toFormula
        output(Clause(condSymex asAtom first, List(entryAtom), cond))
        output(Clause(condSymex asAtom exit, List(entryAtom), ~cond))
        translate(stm.stm_, first, entry)
      }

//      case stm : SiterTwo.   Iter_stm ::= "do" Stm "while" "(" Exp ")" ";" ;
//      case stm : SiterThree. Iter_stm ::= "for" "(" Expression_stm Expression_stm ")" Stm ;
//      case stm : SiterFour.  Iter_stm ::= "for" "(" Expression_stm Expression_stm Exp ")" Stm;
    }

  }

}