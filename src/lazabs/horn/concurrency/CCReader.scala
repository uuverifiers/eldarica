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
                                 Stack, LinkedHashSet}

object CCReader {
  class ParseException(msg : String) extends Exception(msg)
  class TranslationException(msg : String) extends Exception(msg)

  def warn(msg : String) : Unit =
    Console.err.println("Warning: " + msg)

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
    def toTerm : ITerm = f match {
      case IBoolLit(true) =>  1
      case IBoolLit(false) => 0
      case f =>               ite(f, 1, 0)
    }
    def toFormula : IFormula = f
  }
}

class CCReader(input : java.io.Reader, entryFunction : String) {

  import CCReader._

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
    (localVars lastIndexWhere (_.name == name)) match {
      case -1 =>
        (globalVars lastIndexWhere (_.name == name)) match {
          case -1 =>
            throw new TranslationException(
                        "Symbol " + name + " is not declared")
          case i => i
        }
      case i  => i + globalVars.size
    }

  private val localVars = new ArrayBuffer[ConstantTerm]
  private val localFrameStack = new Stack[Int]

  private def pushLocalFrame =
    localFrameStack push localVars.size
  private def popLocalFrame =
    localVars reduceToSize localFrameStack.pop

  private def allFormalVars : Seq[ITerm] =
    globalVars.toList ++ localVars.toList
  private def allVarInits : Seq[ITerm] =
    (globalVarsInit.toList map (_.toTerm)) ++ (localVars.toList map (i(_)))

  private def freeFromGlobal(t : IExpression) : Boolean =
    !ContainsSymbol(t, (s:IExpression) => s match {
                      case IConstant(c) => globalVars contains c
                      case _ => false
                    })

  private def freeFromGlobal(t : CCExpr) : Boolean = t match {
    case CCIntTerm(s) => freeFromGlobal(s)
    case CCFormula(f) => freeFromGlobal(f)
  }

  //////////////////////////////////////////////////////////////////////////////

  private val channels = new MHashMap[String, ParametricEncoder.CommChannel]

  private val functionDefs  = new MHashMap[String, Function_def]
  private val functionDecls = new MHashMap[String, Direct_declarator]

  //////////////////////////////////////////////////////////////////////////////

  private val processes =
    new ArrayBuffer[(ParametricEncoder.Process, ParametricEncoder.Replication)]

  private val assertionClauses = new ArrayBuffer[Clause]

  private val clauses = new ArrayBuffer[(Clause, ParametricEncoder.Synchronisation)]

  private def output(c : Clause) : Unit = {
//println(c)
    clauses += ((c, ParametricEncoder.NoSync))
}

  private def mergeClauses(from : Int) : Unit = if (from < clauses.size - 1) {
    val concernedClauses = clauses.slice(from, clauses.size)
    val (entryClauses, transitionClauses) =
      if (concernedClauses.head._1.body.isEmpty) {
        concernedClauses partition (_._1.body.isEmpty)
      } else {
        val entryPred = concernedClauses.head._1.body.head.pred
        concernedClauses partition (_._1.body.head.pred == entryPred)
      }

    val lastClauses = transitionClauses groupBy (_._1.body.head.pred)

    clauses reduceToSize from

    def chainClauses(currentClause : Clause,
                     currentSync : ParametricEncoder.Synchronisation,
                     seenPreds : Set[Predicate]) : Unit = {
      val headPred = currentClause.head.pred
      if (seenPreds contains headPred)
        throw new TranslationException(
          "cycles in atomic blocks are not supported yet")

      (lastClauses get headPred) match {
        case Some(cls) => {
          for ((c, sync) <- cls)
            if (currentSync == ParametricEncoder.NoSync)
              chainClauses(c mergeWith currentClause, sync,
                           seenPreds + headPred)
            else if (sync == ParametricEncoder.NoSync)
              chainClauses(c mergeWith currentClause, currentSync,
                           seenPreds + headPred)
            else
              throw new TranslationException(
                "Cannot execute " + currentSync + " and " + sync +
                " in one step")

          // add further assertion clauses, since some intermediate
          // states disappear
          for (c <- assertionClauses.toList)
            if (c.bodyPredicates contains headPred) {
              if (currentSync != ParametricEncoder.NoSync)
                throw new TranslationException(
                  "Cannot execute " + currentSync + " and an assertion" +
                  " in one step")
              assertionClauses += (c mergeWith currentClause)
            }
        }
        case None =>
          clauses += ((currentClause, currentSync))
      }
    }

    for ((c, sync) <- entryClauses)
      chainClauses(c, sync, c.bodyPredicates)
  }

  private var atomicMode = false

  private def inAtomicMode[A](comp : => A) : A = {
      val oldAtomicMode = atomicMode
      atomicMode = true
      val res = comp
      atomicMode = oldAtomicMode
      res
  }

  private var prefix : String = ""
  private var locationCounter = 0

  private def setPrefix(pref : String) = {
    prefix = pref
    locationCounter = 0
  }

  private def newPred : Predicate = newPred(0)

  private def newPred(extraArgs : Int) : Predicate = {
    val res = new Predicate(prefix + locationCounter,
                            allFormalVars.size + extraArgs)
    locationCounter = locationCounter + 1
    res
  }

  //////////////////////////////////////////////////////////////////////////////

  /** Implicit conversion so that we can get a Scala-like iterator from a
    * a Java list */
  import scala.collection.JavaConversions.{asScalaBuffer, asScalaIterator}

  private def translateProgram(prog : Program) : Unit = {
    // First collect all declarations. This is a bit more
    // generous than actual C semantics, where declarations
    // have to be in the right order

    atomicMode = true
    val globalVarSymex = Symex(null)

    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
      decl match {
        case decl : Global =>
          collectVarDecls(decl.dec_, true, globalVarSymex)

        case decl : Chan =>
          for (name <- decl.chan_def_.asInstanceOf[AChan].listcident_) {
            if (channels contains name)
              throw new TranslationException(
                "Channel " + name + " is already declared")
            channels.put(name, new ParametricEncoder.CommChannel(name))
          }

        case decl : Afunc => {
          val name = decl.function_def_ match {
            case f : NewFunc => getName(f.declarator_)
            case f : NewFuncInt => getName(f.declarator_)
          }

          if (functionDefs contains name)
            throw new TranslationException(
              "Function " + name + " is already declared")
          functionDefs.put(name, decl.function_def_)
        }

        case _ =>
          // nothing
      }

    globalVarsInit ++= globalVarSymex.getValues

    // then translate the threads
    atomicMode = false

    for (decl <- prog.asInstanceOf[Progr].listexternal_declaration_)
      decl match {
        case decl : Athread =>
          decl.thread_def_ match {
            case thread : SingleThread => {
              setPrefix(thread.cident_)
              val translator = FunctionTranslator.apply
              translator translateNoReturn thread.compound_stm_
              processes += ((clauses.toList, ParametricEncoder.Singleton))
              clauses.clear
            }
            case thread : ParaThread => {
              setPrefix(thread.cident_2)
              pushLocalFrame
              localVars += new ConstantTerm(thread.cident_1)
              val translator = FunctionTranslator.apply
              translator translateNoReturn thread.compound_stm_
              processes += ((clauses.toList, ParametricEncoder.Infinite))
              clauses.clear
              popLocalFrame
            }
          }

        case _ =>
          // nothing
      }

    // is there a global entry point in the program?
    (functionDefs get entryFunction) match {
      case Some(funDef) => {
        setPrefix(entryFunction)

        pushLocalFrame
        val exitPred = newPred(1)
        val stm = pushArguments(funDef)
        val entryPred = newPred
        output(Clause(atom(entryPred, allVarInits), List(), true))

        val translator = FunctionTranslator(exitPred)
        translator.translateWithReturn(stm, entryPred)

        processes += ((clauses.toList, ParametricEncoder.Singleton))
        clauses.clear
        
        popLocalFrame
      }
      case None =>
        warn("entry function \"" + entryFunction + "\" not found")
    }

    // remove assertions that are no longer connected to predicates
    // actually occurring in the system

    val allPreds =
      (for ((cls, _) <- processes.iterator;
            (c, _) <- cls.iterator;
            p <- c.predicates.iterator)
       yield p).toSet

    val remainingAssertions =
      assertionClauses filter { c => c.bodyPredicates subsetOf allPreds }
    assertionClauses.clear
    assertionClauses ++= remainingAssertions
  }

  //////////////////////////////////////////////////////////////////////////////

  private def collectVarDecls(dec : Dec,
                              global : Boolean,
                              values : Symex) : Unit = dec match {
    case decl : Declarators => {
      // just assume that the type is int for the time being

      for (initDecl <- decl.listinit_declarator_) initDecl match {
        case initDecl : OnlyDecl => {
          val name = getName(initDecl.declarator_)
          val directDecl =
            initDecl.declarator_.asInstanceOf[NoPointer].direct_declarator_

          directDecl match {
            case _ : NewFuncDec | _ : OldFuncDef | _ : OldFuncDec =>
              functionDecls.put(name, directDecl)
            case _ => {
              val c = new ConstantTerm(name)
              (if (global) globalVars else localVars) += c
              values addValue CCIntTerm(c)
            }
          }
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
    case decl : Name      => decl.cident_
    case decl : ParenDecl => getName(decl.declarator_)
    case dec : NewFuncDec => getName(dec.direct_declarator_)
    case dec : OldFuncDef => getName(dec.direct_declarator_)
    case dec : OldFuncDec => getName(dec.direct_declarator_)
  }

  //////////////////////////////////////////////////////////////////////////////

  private object Symex {
    def apply(initPred : Predicate) = {
      val values = new ArrayBuffer[CCExpr]
      for (t <- allFormalVars)
        values += CCIntTerm(t)
      new Symex(initPred, values)
    }
  }

  private def atom(pred : Predicate, args : Seq[ITerm]) =
    IAtom(pred, args take pred.arity)

  private class Symex private (oriInitPred : Predicate,
                               values : Buffer[CCExpr]) {
    private var guard : IFormula = true

    private def addGuard(f : IFormula) : Unit = {
      guard = guard &&& f
      touchedGlobalState =
        touchedGlobalState || !freeFromGlobal(f)
    }

    private var initAtom =
      if (oriInitPred == null)
        null
      else
        atom(oriInitPred, allFormalVars)
    private def initPred = initAtom.pred

    private val savedStates = new Stack[(IAtom, Seq[CCExpr], IFormula, Boolean)]
    def saveState =
      savedStates push ((initAtom, values.toList, guard, touchedGlobalState))
    def restoreState = {
      val (oldAtom, oldValues, oldGuard, oldTouched) = savedStates.pop
      initAtom = oldAtom
      values.clear
      oldValues copyToBuffer values
      localVars reduceToSize (values.size - globalVars.size)
      guard = oldGuard
      touchedGlobalState = oldTouched
    }

    private def atomValuesUnchanged = {
      val (oldAtom, oldValues, _, _) = savedStates.top
      initAtom == oldAtom &&
      ((values.iterator zip oldValues.iterator) forall {
         case (x, y) => x == y
       })
    }

    private var touchedGlobalState : Boolean = false

    private def maybeOutputClause : Unit =
      if (!atomicMode && touchedGlobalState) outputClause

    private def pushVal(v : CCExpr) = {
//println("push " + v)
      addValue(v)
      // reserve a local variable, in case we need one later
      localVars += new ConstantTerm("__eval" + localVars.size)
    }

    private def pushFormalVal = {
      val c = new ConstantTerm("__eval" + localVars.size)
      localVars += c
      addValue(CCIntTerm(c))
    }

    private def popVal = {
      val res = values.last
//println("pop " + res)
      values trimEnd 1
      localVars trimEnd 1
      res
    }
    private def topVal = values.last

    private def outputClause : Unit = outputClause(newPred)

    def outputClause(pred : Predicate) : Unit = {
      if (initAtom == null)
        throw new TranslationException("too complicated initialiser")
      output(Clause(asAtom(pred), List(initAtom), guard))
      resetFields(pred)
    }

    def outputClause(headAtom : IAtom) : Unit =
      output(Clause(headAtom, List(initAtom), guard))

    def resetFields(pred : Predicate) : Unit = {
      initAtom = atom(pred, allFormalVars)
      guard = true
      touchedGlobalState = false
      for ((t, i) <- allFormalVars.iterator.zipWithIndex)
        values(i) = CCIntTerm(t)
    }

    def outputITEClauses(cond : IFormula,
                         thenPred : Predicate, elsePred : Predicate) = {
      saveState
      addGuard(cond)
      outputClause(thenPred)
      restoreState
      addGuard(~cond)
      outputClause(elsePred)
    }

    def addValue(t : CCExpr) = {
      values += t
      touchedGlobalState = touchedGlobalState || !freeFromGlobal(t)
    }

    private def getValue(name : String) =
      values(lookupVar(name))
    private def setValue(name : String, t : CCExpr) = {
      val ind = lookupVar(name)
      values(ind) = t
      touchedGlobalState =
        touchedGlobalState || ind < globalVars.size || !freeFromGlobal(t)
    }

    def getValues : Seq[CCExpr] =
      values.toList
    def getValuesAsTerms : Seq[ITerm] =
      for (expr <- values.toList) yield expr.toTerm

    def asAtom(pred : Predicate) = atom(pred, getValuesAsTerms)

    private def asLValue(exp : Exp) : String = exp match {
      case exp : Evar => exp.cident_
      case exp =>
        throw new TranslationException(
                    "Can only handle assignments to variables, not " +
                    (printer print exp))
    }

    def eval(exp : Exp) : CCExpr = {
      val initSize = values.size
      evalHelp(exp)
      val res = popVal
      assert(initSize == values.size)
      res
    }

    def atomicEval(exp : Exp) : CCExpr = atomicEval(List(exp))

    def atomicEval(exps : Seq[Exp]) : CCExpr = {
      val currentClauseNum = clauses.size
      val initSize = values.size

      inAtomicMode {
        pushVal(CCFormula(true))
        for (exp <- exps) {
          popVal
          evalHelp(exp)
        }
      }

      if (currentClauseNum != clauses.size) {
        outputClause
        mergeClauses(currentClauseNum)
      }

      val res = popVal
      assert(initSize == values.size)
      res
    }

    private def evalHelp(exp : Exp) : Unit = exp match {
      case exp : Ecomma => {
        evalHelp(exp.exp_1)
        popVal
        maybeOutputClause
        evalHelp(exp.exp_2)
      }
      case exp : Eassign if (exp.assignment_op_.isInstanceOf[Assign]) => {
        evalHelp(exp.exp_2)
        maybeOutputClause
        setValue(asLValue(exp.exp_1), topVal)
      }
      case exp : Eassign => {
        evalHelp(exp.exp_1)
        maybeOutputClause
        evalHelp(exp.exp_2)
        maybeOutputClause
        val rhs = popVal.toTerm
        val lhs = popVal.toTerm
        val newVal = CCIntTerm(exp.assignment_op_ match {
          case _ : AssignMul =>
            lhs * rhs
          case _ : AssignDiv =>
            ap.theories.BitShiftMultiplication.tDiv(lhs, rhs)
          case _ : AssignMod =>
            ap.theories.BitShiftMultiplication.tMod(lhs, rhs)
          case _ : AssignAdd =>
            lhs + rhs
          case _ : AssignSub =>
            lhs - rhs
//          case _ : AssignLeft.   Assignment_op ::= "<<=" ;
//          case _ : AssignRight.  Assignment_op ::= ">>=" ;
//          case _ : AssignAnd.    Assignment_op ::= "&=" ;
//          case _ : AssignXor.    Assignment_op ::= "^=" ;
//          case _ : AssignOr.     Assignment_op ::= "|=" ;
        })
        pushVal(newVal)
        setValue(asLValue(exp.exp_1), newVal)
      }
      case exp : Econdition => {
        val cond = eval(exp.exp_1).toFormula

        saveState
        addGuard(cond)
        evalHelp(exp.exp_2)
        outputClause
        val intermediatePred = initPred

        restoreState
        addGuard(~cond)
        evalHelp(exp.exp_3)
        outputClause(intermediatePred)
      }
      case exp : Elor => {
        val cond = eval(exp.exp_1).toFormula

        saveState
        addGuard(~cond)
        val newGuard = guard
        evalHelp(exp.exp_2)
        maybeOutputClause

        // check whether the second expression had side-effects
        if ((guard eq newGuard) && atomValuesUnchanged) {
          val cond2 = popVal.toFormula
          restoreState
          pushVal(CCFormula(cond ||| cond2))
        } else {
          outputClause
          val intermediatePred = initPred

          restoreState
          addGuard(cond)
          pushVal(CCFormula(true))
          outputClause(intermediatePred)
        }
      }
      case exp : Eland => {
        val cond = eval(exp.exp_1).toFormula

        saveState
        addGuard(cond)
        val newGuard = guard
        evalHelp(exp.exp_2)
        maybeOutputClause

        // check whether the second expression had side-effects
        if ((guard eq newGuard) && atomValuesUnchanged) {
          val cond2 = popVal.toFormula
          restoreState
          pushVal(CCFormula(cond &&& cond2))
        } else {
          outputClause
          val intermediatePred = initPred

          restoreState
          addGuard(~cond)
          pushVal(CCFormula(false))
          outputClause(intermediatePred)
        }
      }
//      case exp : Ebitor.      Exp6  ::= Exp6 "|" Exp7;
//      case exp : Ebitexor.    Exp7  ::= Exp7 "^" Exp8;
//      case exp : Ebitand.     Exp8  ::= Exp8 "&" Exp9;
      case exp : Eeq =>
        strictBinPred(exp.exp_1, exp.exp_2, _ === _)
      case exp : Eneq =>
        strictBinPred(exp.exp_1, exp.exp_2, _ =/= _)
      case exp : Elthen =>
        strictBinPred(exp.exp_1, exp.exp_2, _ < _)
      case exp : Egrthen =>
        strictBinPred(exp.exp_1, exp.exp_2, _ > _)
      case exp : Ele =>
        strictBinPred(exp.exp_1, exp.exp_2, _ <= _)
      case exp : Ege =>
        strictBinPred(exp.exp_1, exp.exp_2, _ >= _)
//      case exp : Eleft.       Exp11 ::= Exp11 "<<" Exp12;
//      case exp : Eright.      Exp11 ::= Exp11 ">>" Exp12;
      case exp : Eplus =>
        strictBinFun(exp.exp_1, exp.exp_2, _ + _)
      case exp : Eminus =>
        strictBinFun(exp.exp_1, exp.exp_2, _ - _)
      case exp : Etimes =>
        strictBinFun(exp.exp_1, exp.exp_2, _ * _)
      case exp : Ediv =>
        strictBinFun(exp.exp_1, exp.exp_2, {
          (x : ITerm, y : ITerm) =>
            ap.theories.BitShiftMultiplication.tDiv(x, y)
        })
      case exp : Emod =>
        strictBinFun(exp.exp_1, exp.exp_2, {
          (x : ITerm, y : ITerm) =>
            ap.theories.BitShiftMultiplication.tMod(x, y)
        })
//      case exp : Etypeconv.   Exp14 ::= "(" Type_name ")" Exp14;
      case exp : Epreinc => {
        evalHelp(exp.exp_)
        maybeOutputClause
        pushVal(CCIntTerm(popVal.toTerm + 1))
        setValue(asLValue(exp.exp_), topVal)
      }
      case exp : Epredec => {
        evalHelp(exp.exp_)
        maybeOutputClause
        pushVal(CCIntTerm(popVal.toTerm - 1))
        setValue(asLValue(exp.exp_), topVal)
      }
      case exp : Epreop => {
        evalHelp(exp.exp_)
        exp.unary_operator_ match {
//          case _ : Address.     Unary_operator ::= "&" ;
//          case _ : Indirection. Unary_operator ::= "*" ;
          case _ : Plus       => // nothing
          case _ : Negative   => pushVal(CCIntTerm(-popVal.toTerm))
//          case _ : Complement.  Unary_operator ::= "~" ;
          case _ : Logicalneg => pushVal(CCFormula(~popVal.toFormula))
        }
      }
//      case exp : Ebytesexpr.  Exp15 ::= "sizeof" Exp15;
//      case exp : Ebytestype.  Exp15 ::= "sizeof" "(" Type_name ")";
//      case exp : Earray.      Exp16 ::= Exp16 "[" Exp "]" ;

      case exp : Efunk => {
        // inline the called function
        val name = printer print exp.exp_
        outputClause
        callFunctionInlining(name, initPred)
      }

      case exp : Efunkpar => (printer print exp.exp_) match {
        case "assert" | "static_assert" if (exp.listexp_.size == 1) => {
          import HornClauses._
          val property = atomicEval(exp.listexp_.head).toFormula
          assertionClauses += (property :- (initAtom, guard))
          pushVal(CCFormula(true))
        }
        case "assume" if (exp.listexp_.size == 1) => {
          addGuard(atomicEval(exp.listexp_.head).toFormula)
          pushVal(CCFormula(true))
        }
        case name => {
          // then we inline the called function

          // evaluate the arguments
          for (e <- exp.listexp_)
            evalHelp(e)
          outputClause

          val functionEntry = initPred

          // get rid of the local variables, which are later
          // replaced with the formal arguments
          for (e <- exp.listexp_)
            popVal

          callFunctionInlining(name, functionEntry)
        }
      }

//      case exp : Eselect.     Exp16 ::= Exp16 "." Ident;
//      case exp : Epoint.      Exp16 ::= Exp16 "->" Ident;
      case exp : Epostinc => {
        evalHelp(exp.exp_)
        maybeOutputClause
        setValue(asLValue(exp.exp_), CCIntTerm(topVal.toTerm + 1))
      }
      case exp : Epostdec => {
        evalHelp(exp.exp_)
        maybeOutputClause
        setValue(asLValue(exp.exp_), CCIntTerm(topVal.toTerm - 1))
      }
      case exp : Evar =>
        pushVal(getValue(exp.cident_))
      case exp : Econst =>
        evalHelp(exp.constant_)
//      case exp : Estring.     Exp17 ::= String;
    }

    private def callFunctionInlining(name : String,
                                     functionEntry : Predicate) = {
      val functionExit = newPred(1)

      (functionDefs get name) match {
        case Some(fundef) => {
          inlineFunction(fundef, functionEntry, functionExit)

          // reserve an argument for the function result
          pushFormalVal
          resetFields(functionExit)
        }
        case None => (functionDecls get name) match {
          case Some(fundecl) => {
            warn("no definition of function \"" + name + "\" available")
            pushFormalVal
          }
          case None =>
            throw new TranslationException(
              "Function " + name + " is not declared")
        }
      }
    }

    private def strictBinOp(left : Exp, right : Exp,
                            op : (CCExpr, CCExpr) => CCExpr) : Unit = {
      evalHelp(left)
      maybeOutputClause
      evalHelp(right)
      val rhs = popVal
      val lhs = popVal
      pushVal(op(lhs, rhs))
    }

    private def strictBinFun(left : Exp, right : Exp,
                             op : (ITerm, ITerm) => ITerm) : Unit =
      strictBinOp(left, right,
                  (lhs : CCExpr, rhs : CCExpr) =>
                    CCIntTerm(op(lhs.toTerm, rhs.toTerm)))

    private def strictBinPred(left : Exp, right : Exp,
                              op : (ITerm, ITerm) => IFormula) : Unit =
      strictBinOp(left, right,
                  (lhs : CCExpr, rhs : CCExpr) =>
                    CCFormula(op(lhs.toTerm, rhs.toTerm)))

    private def evalHelp(constant : Constant) : Unit = constant match {
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
        pushVal(CCIntTerm(IdealInt(constant.octal_, 8)))
//      case constant : Eoctalunsign.  Constant ::= OctalUnsigned;
//      case constant : Eoctallong.    Constant ::= OctalLong;
//      case constant : Eoctalunslong. Constant ::= OctalUnsLong;
//      case constant : Ecdouble.      Constant ::= CDouble;
//      case constant : Ecfloat.       Constant ::= CFloat;
//      case constant : Eclongdouble.  Constant ::= CLongDouble;
      case constant : Eint =>
        pushVal(CCIntTerm(i(constant.integer_)))
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def inlineFunction(functionDef : Function_def,
                             entry : Predicate,
                             exit : Predicate) : Unit = {
    pushLocalFrame
    val stm = pushArguments(functionDef)

    assert(entry.arity == allFormalVars.size)

    val translator = FunctionTranslator(exit)
    translator.translateWithReturn(stm, entry)

    popLocalFrame
  }

  private def pushArguments(functionDef : Function_def) : Compound_stm = {
    val (declarator, stm) = functionDef match {
      case f : NewFunc    => (f.declarator_, f.compound_stm_)
      case f : NewFuncInt => (f.declarator_, f.compound_stm_)
    }

    declarator.asInstanceOf[NoPointer].direct_declarator_ match {
      case dec : NewFuncDec =>
        for (argDec <- dec.parameter_type_.asInstanceOf[AllSpec]
                          .listparameter_declaration_)
          argDec match {
            case argDec : OnlyType =>
              // ignore, a void argument implies that there are no arguments
            case argDec : TypeAndParam =>
              localVars += new ConstantTerm(getName(argDec.declarator_))
//            case argDec : Abstract =>
          }
      case dec : OldFuncDef =>
        for (ident <- dec.listcident_)
          localVars += new ConstantTerm(ident)
      case dec : OldFuncDec =>
        // no arguments
    }

    stm
  }

  //////////////////////////////////////////////////////////////////////////////

  private object FunctionTranslator {
    def apply =
      new FunctionTranslator(None)
    def apply(returnPred : Predicate) =
      new FunctionTranslator(Some(returnPred))
  }

  private class FunctionTranslator private (returnPred : Option[Predicate]) {

    private def symexFor(initPred : Predicate,
                         stm : Expression_stm) : (Symex, Option[CCExpr]) = {
      val exprSymex = Symex(initPred)
      val res = stm match {
        case _ : SexprOne => None
        case stm : SexprTwo => Some(exprSymex eval stm.exp_)
      }
      (exprSymex, res)
    }

    def translateNoReturn(compound : Compound_stm) : Unit = {
      val entry = newPred
      output(Clause(atom(entry, allVarInits), List(), true))
      translate(compound, entry, newPred)
      postProcessClauses
    }

    def translateWithReturn(stm : Compound_stm,
                            entry : Predicate) : Unit = {
      val finalPred = newPred
      translate(stm, entry, finalPred)
      // add a default return edge
      val rp = returnPred.get
      output(Clause(atom(rp, (allFormalVars take (rp.arity - 1)) ++
                             List(IConstant(new ConstantTerm("__result")))),
                    List(atom(finalPred, allFormalVars)),
                    true))
      postProcessClauses
    }

    ////////////////////////////////////////////////////////////////////////////

    private def postProcessClauses : Unit = {
      connectJumps
      mergeAtomicBlocks
    }    

    private def connectJumps : Unit =
      for ((label, jumpPred, jumpVars, position) <- jumpLocs)
        (labelledLocs get label) match {
          case Some((targetPred, targetVars)) => {
            val commonVars =
              (jumpVars zip targetVars).takeWhile({
                case (x, y) => x == y
              }).map(_._1)
            val jumpArgs = commonVars ++ (
              for (i <- 0 until (jumpPred.arity - commonVars.size))
              yield IConstant(new ConstantTerm("preArg_" + i)))
            val targetArgs = commonVars ++ (
              for (i <- 0 until (targetPred.arity - commonVars.size))
              yield IConstant(new ConstantTerm("postArg_" + i)))
            clauses(position) = (Clause(atom(targetPred, targetArgs),
                                        List(atom(jumpPred, jumpArgs)),
                                        true),
                                 ParametricEncoder.NoSync)
            usedJumpTargets.put(targetPred, label)
          }
          case None =>
            throw new TranslationException("cannot goto label " + label)
        }

    private def mergeAtomicBlocks : Unit = if (!atomicBlocks.isEmpty) {
      val sortedBlocks =
        atomicBlocks sortWith { case ((s1, e1), (s2, e2)) =>
                                  s1 < s2 || (s1 == s2 && e1 > e2) }

      val offset = sortedBlocks.head._1
      var concernedClauses = clauses.slice(offset, clauses.size).toList
      clauses reduceToSize offset

      var curPos = offset
      for ((bstart, bend) <- sortedBlocks)
        if (bstart >= curPos) {
          while (curPos < bend) {
            clauses += concernedClauses.head
            concernedClauses = concernedClauses.tail
            curPos = curPos + 1
          }
          mergeClauses(clauses.size - (bend - bstart))
        }

      clauses ++= concernedClauses

      val bodyPreds =
        (for ((c, _) <- clauses.iterator; p <- c.bodyPredicates.iterator)
         yield p).toSet

      for ((Clause(IAtom(pred, _), _, _), _) <- clauses.iterator)
        if (!(bodyPreds contains pred) && (usedJumpTargets contains pred))
          throw new TranslationException("cannot goto label " +
                                         usedJumpTargets(pred) +
                                         ", which was eliminated due to " +
                                         "atomic blocks")
    }

    private val jumpLocs =
      new ArrayBuffer[(String, Predicate, Seq[ITerm], Int)]
    private val labelledLocs =
      new MHashMap[String, (Predicate, Seq[ITerm])]
    private val usedJumpTargets =
      new MHashMap[Predicate, String]
    private val atomicBlocks =
      new ArrayBuffer[(Int, Int)]

    ////////////////////////////////////////////////////////////////////////////

    private def translate(stm : Stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = stm match {
      case stm : LabelS =>
        translate(stm.labeled_stm_, entry, exit)
      case stm : CompS =>
        translate(stm.compound_stm_, entry, exit)
      case stm : ExprS =>
        symexFor(entry, stm.expression_stm_)._1 outputClause exit
      case stm : SelS =>
        translate(stm.selection_stm_, entry, exit)
      case stm : IterS =>
        translate(stm.iter_stm_, entry, exit)
      case stm : JumpS =>
        translate(stm.jump_stm_, entry, exit)
      case stm : AtomicS =>
        translate(stm.atomic_stm_, entry, exit)
    }

    private def translate(dec : Dec, entry : Predicate) : Predicate = {
      val decSymex = Symex(entry)
      collectVarDecls(dec, false, decSymex)
      val exit = newPred
      decSymex outputClause exit
      exit
    }

    private def translate(stm : Labeled_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = stm match {
      case stm : SlabelOne => { // Labeled_stm ::= CIdent ":" Stm ;
        if (labelledLocs contains stm.cident_)
          throw new TranslationException("multiple labels " + stm.cident_)
        labelledLocs.put(stm.cident_, (entry, allFormalVars))
        translate(stm.stm_, entry, exit)
      }
      //-- SlabelTwo.   Labeled_stm ::= "case" Constant_expression ":" Stm ;
      //SlabelThree. Labeled_stm ::= "default" ":" Stm;
    }

    private def translate(compound : Compound_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = compound match {
      case compound : ScompOne => {
        val vars = allFormalVars
        output(Clause(atom(exit, vars), List(atom(entry, vars)), true))
      }
      case compound : ScompTwo => {
        pushLocalFrame

        val stmsIt = compound.liststm_.iterator
        var prevPred = entry
        while (stmsIt.hasNext)
          stmsIt.next match {
            case stm : DecS => {
              prevPred = translate(stm.dec_, prevPred)
              if (!stmsIt.hasNext)
                output(Clause(atom(exit, allFormalVars),
                              List(atom(prevPred, allFormalVars)),
                              true))
            }
            case stm => {
              val nextPred = if (stmsIt.hasNext) newPred else exit
              translate(stm, prevPred, nextPred)
              prevPred = nextPred
            }
          }

        popLocalFrame
      }

/*
      case compound : ScompThree => {
        pushLocalFrame

        var prevPred = entry
        for (dec <- compound.listdec_)
          prevPred = translate(dec, prevPred)

        val lastAtom = atom(prevPred, allFormalVars)

        popLocalFrame

        output(Clause(atom(exit, allFormalVars), List(lastAtom), true))
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
*/
    }

    var innermostLoopCont : Predicate = null
    var innermostLoopExit : Predicate = null

    private def withinLoop[A](
                     loopCont : Predicate, loopExit : Predicate)
                     (comp : => A) : A = {
      val oldCont = innermostLoopCont
      val oldExit = innermostLoopExit
      innermostLoopCont = loopCont
      innermostLoopExit = loopExit
      try {
        comp
      } finally {
        innermostLoopCont = oldCont
        innermostLoopExit = oldExit
      }
    }

    private def translate(stm : Iter_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = stm match {
      case stm : SiterOne => {
        // while loop

        val first = newPred
        val condSymex = Symex(entry)
        val cond = (condSymex eval stm.exp_).toFormula
        condSymex.outputITEClauses(cond, first, exit)
        withinLoop(entry, exit) {
          translate(stm.stm_, first, entry)
        }
      }

      case stm : SiterTwo => {
        // do ... while loop

        val first = newPred
        withinLoop(first, exit) {
          translate(stm.stm_, entry, first)
        }

        val condSymex = Symex(first)
        val cond = (condSymex eval stm.exp_).toFormula
        condSymex.outputITEClauses(cond, entry, exit)
      }

      case _ : SiterThree | _ : SiterFour => {
        // for loop

        val first, second, third = newPred

        val (initStm, condStm, body) = stm match {
          case stm : SiterThree =>
            (stm.expression_stm_1, stm.expression_stm_2, stm.stm_)
          case stm : SiterFour  =>
            (stm.expression_stm_1, stm.expression_stm_2, stm.stm_)
        }

        symexFor(entry, initStm)._1 outputClause first

        val (condSymex, condExpr) = symexFor(first, condStm)
        val cond : IFormula = condExpr match {
          case Some(expr) => expr.toFormula
          case None       => true
        }

        condSymex.outputITEClauses(cond, second, exit)

        withinLoop(third, exit) {
          translate(body, second, third)
        }
        
        stm match {
          case stm : SiterThree =>
            output(Clause(atom(first, allFormalVars),
                          List(atom(third, allFormalVars)), true))
          case stm : SiterFour  => {
            val incSymex = Symex(third)
            incSymex eval stm.exp_
            incSymex outputClause first
          }
        }
      }
    }

    private def translate(stm : Selection_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = stm match {
      case _ : SselOne | _ : SselTwo => {
        val first, second = newPred
        val vars = allFormalVars
        val condSymex = Symex(entry)
        val cond = stm match {
          case stm : SselOne => (condSymex eval stm.exp_).toFormula
          case stm : SselTwo => (condSymex eval stm.exp_).toFormula
        }
        condSymex.outputITEClauses(cond, first, second)
        stm match {
          case stm : SselOne => {
            translate(stm.stm_, first, exit)
            output(Clause(atom(exit, vars), List(atom(second, vars)), true))
          }
          case stm : SselTwo => {
            translate(stm.stm_1, first, exit)
            translate(stm.stm_2, second, exit)
          }
        }
      }
//      case stm : SselThree.  Selection_stm ::= "switch" "(" Exp ")" Stm ;
    }

    private def translate(jump : Jump_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = jump match {
      case jump : SjumpOne => { // goto
        jumpLocs += ((jump.cident_, entry, allFormalVars, clauses.size))
        // reserve space for the later jump clause
        output(null)
      }
      case jump : SjumpTwo => { // continue
        if (innermostLoopCont == null)
          throw new TranslationException(
            "\"continue\" can only be used within loops")
        Symex(entry) outputClause innermostLoopCont
      }
      case jump : SjumpThree => { // break
        if (innermostLoopExit == null)
          throw new TranslationException(
            "\"break\" can only be used within loops")
        Symex(entry) outputClause innermostLoopExit
      }
      case jump : SjumpFour => // return
        returnPred match {
          case Some(rp) => {
            val args = (allFormalVars take (rp.arity - 1)) ++
                       List(IConstant(new ConstantTerm("__result")))
            output(Clause(atom(rp, args),
                          List(atom(entry, allFormalVars)),
                          true))
          }
          case None =>
            throw new TranslationException(
              "\"return\" can only be used within functions")
        }
      case jump : SjumpFive => { // return exp
        val symex = Symex(entry)
        val retValue = symex eval jump.exp_
        returnPred match {
          case Some(rp) => {
            val args = (symex.getValuesAsTerms take (rp.arity - 1)) ++
                       List(retValue.toTerm)
            symex outputClause atom(rp, args)
          }
          case None =>
            throw new TranslationException(
              "\"return\" can only be used within functions")
        }
      }
    }

    private def translate(aStm : Atomic_stm,
                          entry : Predicate,
                          exit : Predicate) : Unit = aStm match {
      case stm : SatomicOne => {
        val currentClauseNum = clauses.size
        inAtomicMode {
          translate(stm.stm_, entry, exit)
        }
        atomicBlocks += ((currentClauseNum, clauses.size))
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  val (system, assertions) : (ParametricEncoder.System,
                              Seq[HornClauses.Clause]) = {
    def entry(parser : concurrentC.parser) = parser.pProgram
    val prog = parseWithEntry(input, entry _)
//    println(printer print prog)
    translateProgram(prog)

    val singleThreaded =
      processes.size == 1 &&
      processes.head._2 == ParametricEncoder.Singleton

    (ParametricEncoder.System(processes.toList,
                              if (singleThreaded) 0 else globalVars.size,
                              None,
                              ParametricEncoder.NoTime,
                              List()),
     assertionClauses.toList)
  }

}