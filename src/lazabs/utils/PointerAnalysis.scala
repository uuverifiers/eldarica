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

package lazabs.utils
/**
 * Pointer analysis for actors
 * After pointer analysis all the actor references are converted to integers 
 */

import lazabs.ast.ASTree._
import lazabs.types._

object PointerAnalysis {
  /**
   * map from the actor instance to its class name
   */
  var actorInstance2ClassName = Map[String,String]()
  /**
   * information for class actor name
   */
  var classActorName2Params =  Map[String,List[Parameter]]()
  var classActorName2TypeID =  Map[String,Int]()
  /**
   * information for singleton actor name
   */
  var singletonActorName2ID =  Map[String,Int]("main" -> 0)
  /**
   * each actor has a unique ID
   */
  private var curActorID = 0
  /**
   * the current actor name
   */
  private var curActorName = "main" 

  def apply(e: Expression): Expression = e match {
    case Block(declList) => Block(this(declList)).stype(e.stype)
    case IfThenElse(cond, conseq, altern) => IfThenElse(cond, this(conseq), this(altern)).stype(e.stype)
    case WhileLoop(cond, body) => WhileLoop(cond, this(body)).stype(e.stype)
    case IfThen(cond, conseq) => IfThen(cond, this(conseq)).stype(e.stype)
      case Assignment(v@Variable(vname,_), CreateObject(cn,ps)) if (classActorName2TypeID.contains(cn)) =>
        if (classActorName2Params.getOrElse(cn,List()).size != ps.size) println("Insufficient number of parameters in actor generation")
        this(Block(List(Assignment(Variable("lastActorId").stype(IntegerType()),Addition(Variable("lastActorId").stype(IntegerType()),NumericalConst(1)))) :::
        classActorName2Params.getOrElse(cn,List()).zip(ps).map(pv =>
          Assignment(ArraySelect(ScArray(Some(Variable(cn + "_" + pv._1.name.drop(3)).stype(ArrayType(pv._1.typ))),None),Variable("lastActorId").stype(IntegerType())), pv._2)) :::           
            List(Assignment(ArraySelect(ScArray(Some(Variable("actorType").stype(ArrayType(IntegerType()))),None),Variable("lastActorId").stype(IntegerType())),
              NumericalConst(BigInt(classActorName2TypeID.getOrElse(cn,0))))) ::: 
        List(Assignment(Variable(vname).stype(IntegerType()),Variable("lastActorId").stype(IntegerType())))))
    case MemberAccess(e1, Variable("sc_start",_)) => e   // ignore "start" for the moment
    case MemberAccess(e1, Variable("sc_nextInt",_)) => e   // ignore "nextInt" for the moment
    case MemberAccess(c@Variable(classInstance,_), f@Variable(field,_)) if(actorInstance2ClassName.contains(classInstance)) =>
      ArraySelect(ScArray(Some(Variable(actorInstance2ClassName.getOrElse(classInstance,"") + "_" + field.drop(3)).stype(ArrayType(IntegerType()))),None),c)
      case SendMessage(receiver, message) =>
        val senderID = (if(singletonActorName2ID.contains(curActorName)) NumericalConst(BigInt(singletonActorName2ID.getOrElse(curActorName,-1))) else Variable("i").stype(IntegerType()))        
        var receiverID:Expression = receiver match {
          case Variable("sc_sender",_) => 
            ArraySelect(ArraySelect(ScArray(Some(Variable("senderbox").stype(ArrayType(ArrayType(IntegerType())))), None),senderID),
                ArraySelect(ScArray(Some(Variable("front").stype(ArrayType(IntegerType()))),None),senderID))
          case Variable("sc_self",_) if (singletonActorName2ID.contains(curActorName)) => NumericalConst(BigInt(singletonActorName2ID.getOrElse(curActorName,-1)))
            case Variable("sc_self",_) if (!singletonActorName2ID.contains(curActorName)) => Variable("i").stype(IntegerType())
            case Variable(receiverName,_) if (singletonActorName2ID.contains(receiverName)) => NumericalConst(BigInt(singletonActorName2ID.getOrElse(receiverName,-1)))
            case _ => receiver.stype(IntegerType())
        }
        this(Block(List(Assignment(ArraySelect(ArraySelect(ScArray(Some(Variable("mailbox").stype(ArrayType(ArrayType(IntegerType())))), None),receiverID),
            ArraySelect(ScArray(Some(Variable("rear").stype(ArrayType(IntegerType()))), None),receiverID)),message), 
        Assignment(ArraySelect(ArraySelect(ScArray(Some(Variable("senderbox").stype(ArrayType(ArrayType(IntegerType())))), None),receiverID),
            ArraySelect(ScArray(Some(Variable("rear").stype(ArrayType(IntegerType()))), None),receiverID)),senderID),     
        Assignment(ArraySelect(ScArray(Some(Variable("rear").stype(ArrayType(IntegerType()))), None),receiverID), 
            Addition(ArraySelect(ScArray(Some(Variable("rear").stype(ArrayType(IntegerType()))), None),receiverID), NumericalConst(1))))))
    case ActorLoop(declList) => ActorLoop(this(declList)).stype(e.stype)
    case FunctionCall(funcName, exprList) => FunctionCall(funcName, exprList.map(apply)).stype(e.stype)
    case Existential(v, qe) => (Existential(v, this(qe))).stype(e.stype)
    case Universal(v, qe) => Manip.deBruijnIndex(Universal(v, this(qe))).stype(e.stype)
    case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, this(e1), this(e2), this(e3)).stype(e.stype)      
    case BinaryExpression(e1, op, e2) => BinaryExpression(this(e1), op, this(e2)).stype(e.stype)
    case UnaryExpression(op, e) => UnaryExpression(op, this(e)).stype(e.stype)
    case ScArray(None,Some(v@Variable(_,_))) if (e.stype.isInstanceOf[ClassType]) =>
      ScArray(None,Some(v)).stype(ArrayType(IntegerType()))
    case Variable(name,d) => e.stype match {
      case ClassType(_) => Variable(name,d).stype(IntegerType())
      case _ => e
    }
    case Null() => NumericalConst(-1)
    case _ => e
  }
  
  def apply(decls: List[ASTree]): List[ASTree] = decls match {
    case Nil => Nil
    case FunctionDefinition(funcName, ps, t, e, post) :: rest =>
      FunctionDefinition(funcName, ps, t, this(e), post) :: this(rest)
    case VarDeclaration(name, _, CreateObject("sc_Random",ps)) :: rest =>  // ignore new Random for the moment
      VarDeclaration(name, IntegerType(), NumericalConst(0)) :: this(rest)
    case VarDeclaration(name, t@ClassType(cn1), Null()) :: rest =>
      actorInstance2ClassName += (name -> cn1)
      VarDeclaration(name, IntegerType(), NumericalConst(0)) :: this(rest)
    case VarDeclaration(name, t@ArrayType(ClassType(cn1)), value) :: rest =>
      VarDeclaration(name, ArrayType(IntegerType()), this(value)) :: this(rest)     
    case VarDeclaration(name, t@lazabs.types.ClassType(cn1), CreateObject(cn2,ps)) :: rest if (cn1 == cn2) =>
      actorInstance2ClassName += (name -> cn1)
      Assignment(Variable("lastActorId").stype(IntegerType()),Addition(Variable("lastActorId").stype(IntegerType()),NumericalConst(1))) ::   // lastActorId++
      classActorName2Params.getOrElse(cn1,List()).zip(ps).map(pv =>  // class are assigned
        Assignment(ArraySelect(ScArray(Some(Variable(cn1 + "_" + pv._1.name.drop(3)).stype(ArrayType(pv._1.typ))),None),Variable("lastActorId").stype(IntegerType())), pv._2)) :::
          List(Assignment(ArraySelect(ScArray(Some(Variable("actorType").stype(ArrayType(IntegerType()))),None),Variable("lastActorId").stype(IntegerType())),
            NumericalConst(BigInt(classActorName2TypeID.getOrElse(cn1,0)))),   // actorType(lastActorId) is set
      VarDeclaration(name, IntegerType(), Variable("lastActorId").stype(IntegerType()))) ::: this(rest)  // class declaration is converted to integer declaration 
    case VarDeclaration(name, t@lazabs.types.ClassType(cn1), value) :: rest =>
      actorInstance2ClassName += (name -> cn1)
      VarDeclaration(name, IntegerType(), value) :: this(rest)      
    case VarDeclaration(name, t, value) :: rest =>
      VarDeclaration(name, t, this(value)) :: this(rest)
    case PredsDeclaration(preds) :: rest =>
      PredsDeclaration(this(preds)) :: this(rest)
    case SingletonActorDeclaration(name, ads) :: rest =>
      curActorName = name
      curActorID = curActorID + 1
      singletonActorName2ID += (name -> curActorID)
      val analyzedSingletonActorDeclaration = SingletonActorDeclaration(name, this(ads)).stype(decls.head.stype)
      curActorName = "main"
      analyzedSingletonActorDeclaration :: this(rest)
    case ClassDeclaration(className, paramList, Some("sc_Actor"), ads) :: rest =>
      curActorName = className
      curActorID = curActorID + 1
      classActorName2Params += (className -> paramList)
      classActorName2TypeID += (className -> curActorID)
      val analyzedClassDeclaration = ClassDeclaration(className, paramList, Some("sc_Actor"), this(ads)) 
      curActorName = "main"
      analyzedClassDeclaration :: this(rest)
    case CaseClause(pattern, cond, e) :: rest =>
      CaseClause(pattern, cond, this(e)).stype(decls.head.stype) :: this(rest)
    case ReactBlock(cases) :: rest => ReactBlock(this(cases).asInstanceOf[List[CaseClause]]).stype(decls.head.stype) :: this(rest)
    case Predicate(e, cs) :: rest => Predicate(this(e), apply(cs).asInstanceOf[List[Predicate]]) :: this(rest)
    case (e:Expression) :: rest =>
      this(e) :: this(rest)
    case _ :: rest =>
      decls.head :: this(rest)
  }
  def apply(o: Sobject): Sobject = {
    Sobject(apply(o.preds), o.name, apply(o.defs).asInstanceOf[List[Declaration]])
  } 
}