/**
 * Copyright (c) 2011-2015 Hossein Hojjat, Philipp Ruemmer. All rights reserved.
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

package lazabs.types

import lazabs.ast.ASTree._
import lazabs.types._

// performs basic type checking for the moment; just assign types to variables according to the environment

object TypeCheck{
  /**
   * The environment at each point of the program execution
   */
  case class Environ(tpe: Map[String,Type], arrSize: Map[String,Expression])
  /**
   * global predicates which are directly defined in the object
   */
  private var globalPredicates: List[Predicate] = List()
  
  val actorQueues: Map[String,Type] = Map("mailbox" -> ArrayType(ArrayType(IntegerType()))) + ("rear" -> ArrayType(IntegerType())) +
    ("front" -> ArrayType(IntegerType())) + ("senderbox" -> ArrayType(ArrayType(IntegerType())))
  /**
   * extracts the global environment of a function
   */
  def globalEnviron(so: Sobject): Environ = so.defs match {
    case Nil => Environ(Map.empty,Map.empty)
    case VarDeclaration(name, ArrayType(t), ScArray(_, Some(aLength))) :: ds =>
      val Environ(gTpe, gArrSize) = globalEnviron(Sobject(so.preds, so.name, ds))
      Environ(gTpe + (name -> ArrayType(t)), gArrSize + (name -> aLength))
    case VarDeclaration(name, ArrayType(t), ArrayConst(l)) :: ds =>
      val Environ(gTpe, gArrSize) = globalEnviron(Sobject(so.preds, so.name, ds))
      Environ(gTpe + (name -> ArrayType(t)), gArrSize + (name -> NumericalConst(l.size)))
    case VarDeclaration(name, t, value) :: ds => 
      val Environ(gTpe, gArrSize) = globalEnviron(Sobject(so.preds, so.name, ds))
      Environ(gTpe + (name -> t), gArrSize)
    case SingletonActorDeclaration(name, a) :: ds =>
      val Environ(gTpe, gArrSize) = globalEnviron(Sobject(so.preds, so.name, ds))
      Environ(gTpe ++ actorQueues + (name -> ActorType), gArrSize)
    case ClassDeclaration(className, paramList, Some("sc_Actor"), declList) :: ds =>
      val classFields = (paramList.map(param => (param.name,param.typ)) ::: (for (VarDeclaration(name, t, value) <- declList)
        yield (name,t))).map(x => ((className + "_" + x._1.drop(3)) -> ArrayType(x._2 match {
          case ClassType(_) => IntegerType()
          case _ => x._2
        })))
      val Environ(gTpe, gArrSize) = globalEnviron(Sobject(so.preds, so.name, ds))
      val result = Environ(gTpe ++ classFields ++ actorQueues + (className -> ClassType("sc_Actor")) + ("i" -> IntegerType()) + ("lastActorId" -> IntegerType()) + 
        ("actorType" -> ArrayType(IntegerType())), gArrSize)
      result 
    case PredsDeclaration(preds) :: ds =>
      globalPredicates :::= preds.asInstanceOf[List[Predicate]]
      globalEnviron(Sobject(so.preds, so.name, ds))
    case _ :: ds => globalEnviron(Sobject(so.preds, so.name, ds))  
  }
  
  def apply(so: Sobject): Sobject = {
    val global = globalEnviron(so)
    Sobject(typeCheck(so.preds ::: globalPredicates,global).asInstanceOf[List[ASTree]], so.name, typeCheck(so.defs,global).asInstanceOf[List[Declaration]])
  }
  
  def typeCheck(declList : List[ASTree], env: Environ): List[ASTree] = declList match {
    case Nil => Nil
    case VarDeclaration(name, ArrayType(t), ScArray(_, Some(aLength))) :: rest =>
      declList.head :: typeCheck(rest, Environ(env.tpe + (name -> ArrayType(t)), env.arrSize + (name -> aLength)))
    case VarDeclaration(name, ArrayType(t), ArrayConst(l)) :: rest =>
      declList.head :: typeCheck(rest, Environ(env.tpe + (name -> ArrayType(t)), env.arrSize + (name -> NumericalConst(l.size))))
    case VarDeclaration(name, t, value) :: rest =>
      VarDeclaration(name, t, typeCheck(value,env)) :: typeCheck(rest, Environ(env.tpe + (name -> t), env.arrSize))
    case PredsDeclaration(preds) :: rest =>  //LBE is just for large block encoding
      PredsDeclaration(typeCheck(preds,Environ(env.tpe + ("sc_LBE" -> UnitType()), env.arrSize))) :: typeCheck(rest, env)     
    case SingletonActorDeclaration(name, declList)  :: rest =>
      val newEnv = Environ(env.tpe + (name -> ActorType), env.arrSize)
      SingletonActorDeclaration(name, typeCheck(declList,newEnv)) :: typeCheck(rest, newEnv)
    case FunctionDefinition(funcName, ps, t, e, Some((binding,post))) :: rest =>
      val funcEnv = Environ(env.tpe ++ (ps.map(p => (p.name, p.typ))), env.arrSize)
      val typeCheckedBody = typeCheck(e, funcEnv)
      FunctionDefinition(funcName, ps, t, typeCheckedBody, Some(binding,typeCheck(post,funcEnv))).stype(t) :: typeCheck(rest, env)
    case FunctionDefinition(funcName, ps, t, e, None) :: rest =>
      val typeCheckedBody = typeCheck(e, Environ(env.tpe ++ (ps.map(p => (p.name, p.typ))), env.arrSize))
      FunctionDefinition(funcName, ps, t, typeCheckedBody).stype(t) :: typeCheck(rest, env)
    case ClassDeclaration(className, paramList, parentName, declList) :: rest =>
      val newEnv = Environ((env.tpe + (className -> ClassType(className))) ++ (paramList.map(p => (p.name, p.typ))), env.arrSize)
      ClassDeclaration(className, paramList, parentName, typeCheck(declList,newEnv)) :: typeCheck(rest, newEnv)           
    case ReactBlock(cases) :: rest => typeCheck(cases,env) match {
      case cList: List[_] => ReactBlock(cList.asInstanceOf[List[CaseClause]]) :: typeCheck(rest, env)
      case _ => println("Error in type checking case clauses"); declList }
    case ActorLoop(declList) :: rest => ActorLoop(typeCheck(declList, env)) :: typeCheck(rest, env) 
    case CaseClause(Pattern(p), cond, expr) :: rest =>
      val newEnv = Environ(env.tpe + (p.name -> p.stype), env.arrSize)
      CaseClause(Pattern(p), typeCheck(cond,newEnv), typeCheck(expr,newEnv)) :: typeCheck(rest, env)
    case Predicate(pred: Expression, children: List[Predicate]) :: rest =>
      Predicate(typeCheck(pred,env), typeCheck(children,env).asInstanceOf[List[Predicate]]) :: typeCheck(rest, env)
    case (FunctionCall("sc_havoc", List(v@Variable(vname,_)))) :: rest if(v.stype != UnitType()) =>
      declList.head :: typeCheck(rest, Environ(env.tpe + (vname -> v.stype),env.arrSize))
    case (e: Expression) :: rest  =>
      typeCheck(e, env) :: typeCheck(rest, env)
    case _ :: rest =>
      declList.head :: typeCheck(rest, env)
  }

  def typeCheck(e: Expression, env: Environ): Expression = e match {
    case Block(declList) => Block(typeCheck(declList, env))
    case FunctionCall(funcName, exprList) =>
      FunctionCall(funcName, exprList.map(e => typeCheck(e,env)))
    case ArraySelect(array, index) => ArraySelect(typeCheck(array,env), typeCheck(index,env))   
    case ScArray(Some(aName), length) if (e.stype == UnitType()) => (env.tpe.get(aName.name),env.arrSize.get(aName.name)) match {
      case (Some(aType),aLength) => ScArray(Some(aName), aLength).stype(aType)
      case (_,_) => println("Type error: type of variable " + aName + " is unknown in the environment " + env.tpe); e
    }
    case ScArray(None, aLength) if (e.stype == UnitType()) =>
      println("Type error: type of array " + e + " is unknown in the environment " + env.tpe); e
    case ScArray(None, aLength) =>  ScArray(None, aLength).stype(e.stype)
    case ArrayUpdate(array, index, value) => ArrayUpdate(typeCheck(array,env), typeCheck(index,env), typeCheck(value,env)).stype(e.stype) 
    case IfThenElse(cond, conseq, altern) => IfThenElse(typeCheck(cond, env), typeCheck(conseq, env), typeCheck(altern, env))
    case WhileLoop(cond, body) => WhileLoop(typeCheck(cond, env), typeCheck(body, env))
    case DoWhileLoop(cond, body) => DoWhileLoop(typeCheck(cond, env), typeCheck(body, env))    
    case SendMessage(a@Variable(actorName,_), message) =>
      if(actorName != "sc_sender" && actorName != "sc_self") SendMessage(typeCheck(a,env).asInstanceOf[Variable], typeCheck(message,env))
        else SendMessage(a, typeCheck(message,env))
    case MemberAccess(e1, e2) => e // Don't bother with member access for the moment
    case Universal(v, qe) => Universal(v, typeCheck(qe, Environ(env.tpe + (v.name -> v.stype), env.arrSize))).stype(e.stype)
    case Existential(v, qe) => Existential(v, typeCheck(qe, Environ(env.tpe + (v.name -> v.stype), env.arrSize))).stype(e.stype)
    case CreateObject(cName, cArgs) => CreateObject(cName, cArgs.map(e => typeCheck(e,env))).stype(e.stype)
    case BinaryExpression(e1, op, e2) => 
      var te1 = typeCheck(e1, env)
      var te2 = typeCheck(e2, env)
      if((te1.stype == UnitType()) && (te2.stype != UnitType())) te1 = te1.stype(te2.stype)
      if((te1.stype != UnitType()) && (te2.stype == UnitType())) te2 = te2.stype(te1.stype)
      BinaryExpression(te1, op, te2).stype(te1.stype)
    case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, typeCheck(e1, env), typeCheck(e2, env), typeCheck(e3, env)).stype(e.stype)
    case Variable("sc_skip",None) => e.stype(UnitType())
    case Variable(name,d) if (e.stype == UnitType()) => Variable(name,d).stype(env.tpe.get(name) match {
      case Some(typ) => typ
      case None => println("Type error: type of variable " + name + " is unknown in the environment " + env.tpe); UnitType()
    })
    case UnaryExpression(op, e) => UnaryExpression(op, typeCheck(e, env))
    case NumericalConst(n) => e.stype(IntegerType())
    case _ =>
      e
  }
}