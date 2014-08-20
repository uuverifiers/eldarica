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

import lazabs.ast.ASTree._
import lazabs.types._

object Inline {
    /**
   * removes unnecessary multi-level blocking of the instructions
   * e.g., Block(X = 5, Block(X = 7, X = 8)) is converted to Block(X = 5, X = 7, X = 8) 
   */
  def unblock(e: Expression): Expression = e match {
    case Block(declList) => Block(unblockl(declList)).stype(e.stype)
    case IfThenElse(cond, conseq, altern) => IfThenElse(cond, unblock(conseq), unblock(altern)).stype(e.stype)
    case WhileLoop(cond, body) => WhileLoop(cond, unblock(body)).stype(e.stype)
    case DoWhileLoop(cond, body) => DoWhileLoop(cond, unblock(body)).stype(e.stype)
    case IfThen(cond, conseq) => IfThen(cond, unblock(conseq)).stype(e.stype)
    case _ => e
  }
  def unblockl(decls: List[ASTree]): List[ASTree] = decls match {
    case Nil => Nil
    case Block(declList) :: rest => declList ::: rest
    case IfThenElse(cond, conseq, altern) :: rest => (IfThenElse(cond, unblock(conseq), unblock(altern)).stype(decls.head.stype) :: unblockl(rest))
    case WhileLoop(cond, body) :: rest => WhileLoop(cond, unblock(body)).stype(decls.head.stype) :: unblockl(rest)
    case DoWhileLoop(cond, body) :: rest => DoWhileLoop(cond, unblock(body)).stype(decls.head.stype) :: unblockl(rest)
    case IfThen(cond, conseq) :: rest => IfThen(cond, conseq).stype(decls.head.stype) :: unblockl(rest)
    case SingletonActorDeclaration(name, ads) :: rest =>
      SingletonActorDeclaration(name, unblockl(ads)).stype(decls.head.stype) :: unblockl(rest)
    case ClassDeclaration(className, paramList, p@_, declList) :: rest =>
      ClassDeclaration(className, paramList, p, unblockl(declList)).stype(decls.head.stype) :: unblockl(rest)
    case CaseClause(pattern, cond, e) :: rest =>
      CaseClause(pattern, cond, unblock(e)).stype(decls.head.stype) :: unblockl(rest)
    case ActorLoop(declList) :: rest =>
      ActorLoop(declList) :: unblockl(rest)
    case ReactBlock(cases) :: rest => ReactBlock(unblockl(cases).asInstanceOf[List[CaseClause]]).stype(decls.head.stype) :: rest 
    case _ :: rest => 
      decls.head :: unblockl(rest)
  }
  /**
   * map from function name to its definition
   */
  var funcs: Map[String,FunctionDefinition] = Map()
  /**
   * map from the actor instance to its class name
   */
  var actorInstance2ClassName = Map[String,String]()
  /**
   * The fields of the classes are taken as arrays
   */
  var classFields: List[Variable] = List()    
  /**
   * Determines if the variables related to the internal queues of the actors are added to the program
   */
  var isActorQueues = false
  /**
   * the assumptions that relates to the postconditions of function calls
   */
  private var assumptions: List[Expression] = List()  
  /**
   * inlines the function calls
   */
  def inline(o: Sobject): Sobject = {
    val predsVarDec = (o.preds filter {
      case VarDeclaration(_,_,_) => true
      case _ => false
    }).asInstanceOf[List[Declaration]]  // specification variables defined in the predicates section
    funcs = Map[String,FunctionDefinition]() ++ (for (f@FunctionDefinition(funcName, ps, t, e, post) <- (predsVarDec ++ o.defs)) yield (funcName -> f))
    val globalArrays = for (VarDeclaration(name, lazabs.types.ArrayType(t), value) <- (predsVarDec ++ o.defs)) yield Variable(name).stype(lazabs.types.ArrayType(t))
    val inlinedBody = inline(predsVarDec ++ o.defs, globalArrays).asInstanceOf[List[Declaration]]
    Sobject(o.preds.diff(predsVarDec).asInstanceOf[List[Predicate]].map(inline(_, globalArrays)), o.name, inlinedBody)
  }
  def inline(defs: List[ASTree], arrays: List[Variable]): List[ASTree] = defs match {
    case Nil => Nil
    case FunctionDefinition(funcName, ps, t, e, _) :: ds => 
      val localArrays: List[Variable] = ps.filter(_.typ match {
        case ArrayType(_)  => true
        case _ => false
      }).map(p => Variable(p.name).stype(p.typ))
      FunctionDefinition(funcName, ps, t, unblock(inline(e, localArrays ::: arrays))) :: inline(ds, arrays)
    case VarDeclaration(name, t@lazabs.types.ArrayType(at), value) :: ds =>
        var localArray = (Variable(name).stype(lazabs.types.ArrayType(at)))
        var inlinedDeclaration: List[ASTree] = List(VarDeclaration(name, t, inline(value, localArray :: arrays)))
        val havocedVars: List[Variable] = for (FunctionCall("sc_havoc", List(v@Variable(_,_))) <- assumptions) yield (v)
        if(!assumptions.isEmpty) {
          inlinedDeclaration :::= assumptions
          assumptions = List()
        }       
        inlinedDeclaration ::: inline(ds, localArray :: havocedVars ::: arrays)
    case VarDeclaration(name, t, value) :: ds =>
        var inlinedDeclaration: List[ASTree] = List(VarDeclaration(name, t, inline(value, arrays)))
        val havocedVars: List[Variable] = for (FunctionCall("sc_havoc", List(v@Variable(_,_))) <- assumptions) yield (v)
        if(!assumptions.isEmpty) {
          inlinedDeclaration :::= assumptions
          assumptions = List()
        }
      inlinedDeclaration ::: inline(ds, havocedVars ::: arrays)
    case PredsDeclaration(preds) :: ds =>
      val predsVarDec = (preds filter {               // specification variables defined in the predicates section
        case VarDeclaration(_,_,_) => true
        case Predicate(Assignment(_,_),_) => true
        case Predicate(FunctionCall("sc_assume",_),_) => true    // also inline assumes
        case _ => false
      })
      val rest = inline(predsVarDec.map{
        case Predicate(pred,_) => pred
        case p@_ => p} ::: ds, arrays)
      PredsDeclaration(preds.diff(predsVarDec).asInstanceOf[List[Predicate]].map(inline(_,arrays))) :: rest 
    case SingletonActorDeclaration(name, ads) :: ds =>
        SingletonActorDeclaration(name, inline(ads, arrays)) :: inline(ds, arrays)
    case ClassDeclaration(className, paramList, Some("sc_Actor"), ads) :: ds =>
        classFields :::= (paramList.map(param => (param.name,param.typ)) ::: (for (VarDeclaration(name, t, value) <- ads) yield (name,t))).map(x => (Variable(className + "_" + x._1.drop(3)).stype(ArrayType(x._2 match {
            case ClassType(_) => IntegerType()            
            case _ => x._2
          }))))     
        ClassDeclaration(className, paramList, Some("sc_Actor"), inline(ads, arrays)) :: inline(ds, arrays)
    case ReactBlock(cases) :: ds =>
        ReactBlock(inline(cases, arrays).asInstanceOf[List[CaseClause]]) :: inline(ds, arrays)
    case CaseClause(pattern, cond, e) :: ds =>
      CaseClause(pattern, cond, unblock(inline(e,arrays))) :: inline(ds, arrays)
    case ActorLoop(declList) :: ds => ActorLoop(unblockl(inline(declList, arrays))) :: inline(ds, arrays)
    case (e: Expression) :: ds =>
        var inlinedExpression: List[ASTree]  = List(inline(e, arrays))
        val havocedVars: List[Variable] = for (FunctionCall("sc_havoc", List(v@Variable(_,_))) <- assumptions) yield (v)
        if(!assumptions.isEmpty) {
          inlinedExpression :::= assumptions
          assumptions = List()
        }
      inlinedExpression ::: inline(ds, havocedVars ::: arrays)
    case _ :: ds =>
      defs.head :: inline(ds, arrays)
  }
  def inline(pr: Predicate, arrays: List[Variable]): Predicate = pr match {
    case Predicate(e, cs) => Predicate(inline(e,arrays), cs.map(inline(_,arrays)))
    case _ => pr
  }
  /**
   * a fresh name that is used for an inlined function
   */
  private var curNumber = -1
  def freshName: String = {curNumber = curNumber + 1; "f" + curNumber}
  import lazabs.utils.Manip._
  
  def inline(ex: Expression, arrays: List[Variable]): Expression = ex match {
    case Block(declList) => unblock(Block(inline(declList, arrays))).stype(ex.stype)
    case IfThenElse(cond, conseq, altern) =>
      IfThenElse(inline(cond, arrays), inline(conseq, arrays), inline(altern, arrays)).stype(ex.stype)
    case WhileLoop(cond, body) => WhileLoop(inline(cond,arrays), inline(body, arrays)).stype(ex.stype)
    case DoWhileLoop(cond, body) => DoWhileLoop(inline(cond,arrays), inline(body, arrays)).stype(ex.stype)
    case FunctionCall(funcName, exprList) if( funcName == "sc_assert" || funcName == "sc_assume" || funcName == "sc_havoc") =>
      FunctionCall(funcName, exprList.map(inline(_,arrays))).stype(ex.stype)
    case FunctionCall(funcName, List(expr)) if( arrays.map(_.name).exists(_ == funcName)) =>  // function is an array
      arrays.find(_.name == funcName) match {
        case Some(v) => ArraySelect(ScArray(Some(v), Some(NumericalConst(0))), inline(expr,arrays))
        case None => ex}
    case FunctionCall(funcName, List(expr)) if( (funcName.startsWith("actorType") || funcName.startsWith("rear") || funcName.startsWith("front")))  => // dealing arrays related to actors
      ArraySelect(ScArray(Some(Variable(funcName).stype(lazabs.types.ArrayType(lazabs.types.IntegerType()))), None), inline(expr,arrays))
    case FunctionCall(funcName, List(expr)) if( classFields.map(_.name).exists(_ == funcName)) => // dealing arrays related to fields of actors
      classFields.find(_.name == funcName) match {
        case Some(v) => ArraySelect(ScArray(Some(v), None), inline(expr,arrays))
        case None => ex}
    case FunctionCall(funcName, exprList) => funcs.get(funcName) match {
      case Some(f) =>
        val params = f.params.zip(exprList.map(inline(_,arrays)))
        f.post match {
          case Some((binding,post)) =>
            val fresh = Variable(freshName).stype(f.t)
            val assume: Expression = fresh.stype match {
              case ArrayType(_) => inline(FunctionCall("sc_assume", List(substitute(post, Map(binding -> fresh)))),fresh :: arrays)
              case _ => inline(FunctionCall("sc_assume", List(substitute(post, Map(binding -> fresh)))),arrays)
            }
            assumptions :::= List(FunctionCall("sc_havoc", List(fresh)),
                params.foldLeft(assume)((x,y) => substitute(assume, Map(Variable(y._1.name) -> y._2))))
            fresh
          case None =>
            params.foldLeft(f.body)((x,y) => substitute(x, Map(Variable(y._1.name).stype(y._1.stype) -> y._2)))
        }
      case None =>
        println("Function definition \"" + funcName + "\" is missing in this file")
        ex
    }
    case MemberAccess(e1,FunctionCall("sc_contains",List(elem))) =>  // set membership
      SetContains(inline(e1,arrays),inline(elem,arrays)).stype(BooleanType())
    case MemberAccess(e1,FunctionCall("sc_intersect",List(elem))) =>  // set intersect      
      SetIntersect(inline(e1,arrays),inline(elem,arrays)).stype(SetType(IntegerType()))
    case MemberAccess(e1,FunctionCall("sc_subsetOf",List(elem))) =>  // set intersect      
      SetSubset(inline(e1,arrays),inline(elem,arrays)).stype(SetType(IntegerType()))
    case MemberAccess(e1,Variable("sc_isEmpty",_)) =>  // set emptiness checking
      Equality(inline(e1,arrays),ScSet(None).stype(SetType(IntegerType()))).stype(BooleanType())
    case MemberAccess(e1,Variable("sc_head",_)) =>  // extracting the head of the list
      val fresh = Variable(freshName).stype(IntegerType())
      assumptions :::= List(FunctionCall("sc_havoc", List(fresh)),FunctionCall("sc_assume", List(SetContains(inline(e1,arrays),fresh))))
      fresh
    case MemberAccess(e1,Variable("sc_tail",_)) =>  // extracting the tail of the list
      val fresh_x = Variable(freshName).stype(IntegerType())
      val fresh_Y = Variable(freshName).stype(SetType(IntegerType()))
      assumptions :::= List(FunctionCall("sc_havoc", List(fresh_x)),
        FunctionCall("sc_havoc", List(fresh_Y)),
        FunctionCall("sc_assume", List(Conjunction(SetContains(inline(e1,arrays),fresh_x),Equality(fresh_Y,SetDelete(inline(e1,arrays),fresh_x)))))
      )
      fresh_Y
    case MemberAccess(Range(lower,upper),FunctionCall("sc_forall",List(AnonymousFunction(i@Variable(_,_),e)))) =>
      deBruijnIndex(Universal(BinderVariable(i.name).stype(lazabs.types.IntegerType()),Disjunction(Disjunction(LessThan(i,lower),GreaterThanEqual(i,upper)), inline(e, arrays))))
    case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, inline(e1, arrays), inline(e2, arrays), inline(e3, arrays)).stype(ex.stype)
    case BinaryExpression(e1, op, e2) => BinaryExpression(inline(e1, arrays), op, inline(e2, arrays)).stype(ex.stype)
    case UnaryExpression(op, e) => UnaryExpression(op, inline(e, arrays)).stype(ex.stype)
    case Existential(v, qe) => Manip.deBruijnIndex(Existential(v, inline(qe, arrays)))
    case Universal(v, qe) => Manip.deBruijnIndex(Universal(v, inline(qe, arrays)))
    case Variable("sc_skip",None) => FunctionCall("sc_assume", List(BoolConst(true)))
    case _ =>
      ex
  }
}
