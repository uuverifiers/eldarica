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
import lazabs.cfg._
import lazabs.types._
import lazabs.prover.PrincessWrapper


/**
 * manipulates a formula 
 *
 */
object Manip {
  /**
   * short circuits a boolean formula
   */
  def shortCircuit(e: Expression): Expression = e match {
    case Not(Not(exp)) => shortCircuit(exp)
    case Not(exp) => Not(shortCircuit(exp))   
    case Conjunction(BoolConst(false),exp) => BoolConst(false) 
    case Conjunction(exp,BoolConst(false)) => BoolConst(false)
    case Conjunction(BoolConst(true),exp) => shortCircuit(exp) 
    case Conjunction(exp,BoolConst(true)) => shortCircuit(exp)
    case Disjunction(exp,BoolConst(true)) => BoolConst(true)    
    case Disjunction(BoolConst(true),exp) => BoolConst(true)
    case Disjunction(exp,BoolConst(false)) => shortCircuit(exp)
    case Disjunction(BoolConst(false),exp) => shortCircuit(exp)
    case Conjunction(exp1,exp2) =>
      val simp1 = shortCircuit(exp1)
      val simp2 = shortCircuit(exp2)
      if(simp1 == BoolConst(false) || simp2 == BoolConst(false)) BoolConst(false) else Conjunction(simp1,simp2)
    case Disjunction(exp1,exp2) => 
      val simp1 = shortCircuit(exp1)
      val simp2 = shortCircuit(exp2)
      if(simp1 == BoolConst(true) || simp2 == BoolConst(true)) BoolConst(true) else Disjunction(simp1,simp2)
    case Equality(exp1,exp2) => Equality(shortCircuit(exp1),shortCircuit(exp2))
    case Inequality(exp1,exp2) => Inequality(shortCircuit(exp1),shortCircuit(exp2))
    case _ => e
  }
  
  /**
   * find primed and unprimed variables in an expression
   */
  def getUnprimedPrimedVars(oe: Expression): (Set[Variable],Set[Variable]) = oe match {
    case v@Variable(name,None) =>
      if(name.endsWith("'")) (Set(),Set(v)) else (Set(v),Set()) 
    case TernaryExpression(op, e1, e2, e3) =>
      val (vs1,pvs1) = getUnprimedPrimedVars(e1)
      val (vs2,pvs2) = getUnprimedPrimedVars(e2)
      val (vs3,pvs3) = getUnprimedPrimedVars(e3)
      (vs1 ++ vs2 ++ vs3,pvs1 ++ pvs2 ++ pvs3)
    case BinaryExpression(e1, op, e2) => 
      val (vs1,pvs1) = getUnprimedPrimedVars(e1)
      val (vs2,pvs2) = getUnprimedPrimedVars(e2)
      (vs1 ++ vs2,pvs1 ++ pvs2)
    case UnaryExpression(op, e) => 
      getUnprimedPrimedVars(e)
    case Existential(bv, qe) =>
      getUnprimedPrimedVars(qe)
    case Universal(bv, qe) =>
      getUnprimedPrimedVars(qe)
    case _ => (Set(),Set())
  }
  
   /**
    * @param pred given predicate 
    * @param h the height of the formula in the path
    * @param t transition
    */
  def wp(t: Label, pred: Expression): Expression = t match {
    case Assume(p) => Disjunction(Not(p),pred)
    case Assign(l@Variable(_,_), rhs) => substitute(pred, Map(l -> rhs))
    case Assign(ArraySelect(array@ScArray(Some(aName), aLength),i), rhs) => substitute(pred, Map(aName -> ArrayUpdate(array, i, rhs)))
    case Assign(ArraySelect(ArraySelect(array@ScArray(Some(aName),aLength), i), j), rhs) => substitute(pred, Map(aName -> ArrayUpdate(array, i, ArrayUpdate(ArraySelect(array,i),j,rhs))))
    case Havoc(v) =>
      val newFreshVariable = freshVariable(v.stype)
      val newPred = substitute(pred,Map(v->newFreshVariable))
     Universal(BinderVariable(newFreshVariable.name).stype(v.stype),newPred)
    case Choice(l1, l2) => Conjunction(wp(l1,pred),wp(l2,pred))
    case Sequence(l1, l2) => wp(l1,wp(l2,pred))
    case Transfer(t) =>
      val (unprimedVars,primedVars) = getUnprimedPrimedVars(t)
      val replaceMap = ((unprimedVars union primedVars.map(x => Variable(x.name.dropRight(1)).stype(x.stype))).map{x => (x,freshVariable(x.stype))}.toMap)
      lazabs.prover.PrincessWrapper.elimQuantifiers(deBruijnIndex(replaceMap.values.foldLeft[Expression](Disjunction(Not(substitute(t,replaceMap.map(x => (Variable(x._1.name + "'").stype(x._1.stype),x._2)))),substitute(pred,replaceMap)))
          ((a,b) => Universal(BinderVariable(b.name).stype(b.stype),a))))
    case _ =>
      println("Label not handled in wp computation: " + lazabs.viewer.ScalaPrinter(t))
      pred
  }

  /**
   * @param pred given predicate
   * @param t transition
   */
  def sp(pred: Expression, t: Label): Expression = t match {
    case Assume(p) => Conjunction(p,pred)
    case Assign(l@Variable(n,_), rhs) =>
      val bv = freshVariable(l.stype)
      Existential(BinderVariable(bv.name).stype(l.stype), Conjunction(substitute(pred, Map(l -> Variable(bv.name,Some(1)).stype(l.stype))), 
          Equality(l, substitute(rhs, Map(l -> Variable(bv.name,Some(1)).stype(l.stype))))))
    //case Assign(ArraySelect(array@ScArray(Some(aName), aLength),i), rhs) => substitute(pred, aName, ArrayUpdate(array, i, rhs))
      //case Assign(ArraySelect(ArraySelect(array@ScArray(Some(aName),aLength), i), j), rhs) => substitute(pred, aName, ArrayUpdate(array, i, ArrayUpdate(ArraySelect(array,i),j,rhs)))
    case Transfer(t) =>
      val vars = freeVars(t).map(x => if(x.name.endsWith("'")) Variable(x.name.dropRight(1)).stype(x.stype) else x)
      val replaceMap = vars.map{x => (x,freshVariable(x.stype))}.toMap
      val prime2Unprime = vars.map{x => (Variable(x.name + "'").stype(x.stype),x)}.toMap
      deBruijnIndex(replaceMap.values.foldLeft[Expression](Conjunction(substitute(t,replaceMap ++ prime2Unprime),substitute(pred,replaceMap)))((a,b) => Existential(BinderVariable(b.name).stype(b.stype),a)))
    case _=> pred
  }
  
  /**
   * substitutes the variable 'v' with the formula 'replace'
     * @param original the given expression
     * @param replace mapping from a variable to the expression to be replaced
   */
  def substitute(original: Expression, replace: Map[Variable,Expression]): Expression = original match {
    case Block(declList) => declList match {
      case Nil => Block(Nil)
      case VarDeclaration(name, t, value) :: rest =>
        substitute(Block(rest), replace) match {
          case Block(ds) => Block(VarDeclaration(name, t, substitute(value, replace)) :: ds)
        }
      case PredsDeclaration(preds) :: rest =>
        substitute(Block(rest), replace) match {
          case Block(ds) => Block(PredsDeclaration(preds.asInstanceOf[List[Predicate]].map(substitute(_,replace))) :: ds)
        }
      case (e: Expression) :: rest  =>
        substitute(Block(rest), replace) match {
          case Block(ds) => Block( substitute(e, replace) :: ds)
        }
      case _ :: rest => println("Unexpected declaration in substitution: " + declList.head); Block(Nil) 
    }
    case IfThenElse(cond, conseq, altern) =>
      IfThenElse(substitute(cond, replace), substitute(conseq, replace), substitute(altern, replace)).stype(original.stype)
    case WhileLoop(cond, body) => WhileLoop(substitute(cond, replace), substitute(body, replace)).stype(original.stype)
    case ScArray(Some(aName), aLength) if (replace.contains(aName)) => replace.getOrElse(aName,original)
    case v@Variable(_,None) if (replace.contains(v)) => replace.getOrElse(v,original)
    case Variable(vName,Some(i)) if (replace.map(x => (x._1.name,x._2)).contains(vName)) => replace.map(x => (x._1.name,x._2)).get(vName) match {  // the variable is bound
      case Some(Variable(rName,rIndex)) => Variable(rName,Some(i)).stype(original.stype)   // keep the DeBruijn index, a bound variable can just be renamed
      case _ => original
    }
    case FunctionCall(funcName, exprList) if(replace.map(x => (x._1.name,x._2)).contains(funcName)) => replace.map(x => (x._1.name,x._2)).get(funcName) match {
      case Some(Variable(r,_)) => FunctionCall(r, exprList.map(substitute(_,replace))).stype(original.stype)
      case _ => original
    }
    case FunctionCall(funcName, exprList) => FunctionCall(funcName, exprList.map(substitute(_,replace))).stype(original.stype)
    case Existential(bv, qe) =>
      val newFreshVariable = freshVariable(bv.stype)
      val newQe = substitute(qe,Map(Variable(bv.name).stype(bv.stype)->newFreshVariable))
      Existential(BinderVariable(newFreshVariable.name).stype(bv.stype), substitute(newQe,replace)).stype(original.stype)
    case Universal(bv, qe) =>
      val newFreshVariable = freshVariable(bv.stype)
      val newQe = substitute(qe,Map(Variable(bv.name).stype(bv.stype)->newFreshVariable))
      Universal(BinderVariable(newFreshVariable.name).stype(bv.stype), substitute(newQe,replace)).stype(original.stype)   
    case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, substitute(e1,replace), substitute(e2,replace), substitute(e3,replace)).stype(original.stype)   
    case BinaryExpression(e1, op, e2) => BinaryExpression(substitute(e1,replace), op, substitute(e2,replace)).stype(original.stype)
    case UnaryExpression(op, e) => UnaryExpression(op, substitute(e,replace)).stype(original.stype)
    case _ =>
      original
  }
  
  def substitute(original: Predicate, replace: Map[Variable,Expression]): Predicate = original match {
    case Predicate(e, cs) => Predicate(substitute(e,replace), cs.map(substitute(_,replace)))
    case _ => original
  }

  def substitute(original: Label, replace: Map[Variable,Expression]): Label = original match {
    case Assume(p) => Assume(substitute(p,replace))
    case Assign(lhs, rhs) => Assign(substitute(lhs,replace), substitute(rhs,replace))
    case Havoc(vh) if (replace.contains(vh)) => Havoc(replace.getOrElse(vh,vh).asInstanceOf[Variable])
    case Sequence(l1, l2) => Sequence(substitute(l1,replace), substitute(l2,replace))
    case Choice(l1, l2) => Choice(substitute(l1,replace), substitute(l2,replace))
    case _ => original
  }
  
  def substitute(original: Map[CFGVertex,Set[CFGAdjacent]], replace: Map[Variable,Expression]): Map[CFGVertex,Set[CFGAdjacent]] = {
    original.mapValues {
      s => s.map(adj => CFGAdjacent(substitute(adj.label,replace),adj.to))
    }
  }
  /**
   * inputs a formula and puts version number for variables
   * returns the versioned formula and the variables that are changed in the formula
   * this method is used in SSA computation
   * @param e the given expression
   * @param timeStamp the current depth in the spurious path
   * @param determines if the SSA computation is forward or backward
   */
  def putVersion(e: Expression, timeStamp: Int, forward: Boolean) : Expression = e match {
    case Existential(v, qe) => 
      Existential(v, putVersion(qe,timeStamp,forward))
    case TernaryExpression(op, e1, e2, e3) =>
      val versioned1 = putVersion(e1,timeStamp,forward)
      val versioned2 = putVersion(e2,timeStamp,forward)
      val versioned3 = putVersion(e3,timeStamp,forward)
      TernaryExpression(op, versioned1, versioned2, versioned3).stype(e.stype)
    case BinaryExpression(e1, op, e2) =>
      val versioned1 = putVersion(e1,timeStamp,forward)
      val versioned2 = putVersion(e2,timeStamp,forward)
      BinaryExpression(versioned1, op, versioned2).stype(e.stype)
    case UnaryExpression(op, e) =>
      UnaryExpression(op, putVersion(e,timeStamp,forward)).stype(e.stype)
    case v@Variable(name,None) if (name.endsWith("'")) =>
      val varWithoutPrime = Variable(name.stripSuffix("'"),None).stype(e.stype)
      if(forward)
        Variable(("x" + (timeStamp + 1)) + name.stripSuffix("'"),None).stype(e.stype)
      else
        Variable(("x" + timeStamp) + name.stripSuffix("'"),None).stype(e.stype)
    case v@Variable(name,None) =>
      if(forward)
        Variable(("x" + timeStamp) + name,None).stype(e.stype)
      else
        Variable(("x" + (timeStamp + 1)) + name,None).stype(e.stype)
    case v@Variable(name,Some(_)) => v
    case NumericalConst(_) => e
    case BoolConst(_) => e
    case ScSet(None) => e
    case _ =>
      println("Expression not supported in interpolation " + e)
      e
  }
  
  /**
   * converts a list of formulas into static single assignment format 
   */
  def forwardSSA(fs: List[Expression]): List[Expression] = {
    fs.zip(0 until fs.length).map(fi => putVersion(fi._1,fi._2,true))
  }
  
  /**
   * converts a Scala condition to a Z3 condition
   */
  def convertScalaCond(e: Expression): Expression = e match {
    case MemberAccess(Range(lower,upper),FunctionCall("sc_forall",List(AnonymousFunction(i@Variable(_,_),e)))) =>
      deBruijnIndex(Universal(BinderVariable(i.name).stype(lazabs.types.IntegerType()),Disjunction(Disjunction(LessThan(i,lower),GreaterThanEqual(i,upper)), convertScalaCond(e))))
    case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, convertScalaCond(e1), convertScalaCond(e2), convertScalaCond(e3))
    case BinaryExpression(e1, op, e2) => BinaryExpression(convertScalaCond(e1), op, convertScalaCond(e2))
    case UnaryExpression(op, e) => UnaryExpression(op, convertScalaCond(e))
    case _ => e  
  }

  /**
   * gets the free variables of an expression
   */
  def freeVars(f: Expression): Set[Variable] = f match {
    case v@Variable(name,None) => Set[Variable](v)
    case Existential(BinderVariable(name), body) => freeVars(body)
    case Universal(BinderVariable(name), body) => freeVars(body)
    case BinaryExpression(e1, op, e2) => freeVars(e1) ++ freeVars(e2)
    case TernaryExpression(op, e1, e2, e3) => freeVars(e1) ++ freeVars(e2) ++ freeVars(e3)
    case _ => Set[Variable]()
  }
  
  /**
   * free the bound variables in an expression
   */
  def dischargeVariables(e: Expression): Expression = e match {
    case Variable(name,Some(_)) => Variable(name,None).stype(e.stype)
    case BinaryExpression(e1, op, e2) => BinaryExpression(dischargeVariables(e1), op, dischargeVariables(e2)).stype(e.stype)
    case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, dischargeVariables(e1), dischargeVariables(e2), dischargeVariables(e3))
    case _ => e
  }
  
  /**
   * performs skolemization and returns the used fresh symbols as well as the skolemized formula
   */
  
  def skolemize(se: Expression): (Expression,Set[Variable]) = {
    var cache = collection.mutable.Map[String,Variable]().empty
    def skolem(e: Expression): Expression = e match {
      case Variable(name,Some(i)) => cache.get(name) match {
        case Some(cvar) => cvar
        case None => 
          val f = freshVariable(e.stype)
          cache += (name -> f)
          Variable(f.name,None).stype(e.stype)
      }
      case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, skolem(e1), skolem(e2), skolem(e3)).stype(e.stype)
      case BinaryExpression(e1, op, e2) => BinaryExpression(skolem(e1), op, skolem(e2)).stype(e.stype)
      case UnaryExpression(op, e) => UnaryExpression(op, skolem(e)).stype(e.stype)
      case Existential(v, qe) => skolem(qe).stype(e.stype)
      case Universal(v, qe) =>
        println("Universal quantification is not supported yet in skolemization")
        sys.exit(0)
      case _ => e
    }
    val result = skolem(se)
    (result,Set() ++ cache.values)
  }
  
  /**
   * assigns correct debruijn indexes based on the names of the quantified variables 
   */
  def deBruijnIndex(e: Expression): Expression = {
    def deBruijn(e: Expression, bounds: List[String]): Expression = e match {
      case Variable(name,_) if (bounds.contains(name)) => Variable(name,Some(bounds.takeWhile(s => (s != name)).length)).stype(e.stype)
      case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, deBruijn(e1,bounds), deBruijn(e2,bounds), deBruijn(e3,bounds)).stype(e.stype)
      case BinaryExpression(e1, op, e2) => BinaryExpression(deBruijn(e1,bounds), op, deBruijn(e2,bounds)).stype(e.stype)
      case UnaryExpression(op, e) => UnaryExpression(op, deBruijn(e,bounds)).stype(e.stype)
      case Existential(v, qe) => Existential(v, deBruijn(qe,v.name :: bounds)).stype(e.stype)
      case Universal(v, qe) => Universal(v, deBruijn(qe,v.name :: bounds)).stype(e.stype)
      case _ => e
    }
    deBruijn(e,List())
  }
  
  /**
   * lifts the quantifiers in an expression
   */
  def liftQuantifiers(e: Expression): Expression = e match {
    case BinaryExpression(e1, op, Universal(bind, body)) if(!freeVars(e1).map(_.name).contains(bind.name)) =>
      liftQuantifiers(Universal(bind, liftQuantifiers(BinaryExpression(e1, op, body))))
    case BinaryExpression(Universal(bind, body), op, e2) if(!freeVars(e2).map(_.name).contains(bind.name)) =>
      liftQuantifiers(Universal(bind, liftQuantifiers(BinaryExpression(e2, op, body))))
    case BinaryExpression(e1, op, Existential(bind, body)) if(!freeVars(e1).map(_.name).contains(bind.name)) =>
      liftQuantifiers(Existential(bind, liftQuantifiers(BinaryExpression(e1, op, body))))
    case BinaryExpression(Existential(bind, body), op, e2) if(!freeVars(e2).map(_.name).contains(bind.name)) =>
      liftQuantifiers(Existential(bind, liftQuantifiers(BinaryExpression(e2, op, body))))
    case BinaryExpression(e1, op, e2) =>
      val le1 = liftQuantifiers(e1)
      val le2 = liftQuantifiers(e2)
      (le1,le2) match {
        case (Existential(_,_),_) => liftQuantifiers(BinaryExpression(le1, op, le2)).stype(e.stype)
        case (Universal(_,_),_) => liftQuantifiers(BinaryExpression(le1, op, le2)).stype(e.stype)
        case (_,Existential(_,_)) => liftQuantifiers(BinaryExpression(le1, op, le2)).stype(e.stype)
        case (_,Universal(_,_)) => liftQuantifiers(BinaryExpression(le1, op, le2)).stype(e.stype)
        case _ => BinaryExpression(le1, op, le2).stype(e.stype)
      }
    case _ => e
  }

  /**
   * converts all the variables in an expression to their primed version
   * @param e given expression
   */
  def prime(e: Expression): Expression = e match {
    case Variable(name,None) => Variable(name + "'",None).stype(e.stype)
    case bv@Variable(name,Some(_)) => bv
    case ArraySelect(array, index) => ArraySelect(prime(array), prime(index)).stype(e.stype)
    case ScArray(Some(aName), aLength) => ScArray(Some(prime(aName).asInstanceOf[Variable]), aLength).stype(e.stype)
    case ScArray(None, aLength) => ScArray(None, aLength).stype(e.stype)
    case UnaryExpression(op, e) => UnaryExpression(op, prime(e)).stype(e.stype)
    case BinaryExpression(e1, op, e2) => BinaryExpression(prime(e1), op, prime(e2)).stype(e.stype)
    case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, prime(e1), prime(e2), prime(e3)).stype(e.stype)
    case Existential(v, qe) => Existential(v, prime(qe)).stype(e.stype)
    case Universal(v, qe) => Universal(v, prime(qe)).stype(e.stype)
    case _ => e
  }
  
  /**
   * converts all the primed variables in an expression to their unprimed version
   * @param e given expression
   */
  def unprime(e: Expression): Expression = e match {
    case Variable(name,None) if (name.endsWith("'")) => Variable(name.dropRight(1),None).stype(e.stype)
    case bv@Variable(name,Some(_)) => bv
    case ArraySelect(array, index) => ArraySelect(unprime(array), unprime(index)).stype(e.stype)
    case ScArray(Some(aName), aLength) => ScArray(Some(unprime(aName).asInstanceOf[Variable]), aLength).stype(e.stype)
    case ScArray(None, aLength) => ScArray(None, aLength).stype(e.stype)
    case UnaryExpression(op, e) => UnaryExpression(op, unprime(e)).stype(e.stype)
    case BinaryExpression(e1, op, e2) => BinaryExpression(unprime(e1), op, unprime(e2)).stype(e.stype)
    case TernaryExpression(op, e1, e2, e3) => TernaryExpression(op, unprime(e1), unprime(e2), unprime(e3)).stype(e.stype)
    case Existential(v, qe) => Existential(v, unprime(qe)).stype(e.stype)
    case Universal(v, qe) => Universal(v, unprime(qe)).stype(e.stype)
    case _ => e
  }  
  
  private var curVarID = -1
  def freshVariable(t: Type): Variable = {
      curVarID = curVarID + 1
      Variable("v" + curVarID).stype(t)
  }
  
  /**
   * translates a label to a formula
   * @param l the given formula
   * @param vars the current set of variables
   * @return 1) translated expression,   2) list of variables,   3) generated list of fresh variables
   */
  def transFormula(l: Label, vars: Set[Variable]): (Expression,Set[Variable],Set[Variable]) = l match {
  case Assume(p) =>
    (vars.foldLeft(p)((a,b) => Conjunction(a, Equality(b,Variable(b.name + "'").stype(b.stype)))),vars,Set()) // the primed version of the variables is equal to the previous value
  case Assign(l@Variable(n,_), rhs) =>
    val newVars = if(!vars.contains(l)) vars + l else vars // add the variable to the list of variables if it is not already there
    (newVars.filter(_.name != n).foldLeft(Equality(prime(l), rhs))((a,b) => Conjunction(a, Equality(b,Variable(b.name + "'",None).stype(b.stype)))),newVars,Set())  // the primed version of lhs is equal to the rhs
  case Assign(ScArray(Some(an1),_),ScArray(Some(an2),_)) =>
    val newVars = if(!vars.contains(an1)) vars + an1 else vars // add the variable to the list of variables if it is not already there
    (newVars.filter(_ != an1).foldLeft(Equality(prime(an1), an2))((x,y) => Conjunction(x, Equality(y,Variable(y.name + "'",None).stype(y.stype)))),newVars,Set())  // the primed version of lhs is equal to the rhs       
  case Assign(ArraySelect(array@ScArray(Some(an),aLength),i), rhs) =>
    val newVars = if(!vars.contains(an)) vars + an else vars // add the variable to the list of variables if it is not already there
    (newVars.filter(_ != an).foldLeft(Equality(prime(an), ArrayUpdate(array, i, rhs)))((x,y) => Conjunction(x, Equality(y,Variable(y.name + "'",None).stype(y.stype)))),newVars,Set())  // the primed version of lhs is equal to the rhs
  case Assign(ArraySelect(ArraySelect(array@ScArray(Some(an),aLength), i), j), rhs) =>
    val newVars = if(!vars.contains(an)) vars  + an else vars // add the variable to the list of variables if it is not already there
    (newVars.filter(_ != an).foldLeft(Equality(prime(an),ArrayUpdate(array, i, ArrayUpdate(ArraySelect(array, i), j, rhs))))((x,y) => Conjunction(x, Equality(y,Variable(y.name + "'").stype(y.stype)))),newVars,Set())
  case Havoc(l@Variable(n,None)) =>
    val newVars = if(!vars.contains(l)) vars + l else vars // add the variable to the list of variables if it is not already there
    val fresh = freshVariable(l.stype)
    (newVars.filter(_.name != n).map(x => Equality(x,Variable(x.name + "'",None).stype(x.stype))).foldLeft(Equality(prime(l),fresh))((a,b) => Conjunction(a, b)),newVars,Set(fresh))  // the primed version of lhs is equal to the rhs
  case Choice(l1, l2) =>
    val (e1,n1,fresh1) = transFormula(l1,vars)
    val (e2,n2,fresh2) = transFormula(l2,vars)
    (Disjunction(e1,e2),n1 ++ n2, fresh1 ++ fresh2)
  case Sequence(l1, l2) =>
    val (conjunct1,nv1,fresh1) = transFormula(l1,vars)
    val (conjunct2,nv2,fresh2) = transFormula(l2,nv1 ++ vars)
    val newVars = nv1 ++ nv2 ++ vars
    val bvs = newVars.zip(newVars.map(v => freshVariable(v.stype)))
    val conjunct1Rename = bvs.foldLeft(conjunct1)((a,b) => substitute(a,Map(prime(b._1).asInstanceOf[Variable] -> b._2)))
    val conjunct2Rename = bvs.foldLeft(conjunct2)((a,b) => substitute(a,Map(b._1 -> b._2)))
    //println("The quantifier eliminated version is the following: " + lazabs.viewer.ScalaPrinter(Conjunction(conjunct1Rename,conjunct2Rename)))
    (Conjunction(conjunct1Rename,conjunct2Rename),newVars,(fresh1 ++ fresh2 ++ bvs.map(_._2)))
  case Transfer(t) =>
    (t,vars,Set())
  case _ =>
    println("Unsupported label in control flow graph " + l)
    (BoolConst(true),vars,Set())
  }
  
  /**
   *  translates a label to a formula and apply quantifier elimination to sequences composition
   */
  def transFormulaElim(l: Label, vars: Set[Variable]): (Expression,Set[Variable]) = l match {
  case Sequence(l1, l2) =>
    val (conjunct1,nv1) = transFormulaElim(l1,vars)
    val (conjunct2,nv2) = transFormulaElim(l2,nv1 ++ vars)
    val newVars = nv1 ++ nv2 ++ vars
    val bvs = newVars.zip(newVars.map(v => freshVariable(v.stype)))
    val conjunct1Rename = bvs.foldLeft(conjunct1)((a,b) => substitute(a,Map(prime(b._1).asInstanceOf[Variable] -> b._2)))
    val conjunct2Rename = bvs.foldLeft(conjunct2)((a,b) => substitute(a,Map(b._1 -> b._2)))
    val formula = PrincessWrapper.elimQuantifiers(deBruijnIndex((bvs.map(_._2)).foldLeft[Expression](Conjunction(conjunct1Rename,conjunct2Rename))((a,b) => Existential(BinderVariable(b.name).stype(b.stype),a))))
    (formula,newVars)
  case Choice(l1, l2) =>
    val (e1,n1) = transFormulaElim(l1,vars)
    val (e2,n2) = transFormulaElim(l2,vars)
    (Disjunction(e1,e2),n1 ++ n2)
  case _ =>
    val res = transFormula(l,vars)
    (res._1,res._2)
  }
}