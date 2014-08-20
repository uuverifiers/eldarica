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

package lazabs.cfg

import lazabs.ast.ASTree._
import lazabs.types._
import lazabs.utils.Manip._

object MakeCFG {
  /**
   * The name of the function which is considered for CFG generation
   */
  private var funcName = "main"
  /**
   * The list of atomic blocks.
   * First element is the start vertex
   * Second element is the adjacency list
   * Third element is the end vertex
   */
  private var singletonAtomicBlocks = List[(CFGVertex,Map[CFGVertex,Set[CFGAdjacent]],CFGVertex)]()
  private var classAtomicBlocks = Map[Int,Set[(CFGVertex,Map[CFGVertex,Set[CFGAdjacent]],CFGVertex)]]()
  /**
   * variables related to the queues of the actors
   */
  val actorQueues: List[(Variable,Expression)] = List((Variable("mailbox").stype(ArrayType(ArrayType(IntegerType()))),ScArray(None, None).stype(ArrayType(ArrayType(IntegerType())))),
      (Variable("senderbox").stype(ArrayType(ArrayType(IntegerType()))),ScArray(None, None).stype(ArrayType(ArrayType(IntegerType())))),
      (Variable("rear").stype(ArrayType(IntegerType())),ScArray(None, None).stype(ArrayType(IntegerType()))),
      (Variable("front").stype(ArrayType(IntegerType())),ScArray(None, None).stype(ArrayType(IntegerType()))))
  /**
   * The parent map; shows the parents of each vertex
   */
  def makeParentMap(m: Map[CFGVertex,Set[CFGAdjacent]]): Map[CFGVertex,Set[CFGAdjacent]] = {
    var result = Map[CFGVertex,Set[CFGAdjacent]]().empty
    m.toList.foreach(e => e._2.foreach(adj =>
      result += (adj.to -> (result.getOrElse(adj.to,Set()) ++ Set(CFGAdjacent(adj.label, e._1))))
    ))
    result
  }
  /**
   * Extracts the initial values of the variables
   */
  def initialValues(o: Sobject): List[(Variable,Expression)] = {
  var isSingletonActorDefined = false     // if any singleton actor is defined
  var isClassActorDefined = false         // if any class actor is defined
    def ival(o: Sobject): List[(Variable,Expression)] = o.defs match {
      case Nil => List()
        case VarDeclaration(name, t, n) :: ds =>
        (Variable(name).stype(t), n) :: ival(Sobject(o.preds, o.name, ds))
      case ClassDeclaration(className, paramList, Some("sc_Actor"), declList) :: ds =>
          isClassActorDefined = true
          var classFields: List[(Variable,Expression)] = (for (VarDeclaration(name, t, value) <- declList) yield (name,t)).map(x => (Variable(className + "_" + x._1.drop(3)).stype(ArrayType(x._2 match {
            case ClassType(_) => IntegerType()
            case _ => x._2
          })), ScArray(None, None).stype(ArrayType(IntegerType()))))
          classFields :::= paramList.map(param => (Variable(className + "_" + param.name.drop(3)).stype(ArrayType(param.typ match {
            case ClassType(_) => IntegerType()
            case _ => param.typ
          })), ScArray(None, None).stype(ArrayType(IntegerType())))) 
        classFields ::: ival(Sobject(o.preds, o.name, ds))
      case SingletonActorDeclaration(name, a) :: ds =>
        isSingletonActorDefined = true
        ival(Sobject(o.preds, o.name, ds))         
      case _ :: ds => ival(Sobject(o.preds, o.name, ds))
    }
    var init = ival(o)
    if( isSingletonActorDefined) init = actorQueues ::: init
    if( isClassActorDefined) init = 
      (Variable("lastActorId").stype(IntegerType()),NumericalConst(0)) ::
      (Variable("actorType").stype(ArrayType(IntegerType())),ScArray(None, None).stype(ArrayType(IntegerType()))) :: actorQueues ::: init
    init
  }
  
  /**
   * gets the body of the function for constructing its CFG
   * all the actor definitions in the body of the object are moved inside
   * note that we assume the program can be basically inlined
   */
  def getFuncExpression(defs: List[Declaration]): Expression = {
    var me: Expression = null
    var singletonActors = List[Declaration]()
    var classActors = List[Declaration]()
    def getFuncBody(defs: List[Declaration]): Expression = defs match {
      case Nil =>
        if (me == null) {
          println("Error: Could not find the method for CFG generation")
          sys.exit(0)
        }
        me match {
          case Block(es) => Block(singletonActors ::: classActors ::: es)
          case _ => Block(singletonActors ::: classActors ::: List(me))
        }
      case FunctionDefinition(fn, ps, t, e, _) :: ds if (funcName == fn) =>
        val havocs = if (funcName != "sc_main") ps.map(p => FunctionCall("sc_havoc", List(Variable(p.name).stype(p.typ)))) else List()
        me = e match {
          case Block(es) => Block(havocs ::: es)
          case _ => Block(havocs ::: List(e))
        }
        getFuncBody(ds)
      case FunctionDefinition(fn, ps, t, e, _) :: ds => getFuncBody(ds)
      case SingletonActorDeclaration(name, ads) :: ds => singletonActors = singletonActors :+ defs.head; getFuncBody(ds)
      case ClassDeclaration(className, paramList, Some("sc_Actor"), declList) :: ds =>
        classActors = classActors :+ defs.head 
        getFuncBody(ds)
      case VarDeclaration(name: String, t: Type, value: Expression) :: ds => 
        getFuncBody(ds)
      case _ :: ds => getFuncBody(ds)
    }
    getFuncBody(defs)
  }
  /**
   * Flatten a hierarchical predicate
   * @param p the predicate to be flatten
   * @param preds the predicates currently in the list
   */
  def flatPredicates(p: Predicate, preds: List[(Expression,List[Int])]): List[(Expression,List[Int])] = {
    var result = preds
    def traverse(pt: Predicate, parents: List[Int]): Unit = {
      result = result :+ (pt.pred,parents)
      val parent = result.size - 1
      pt.children.foreach(child => traverse(child,parents :+ parent))     
    }
    traverse(p, List())
    result     
  }   
  
  /**
   * the initial predicates of a given Scala object
   */
  def initialPredicates(o: Sobject): List[List[(Expression,List[Int])]] = {
    var result: List[List[(Expression,List[Int])]] = List(List((BoolConst(false),List())))   // We assume always the first predicate is false
    val initialPredicates = o.preds.asInstanceOf[List[Predicate]].filter(_.pred != BoolConst(false))
    initialPredicates.foreach(p => 
      result = (if(p.children.size != 0) List(flatPredicates(p, result.head)) else List(result.head ::: List((p.pred,List()))))
    )
    result
  }   
  
  /**
   * Gets a Scala object and generates the control flow graph for the main function 
   */
  def construct(o: Sobject): CFG = {
    val initPreds = initialPredicates(o)
    val to = CFGVertex(FreshCFGStateId.apply) // the end state
    var predMap: Map[CFGVertex,List[(Expression,List[Int])]] = Map(to -> (initPreds.reduceLeft(_:::_) ::: List((Variable("sc_LBE",None),List()))),
        CFGVertex(-1) -> List((BoolConst(false),List()),(Variable("sc_LBE",None),List())))
    val funcExpression = getFuncExpression(o.defs)
    val initialVars = Set(initialValues(o).map(_._1) : _*)
    var varsMap: Map[CFGVertex,Set[Variable]] = Map(to -> initialVars)
    var (start,trans,pm,vm) = makeCFG(funcExpression,to,initPreds,List(initialVars))
    predMap ++= pm
    varsMap ++= vm
    if(singletonAtomicBlocks.size > 0)
      singletonAtomicBlocks.foreach(a => {
        var (aStart,aTrans,aFinish) = a
        aTrans = (addMultiMap(aTrans,Map(to -> (aTrans.getOrElse(aStart, Set.empty)))) - aStart).mapValues(s => s.map(adj => adj match {
          case CFGAdjacent(adjLabel, adjTo) if (aFinish == adjTo) => CFGAdjacent(adjLabel, to)
          case _ => adj
        }))
        predMap = predMap - aStart - aFinish
        varsMap = varsMap - aStart - aFinish
        trans = addMultiMap(trans,aTrans)
      })     
    if(classAtomicBlocks.size > 0) {
      var newStartVertex = CFGVertex(FreshCFGStateId.apply)
      predMap += (newStartVertex -> initPreds.reduceLeft(_:::_))
      varsMap += (newStartVertex -> initialVars)
      val typeSelectVertex = CFGVertex(FreshCFGStateId.apply)
      predMap += (typeSelectVertex -> initPreds.reduceLeft(_:::_))
      varsMap += (typeSelectVertex -> (initialVars + Variable("i").stype(IntegerType())))
      val newLabel: Label = (List(
          Assign(Variable("lastActorId").stype(IntegerType()),NumericalConst(singletonActorName2ID.size - 1))) ++
          ((0 to singletonActorName2ID.size - 1).map(x =>
            Assign(ArraySelect(ScArray(Some(Variable("actorType").stype(ArrayType(IntegerType()))),None),NumericalConst(x)),
            NumericalConst(x))))).reduceLeft[Label](Sequence(_,_))
      trans = addMultiMap(trans,Map(newStartVertex -> Set(CFGAdjacent(newLabel,start)),to -> Set(CFGAdjacent(Havoc(Variable("i").stype(IntegerType())),typeSelectVertex))))
      start = newStartVertex
      classAtomicBlocks.toList.foreach(cab => {
        var (cId,cAtomicBlocks) = cab
        val actorStartVertex = CFGVertex(FreshCFGStateId.apply)
        predMap += (actorStartVertex -> initPreds.reduceLeft(_:::_))
        varsMap += (actorStartVertex -> (initialVars + Variable("i").stype(IntegerType())))
        trans = addMultiMap(trans,Map(typeSelectVertex -> Set(CFGAdjacent(Assume(Equality(ArraySelect(ScArray(Some(Variable("actorType").stype(ArrayType(IntegerType()))),None),Variable("i").stype(IntegerType())),
        NumericalConst(cId))),actorStartVertex))))
        cAtomicBlocks.foreach(a => {
          var (aStart,aTrans,aFinish) = a
          aTrans = (addMultiMap(aTrans,Map(actorStartVertex -> (aTrans.getOrElse(aStart, Set.empty)))) - aStart).mapValues(s => s.map(adj => adj match {
            case CFGAdjacent(adjLabel, adjTo) if (aFinish == adjTo) => CFGAdjacent(adjLabel, to)
            case _ => adj
            }))
          predMap = predMap - aStart - aFinish
          varsMap = varsMap - aStart - aFinish
          trans = addMultiMap(trans,aTrans)
        })
      })
    }
    CFG(start,trans,makeParentMap(trans),predMap,varsMap,Map.empty,Map.empty,Some(o))
  }
  def apply(o: Sobject, f: String, arrayRemoval: Boolean = false, accelerate: Boolean = false): CFG = {
    funcName = f
    val cfg = construct(o)
    CFGTransform(cfg,arrayRemoval,accelerate)
  }
  
  /**
   * adds a new atomic block to the current list of blocks
   */
  def addAtomicBlock(m:Map[Int,Set[(CFGVertex,Map[CFGVertex,Set[CFGAdjacent]],CFGVertex)]], i:Int, at: (CFGVertex,Map[CFGVertex,Set[CFGAdjacent]],CFGVertex)):Map[Int,Set[(CFGVertex,Map[CFGVertex,Set[CFGAdjacent]],CFGVertex)]] = {
    m + (i -> (m.getOrElse(i,Set[(CFGVertex,Map[CFGVertex,Set[CFGAdjacent]],CFGVertex)]().empty) + at))      
  }
  
  /**
   * adding two multi-maps and returning the result
   */
  def addMultiMap(l:Map[CFGVertex,Set[CFGAdjacent]], r:Map[CFGVertex,Set[CFGAdjacent]]):Map[CFGVertex,Set[CFGAdjacent]] = {
    var res = Map[CFGVertex,Set[CFGAdjacent]]().empty
    val keys = (l.keySet ++ r.keySet)
    keys.foreach( k => res += (k -> (l.getOrElse(k,Set[CFGAdjacent]().empty) ++ r.getOrElse(k,Set[CFGAdjacent]().empty))))
    res
  }
  
  /**
   * subtracting two multi-maps and returning the result
   */
  def subtractMultiMap(l:Map[CFGVertex,Set[CFGAdjacent]], r:Map[CFGVertex,Set[CFGAdjacent]]):Map[CFGVertex,Set[CFGAdjacent]] = {
    var res = Map[CFGVertex,Set[CFGAdjacent]]().empty
    val keys = l.keySet
    keys.foreach( k => res += (k -> (l.getOrElse(k,Set[CFGAdjacent]().empty) -- r.getOrElse(k,Set[CFGAdjacent]().empty))))
    res.filterNot(_._2.size == 0)
  }
  
  /**
   * list of the starting nodes of loops 
   */
  private var loops = List[CFGVertex]()
  def getLoops = loops
  
  /**
   * the current actor name
   */
  private var curActorName = "main"
    
  /**
   * each actor has a unique ID
   */
  private var curActorID = 0
  def freshActorID = {curActorID = curActorID + 1; curActorID}
    
  /**
   * a mapping from single actor name to its id
   */
  var singletonActorName2ID = Map[String,Int]("main" -> 0)
  /**
   * a mapping from class actor name to its type id
   */  
  var classActorName2TypeID =  Map[String,Int]()
  /**
   * a mapping from class actor name to its local variable declarations
   */  
  var classActorName2VarDecls =  Map[String,List[VarDeclaration]]()
  /**
   * a mapping from class actor name to its parameters
   */
  var classActorName2Params =  Map[String,List[Parameter]]()  
  
  /**
   * Making a control flow graph for a sequence of statements: s1 ; s2 ; ... ; sn
   * @param es list of statements
   * @param to last node
   * @param predicates predicates is a list of tuples (scope number, list of predicates). The scope 0 is always the global scope 
   * @return starting node of the graph and the set of CFGAdjacent nodes 
   */  
  def makeCFG(e: Expression, to: CFGVertex, predicates: List[List[(Expression,List[Int])]], variables: List[Set[Variable]])
            :(CFGVertex,Map[CFGVertex,Set[CFGAdjacent]],Map[CFGVertex,List[(Expression,List[Int])]],Map[CFGVertex,Set[Variable]]) = e match {
    case Block(es) =>
      makeCFG(es, to, predicates :+ List(), variables :+ Set())
    case _ => makeCFG(List(e), to, predicates, variables)
  }
  def makeCFG(es: List[ASTree], to: CFGVertex, predicates: List[List[(Expression,List[Int])]], variables: List[Set[Variable]])
           :(CFGVertex,Map[CFGVertex,Set[CFGAdjacent]],Map[CFGVertex,List[(Expression,List[Int])]],Map[CFGVertex,Set[Variable]]) = es match {
    case Nil => (to,Map[CFGVertex,Set[CFGAdjacent]]().empty,Map[CFGVertex,List[(Expression,List[Int])]]().empty,Map[CFGVertex,Set[Variable]]().empty)
    case e :: rest => e match {
      case IfThenElse(cond, conseq, altern) =>
        val currentVertex = CFGVertex(FreshCFGStateId.apply)
        val currentPredMap = Map(currentVertex -> predicates.reduceLeft(_:::_))
        val currentVarsMap = Map(currentVertex -> variables.foldLeft(Set[Variable]())(_++_))
        val (restVertex,restTrans, restPredMap, restVarsMap)   = makeCFG(rest, to, predicates, variables)
        val (leftVertex,leftTrans, leftPredMap, leftVarsMap)   = makeCFG(conseq, restVertex, predicates, variables)
        val (rightVertex,rightTrans, rightPredMap, rightVarsMap) = makeCFG(altern, restVertex, predicates, variables)
        val trans = addMultiMap(addMultiMap(restTrans, leftTrans), rightTrans) +
          (currentVertex -> Set(CFGAdjacent(Assume(shortCircuit(cond)),leftVertex),CFGAdjacent(Assume(shortCircuit(Not(cond))),rightVertex)))
        (currentVertex, trans, currentPredMap ++ restPredMap ++ leftPredMap ++ rightPredMap, currentVarsMap ++ restVarsMap ++ leftVarsMap ++ rightVarsMap)
      case IfThen(cond, conseq) =>
        val currentVertex = CFGVertex(FreshCFGStateId.apply)
        val currentPredMap = Map(currentVertex -> predicates.reduceLeft(_:::_))
        val currentVarsMap = Map(currentVertex -> variables.foldLeft(Set[Variable]())(_++_))
        val (restVertex,restTrans,restPredMap,restVarsMap)   = makeCFG(rest, to, predicates, variables)
        val (leftVertex,leftTrans,leftPredMap,leftVarsMap)   = makeCFG(conseq, restVertex, predicates, variables)
        val trans = addMultiMap(restTrans, leftTrans) + 
          (currentVertex -> Set(CFGAdjacent(Assume(shortCircuit(cond)),leftVertex),CFGAdjacent(Assume(shortCircuit(Not(cond))),restVertex)))
        (currentVertex, trans, currentPredMap ++ restPredMap ++ leftPredMap, currentVarsMap ++ restVarsMap ++ leftVarsMap)
      case WhileLoop(cond, body) => 
        val currentVertex = CFGVertex(FreshCFGStateId.apply)
        val currentPredMap = Map(currentVertex -> predicates.reduceLeft(_:::_))
        val currentVarsMap = Map(currentVertex -> variables.foldLeft(Set[Variable]())(_++_))
        loops = loops ::: List(currentVertex)
        val (restVertex,restTrans,restPredMap,restVarsMap)   = makeCFG(rest, to, predicates, variables)
        val (leftVertex,leftTrans,leftPredMap,leftVarsMap)   = makeCFG(body, currentVertex, predicates, variables)
        val trans = addMultiMap(restTrans, leftTrans) + 
          (currentVertex -> Set(CFGAdjacent(Assume(shortCircuit(cond)),leftVertex),CFGAdjacent(Assume(shortCircuit(Not(cond))),restVertex)))
        (currentVertex, trans, currentPredMap ++ restPredMap ++ leftPredMap, currentVarsMap ++ restVarsMap ++ leftVarsMap)
      case DoWhileLoop(cond, body) =>
        val currentVertex = CFGVertex(FreshCFGStateId.apply)
        val currentPredMap = Map(currentVertex -> predicates.reduceLeft(_:::_))
        val currentVarsMap = Map(currentVertex -> variables.foldLeft(Set[Variable]())(_++_))
        loops = loops ::: List(currentVertex)
        val (restVertex,restTrans,restPredMap,restVarsMap)   = makeCFG(rest, to, predicates, variables)
        val (leftVertex,leftTrans,leftPredMap,leftVarsMap)   = makeCFG(body, currentVertex, predicates, variables)
        val trans = addMultiMap(restTrans, leftTrans) + 
          (currentVertex -> Set(CFGAdjacent(Assume(shortCircuit(cond)),leftVertex),CFGAdjacent(Assume(shortCircuit(Not(cond))),restVertex)))
        (leftVertex, trans, currentPredMap ++ restPredMap ++ leftPredMap, currentVarsMap ++ restVarsMap ++ leftVarsMap)
      case VarDeclaration(name, ClassType(_), value) =>
        makeCFG(Assignment(Variable(name).stype(IntegerType()), value) :: rest, to, predicates, variables)
      case VarDeclaration(name, t, value) =>
        makeCFG(Assignment(Variable(name).stype(t), value) :: rest, to, predicates, variables)
      case PredsDeclaration(preds) =>
        makeCFG(rest, to, predicates.init :+ (predicates.last ::: preds.asInstanceOf[List[Predicate]].map(_.pred).filter(_ != BoolConst(false)).map(x => (x,List()))),variables)
      case Assignment(v@Variable(_,_), MemberAccess(Variable(_,_), Variable("sc_nextInt",_))) =>
        val currentVertex = CFGVertex(FreshCFGStateId.apply)
        val currentPredMap = Map(currentVertex -> predicates.reduceLeft(_:::_))
        val currentVarsMap = Map(currentVertex -> variables.foldLeft(Set[Variable]())(_++_))
        val (restVertex,restTrans,restPredMap,restVarsMap)   = makeCFG(rest, to, predicates, variables)
        val trans = restTrans +
          (currentVertex -> Set(CFGAdjacent(Havoc(v),restVertex)))
        (currentVertex, trans, currentPredMap ++ restPredMap, currentVarsMap ++ restVarsMap)
      case Assignment(lhs, rhs) =>
        val currentVertex = CFGVertex(FreshCFGStateId.apply)
        val currentPredMap = Map(currentVertex -> predicates.reduceLeft(_:::_))
        val currentVarsMap = Map(currentVertex -> variables.foldLeft(Set[Variable]())(_++_))
        val currentVariable: Variable = lhs match {
          case l@Variable(n,_) => l
          case ScArray(Some(an),_) => an
          case ArraySelect(array@ScArray(Some(an),aLength),i) => an
          case ArraySelect(ArraySelect(array@ScArray(Some(an),aLength), i), j) => an
          case _ =>
            throw new Exception("error in adding the variable: " + e)
        }
        val (restVertex,restTrans,restPredMap,restVarsMap)   = makeCFG(rest, to, predicates, variables.init :+ (variables.last + currentVariable))
        val trans = restTrans +
          (currentVertex -> Set(CFGAdjacent(Assign(lhs, rhs),restVertex)))
        (currentVertex, trans, currentPredMap ++ restPredMap, currentVarsMap ++ restVarsMap)
      case FunctionCall("sc_assert", exprList) => 
        val currentVertex = CFGVertex(FreshCFGStateId.apply)
        val errorVertex = CFGVertex(-1)
        val currentPredMap = Map(currentVertex -> predicates.reduceLeft(_:::_))
        val currentVarsMap = Map(currentVertex -> variables.foldLeft(Set[Variable]())(_++_))
        val (restVertex,restTrans,restPredMap,restVarsMap)   = makeCFG(rest, to, predicates, variables)
        val trans = restTrans +
          (currentVertex -> Set(CFGAdjacent(Assume(shortCircuit(exprList.head)),restVertex),CFGAdjacent(Assume(shortCircuit(Not(exprList.head))),errorVertex)))
        (currentVertex, trans,currentPredMap ++ restPredMap,currentVarsMap ++ restVarsMap)
      case FunctionCall("sc_assume", exprList) =>
        val currentVertex = CFGVertex(FreshCFGStateId.apply)
        val currentPredMap = Map(currentVertex -> predicates.reduceLeft(_:::_))
        val currentVarsMap = Map(currentVertex -> variables.foldLeft(Set[Variable]())(_++_))
        val (restVertex,restTrans,restPredMap,restVarsMap)   = makeCFG(rest, to, predicates, variables)
        val trans = restTrans + 
          (currentVertex -> Set(CFGAdjacent(Assume(shortCircuit(exprList.head)),restVertex)))
        (currentVertex, trans, currentPredMap ++ restPredMap,currentVarsMap ++ restVarsMap)
      case FunctionCall("sc_havoc", List(v@Variable(_,_))) =>
        val currentVertex = CFGVertex(FreshCFGStateId.apply)
        val currentPredMap = Map(currentVertex -> predicates.reduceLeft(_:::_))
        val currentVarsMap = Map(currentVertex -> variables.foldLeft(Set[Variable]())(_++_))
        val (restVertex,restTrans,restPredMap,restVarsMap)   = makeCFG(rest, to, predicates, variables.init :+ (variables.last + v))         
        val trans = restTrans +
          (currentVertex -> Set(CFGAdjacent(Havoc(v),restVertex)))
        (currentVertex, trans, currentPredMap ++ restPredMap,currentVarsMap ++ restVarsMap)
      case SingletonActorDeclaration(name, declList) =>
        curActorName = name
        singletonActorName2ID += (name -> freshActorID)
        val actorToVertex  = CFGVertex(FreshCFGStateId.apply)
        //val currentPredMap = Map(actorToVertex -> predicates.reduceLeft(_:::_))
        //val currentVarsMap = Map(actorToVertex -> variables.foldLeft(Set[Variable]())(_++_))
        val (_,_, actPredMap, actVarsMap) = makeCFG(declList, actorToVertex, predicates :+ List(),variables)   // bad programming style: the actor loops are accumulated in 'global' variable singletonAtomicBlocks
        curActorName = "main"
        val (restVertex,restTrans, restPredMap, restVarsMap)   = makeCFG(rest, to, predicates, variables)
        (restVertex,restTrans, restPredMap ++ actPredMap,restVarsMap ++ actVarsMap)
      case ClassDeclaration(className, paramList, Some("sc_Actor"), declList) =>
        curActorName = className
        classActorName2TypeID += (className -> freshActorID)
        classActorName2Params += (className -> paramList)
        val actorToVertex  = CFGVertex(FreshCFGStateId.apply)
        //val currentPredMap = Map(actorToVertex -> predicates.reduceLeft(_:::_))
        //val currentVarsMap = Map(actorToVertex -> variables.foldLeft(Set[Variable]())(_++_))
        val declListWithoutVarDecl = declList flatMap {
          case VarDeclaration(name, t, value) => None
          case d@_ => Some(d)
        }
        classActorName2VarDecls += (className -> (declList filterNot (declListWithoutVarDecl contains)).asInstanceOf[List[VarDeclaration]])
        val (_,_, actPredMap, actVarsMap) = makeCFG(declListWithoutVarDecl, actorToVertex, predicates :+ List(), variables.init :+ (variables.last + Variable("i").stype(IntegerType())))    // bad programming style: the actor loops are accumulated in 'global' variable classAtomicBlocks
        curActorName = "main"
        val (restVertex,restTrans, restPredMap, restVarsMap) = makeCFG(rest, to, predicates, variables)
        (restVertex,restTrans, restPredMap ++ actPredMap, restVarsMap ++ actVarsMap)
      case FunctionDefinition("sc_act",List(),UnitType(),declList,_) =>
        val (restVertex,restTrans,restPredMap,restVarsMap)   = makeCFG(rest, to, predicates,variables)
        val (declVertex,declTrans,declPredMap,declVarsMap)   = makeCFG(declList, restVertex, predicates, variables)
        (declVertex,(restTrans ++ declTrans),(restPredMap ++ declPredMap),(restVarsMap ++ declVarsMap))
      case ReactBlock(cases) =>
        var currentPredMap: Map[CFGVertex,List[(Expression,List[Int])]]  = Map.empty
        var currentVarsMap: Map[CFGVertex,Set[Variable]]  = Map.empty
        cases.foreach( c => c match {
          case CaseClause(Pattern(v@Variable(msg,_)), cond, e) =>
            val (restVertex,restTrans, restPredMap, restVarsMap)   = makeCFG(rest, to, predicates, variables)
            val atomicFinishVertex  = CFGVertex(FreshCFGStateId.apply)
            //currentPredMap ++= (restPredMap + (atomicFinishVertex -> predicates.reduceLeft(_:::_)))
            //currentVarsMap ++= (restVarsMap + (atomicFinishVertex -> variables.foldLeft(Set[Variable]())(_++_)))
            var (atomicStartVertex,atomicTrans,atomicPredMap,atomicVarsMap) = makeCFG(e, atomicFinishVertex, predicates, variables)
            currentPredMap ++= atomicPredMap
            currentVarsMap ++= atomicVarsMap
            val atomicFinishVertexWithPredicates = CFGVertex(FreshCFGStateId.apply)   // there may be predicates defined inside the block
            currentPredMap += (atomicFinishVertexWithPredicates -> atomicPredMap.getOrElse(atomicStartVertex,List()))
            currentVarsMap += (atomicFinishVertexWithPredicates -> atomicVarsMap.getOrElse(atomicStartVertex,Set()))
            atomicTrans = atomicTrans.mapValues(s => s.map(adj => adj match {
              case CFGAdjacent(adjLabel, adjTo) if (adjTo == atomicFinishVertex) => CFGAdjacent(adjLabel, atomicFinishVertexWithPredicates)
              case _ => adj
            }))
            val currentVertex1  = CFGVertex(FreshCFGStateId.apply)
            val currentVertex2  = CFGVertex(FreshCFGStateId.apply)
            val finishVertex  = CFGVertex(FreshCFGStateId.apply)
            currentPredMap ++= Map(currentVertex1 -> predicates.reduceLeft(_:::_),currentVertex2 -> predicates.reduceLeft(_:::_),finishVertex -> predicates.reduceLeft(_:::_))
            currentVarsMap ++= Map(currentVertex1 -> variables.foldLeft(Set[Variable]())(_++_),currentVertex2 -> variables.foldLeft(Set[Variable]())(_++_),finishVertex -> variables.foldLeft(Set[Variable]())(_++_))
            val id = (if(singletonActorName2ID.contains(curActorName)) NumericalConst(curActorID) else Variable("i").stype(IntegerType()))
            atomicTrans = atomicTrans + 
              (currentVertex1 -> Set(CFGAdjacent(Assume(Inequality(ArraySelect(ScArray(Some(Variable("front").stype(ArrayType(IntegerType()))),None),id),
                ArraySelect(ScArray(Some(Variable("rear").stype(ArrayType(IntegerType()))),None),id))),currentVertex2))) +
                (atomicFinishVertexWithPredicates -> Set(CFGAdjacent(Assign(ArraySelect(ScArray(Some(Variable("front").stype(ArrayType(IntegerType()))),None),id), 
                Addition(ArraySelect(ScArray(Some(Variable("front").stype(ArrayType(IntegerType()))),None),id), NumericalConst(1))), finishVertex)))
            if(cond == BoolConst(true))
              atomicTrans = atomicTrans +
                (currentVertex2 -> Set(CFGAdjacent(Assign(v,ArraySelect(ArraySelect(ScArray(Some(Variable("mailbox").stype(ArrayType(ArrayType(IntegerType())))), None),id),
                ArraySelect(ScArray(Some(Variable("front").stype(ArrayType(IntegerType()))), None),id))), atomicStartVertex)))
            else {
              val currentVertex3  = CFGVertex(FreshCFGStateId.apply)
              currentPredMap += (currentVertex3 -> atomicPredMap.getOrElse(atomicStartVertex,List()))
              currentVarsMap += (currentVertex3 -> atomicVarsMap.getOrElse(atomicStartVertex,Set()))
              atomicTrans = atomicTrans +
                (currentVertex2 -> Set(CFGAdjacent(Assign(v,ArraySelect(ArraySelect(ScArray(Some(Variable("mailbox").stype(ArrayType(ArrayType(IntegerType())))), None),id),
              ArraySelect(ScArray(Some(Variable("front").stype(ArrayType(IntegerType()))), None),id))), currentVertex3))) +
                (currentVertex3 -> Set(CFGAdjacent(Assume(cond), atomicStartVertex)))
            }
            if(singletonActorName2ID.contains(curActorName)) singletonAtomicBlocks ::= (currentVertex1,atomicTrans,finishVertex)
              else {
                var transitions = atomicTrans
                classActorName2Params.getOrElse(curActorName, List()).foreach(param => transitions = substitute(transitions, Map(Variable(param.name).stype(param.typ) -> 
                  ArraySelect(ScArray(Some(Variable(curActorName + "_" + param.name.drop(3)).stype(ArrayType(param.typ))),None),Variable("i").stype(IntegerType())))))
                classActorName2VarDecls.getOrElse(curActorName, List()).foreach(vardecl => {
                  transitions = substitute(transitions, Map(Variable(vardecl.name).stype(vardecl.t) ->
                    ArraySelect(ScArray(Some(Variable(curActorName + "_" + vardecl.name.drop(3)).stype(ArrayType(vardecl.t))),None),Variable("i").stype(IntegerType()))))})                  
                  classAtomicBlocks = addAtomicBlock(classAtomicBlocks, curActorID, (currentVertex1,transitions,finishVertex))          
              }
          case _ => 
            println("Only simple case clauses are supported")
        })
        (to,Map[CFGVertex,Set[CFGAdjacent]]().empty,currentPredMap,currentVarsMap)
      case ActorLoop(declList) => makeCFG(declList, to, predicates, variables)
      case MemberAccess(e, Variable("sc_start",_)) => // Don't bother with start for the moment
        makeCFG(rest, to, predicates, variables)
      case _ => println("Expression not handled in CFG generation " + e)
        makeCFG(rest, to, predicates, variables)
    }
  }
}