/**
 * Copyright (c) 2011-2016 Hossein Hojjat and Philipp Ruemmer.
 * All rights reserved.
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

package lazabs.horn.bottomup

import ap.parser._
import IExpression._
import ap.SimpleAPI
import ap.SimpleAPI.ProverStatus

import lazabs.horn.preprocessor.{DefaultPreprocessor, HornPreprocessor}
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.global._
import lazabs.utils.Manip._
import lazabs.prover.PrincessWrapper._
import lazabs.prover.Tree
import Util._
import HornPredAbs.{RelationSymbol}
import lazabs.horn.abstractions.{AbsLattice, AbsReader, LoopDetector,
                                 StaticAbstractionBuilder}

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashMap}


object HornWrapper {

  object NullStream extends java.io.OutputStream {
    def write(b : Int) = {}
  }

}

////////////////////////////////////////////////////////////////////////////////

class HornWrapper(constraints: Seq[HornClause], 
                  uppaalAbsMap: Option[Map[String, AbsLattice]],
                  lbe: Boolean,
                  log : Boolean,
                  disjunctive : Boolean) {

  import HornWrapper._
  import HornPreprocessor.{VerifHintElement, VerificationHints,
                           EmptyVerificationHints}

  def printClauses(cs : Seq[Clause]) = {
    for (c <- cs) {
      println(c);
    }
  }

  private val translator = new HornTranslator
  import translator._
  
  //////////////////////////////////////////////////////////////////////////////

  ap.util.Debug enableAllAssertions lazabs.Main.assertions

  private val outStream = if (log) Console.err else NullStream

  private val originalClauses = constraints
  private val unsimplifiedClauses = originalClauses map (transform(_))

//    if (lazabs.GlobalParameters.get.printHornSimplified)
//      printMonolithic(unsimplifiedClauses)

  private val name2Pred =
    (for (Clause(head, body, _) <- unsimplifiedClauses.iterator;
          IAtom(p, _) <- (head :: body).iterator)
     yield (p.name -> p)).toMap

  //////////////////////////////////////////////////////////////////////////////

  private val hints : VerificationHints =
    lazabs.GlobalParameters.get.cegarHintsFile match {
      case "" =>
        EmptyVerificationHints
      case hintsFile => {
        val reader = new AbsReader (
                       new java.io.BufferedReader (
                         new java.io.FileReader(hintsFile)))
        val hints =
          (for ((predName, hints) <- reader.allHints.iterator;
                pred = name2Pred get predName;
                if {
                  if (!pred.isDefined)
                    Console.err.println("   Ignoring hints for " + predName + "\n")
                  pred.isDefined
                }) yield {
             (pred.get, hints)
           }).toMap
        VerificationHints(hints)
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  private val (simplifiedClauses, simpHints, preprocBackTranslator) =
    Console.withErr(outStream) {
    var (simplifiedClauses, simpHints, backTranslator) =
      if (lbe) {
        (unsimplifiedClauses, hints, HornPreprocessor.IDENTITY_TRANSLATOR)
      } else {
        val preprocessor = new DefaultPreprocessor
        preprocessor.process(unsimplifiedClauses, hints)
      }

    if (lazabs.GlobalParameters.get.printHornSimplified) {
//      println("-------------------------------")
//      printClauses(simplifiedClauses)
//      println("-------------------------------")

      println("Clauses after preprocessing:")
      for (c <- simplifiedClauses)
        println(c.toSMTString)

      //val aux = simplifiedClauses map (horn2Eldarica(_))
//      val aux = horn2Eldarica(simplifiedClauses)
//      println(lazabs.viewer.HornPrinter(aux))
//      simplifiedClauses = aux map (transform(_))
//      println("-------------------------------")
//      printClauses(simplifiedClauses)
//      println("-------------------------------")
    }

    (simplifiedClauses, simpHints, backTranslator)
  }

  //////////////////////////////////////////////////////////////////////////////

  private lazy val loopDetector = new LoopDetector(simplifiedClauses)

  /** Manually provided interpolation abstraction hints */
  private lazy val hintsAbstraction : TemplateInterpolator.AbstractionMap =
    if (simpHints.isEmpty)
      Map()
    else
      loopDetector hints2AbstractionRecord simpHints

  /** Automatically computed interpolation abstraction hints */
  private val abstractionType =
    lazabs.GlobalParameters.get.templateBasedInterpolationType

  private lazy val autoAbstraction : TemplateInterpolator.AbstractionMap =
    if (abstractionType == StaticAbstractionBuilder.AbstractionType.Empty) {
      Map()
    } else {
      val builder = new StaticAbstractionBuilder(simplifiedClauses, abstractionType)
      builder.abstractions mapValues (TemplateInterpolator.AbstractionRecord(_))
    }

  //////////////////////////////////////////////////////////////////////////////

  private val predGenerator = Console.withErr(outStream) {
    if (lazabs.GlobalParameters.get.templateBasedInterpolation) {
      val fullAbstractionMap =
        TemplateInterpolator.AbstractionRecord
          .mergeMaps(hintsAbstraction, autoAbstraction)

      if (fullAbstractionMap.isEmpty)
        DagInterpolator.interpolatingPredicateGenCEXAndOr _
      else
        TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
          fullAbstractionMap,
          lazabs.GlobalParameters.get.templateBasedInterpolationTimeout)
    } else {
      DagInterpolator.interpolatingPredicateGenCEXAndOr _
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  val result : Either[Map[Predicate, IFormula], Dag[IAtom]] = {
    val counterexampleMethod =
      if (disjunctive)
        HornPredAbs.CounterexampleMethod.AllShortest
      else
        HornPredAbs.CounterexampleMethod.FirstBestShortest

    val result = Console.withOut(outStream) {
      println
      println(
        "-------------------- Starting solver -----------------------")

       (new HornPredAbs(simplifiedClauses,
                        simpHints.toInitialPredicates, predGenerator,
                        counterexampleMethod)).result
    }

    result match {
      case Left(res) =>
        if (lazabs.GlobalParameters.get.needFullSolution) {
          val fullSol = preprocBackTranslator translate res

          // verify correctness of the solution
          if (lazabs.Main.assertions) assert(SimpleAPI.withProver { p =>
            import p._
            unsimplifiedClauses forall { case clause@Clause(head, body, constraint) => scope {
                addConstants(clause.constants.toSeq.sortWith(_.name < _.name))
                !! (constraint)
                for (IAtom(pred, args) <- body)
                  !! (subst(fullSol(pred), args.toList, 0))
                ?? (if (head.pred == HornClauses.FALSE)
                      i(false)
                    else
                      subst(fullSol(head.pred), head.args.toList, 0))
                ??? == ProverStatus.Valid
              }}})

          Left(fullSol)
        } else {
          // only keep relation symbols that were also part of the orginal problem
          Left(res filterKeys predPool.values.toSet)
        }
        
      case Right(cex) =>
        if (lazabs.GlobalParameters.get.needFullCEX) {
          val fullCEX = preprocBackTranslator translate cex

          // verify correctness of the counterexample
          if (lazabs.Main.assertions) assert(SimpleAPI.withProver { p =>
            import p._
            fullCEX.head._1.pred == HornClauses.FALSE &&
            (fullCEX.subdagIterator forall {
               case dag@DagNode((state, clause@Clause(head, body, constraint)),
                                children, _) =>
                 // syntactic check: do clauses fit together?
                 state.pred == head.pred &&
                 children.size == body.size &&
                 (unsimplifiedClauses contains clause) &&
                 ((children.iterator zip body.iterator) forall {
                    case (c, IAtom(pred, _)) =>
                      c > 0 && dag(c)._1.pred == pred }) &&
                 // semantic check: are clause constraints satisfied?
                 scope {
                   addConstants(clause.constants.toSeq.sortWith(_.name < _.name))
                   !! (state.args === head.args)
                   for ((c, IAtom(_, args)) <- children.iterator zip body.iterator)
                     !! (dag(c)._1.args === args)
                   !! (constraint)
                   ??? == ProverStatus.Sat
                 }
             })
          })

          Right(for (p <- fullCEX) yield p._1)
        } else {
          Right(for (p <- cex) yield p._1)
        }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  def printMonolithic(converted : Seq[Clause]) : Unit =
      if (converted forall { case Clause(_, body, _) => body.size <= 1 }) {
        Console.err.println("Clauses are linear; printing monolithic form")
        
        val preds =
          (for (Clause(head, body, _) <- converted.iterator;
                IAtom(p, _) <- (Iterator single head) ++ body.iterator)
           yield p).toList.distinct

        val predNum = preds.iterator.zipWithIndex.toMap
        val maxArity = (preds map (_.arity)).max

        val p = new Predicate("p", maxArity + 1)
        val preArgs =  for (i <- 0 until (maxArity + 1))
                       yield new ConstantTerm("pre" + i)
        val postArgs = for (i <- 0 until (maxArity + 1))
                       yield new ConstantTerm("post" + i)

        val initClause = {
          val constraint = 
            or(for (Clause(IAtom(pred, args), List(), constraint) <-
                      converted.iterator;
                    if (pred != FALSE))
               yield ((postArgs.head === predNum(pred)) &
                      (args === postArgs.tail) &
                      constraint))
          Clause(IAtom(p, postArgs), List(), constraint)
        }

        if (converted exists { case Clause(IAtom(FALSE, _), List(), _) => true
                               case _ => false })
          Console.err.println("WARNING: ignoring clauses without relation symbols")
          
        val transitionClause = {
          val constraint = 
            or(for (Clause(IAtom(predH, argsH),
                           List(IAtom(predB, argsB)), constraint) <-
                      converted.iterator;
                    if (predH != FALSE))
               yield ((postArgs.head === predNum(predH)) &
                      (preArgs.head === predNum(predB)) &
                      (argsH === postArgs.tail) &
                      (argsB === preArgs.tail) &
                      constraint))
          Clause(IAtom(p, postArgs), List(IAtom(p, preArgs)), constraint)
        }

        val assertionClause = {
          val constraint = 
            or(for (Clause(IAtom(FALSE, _),
                           List(IAtom(predB, argsB)), constraint) <-
                      converted.iterator)
               yield ((preArgs.head === predNum(predB)) &
                      (argsB === preArgs.tail) &
                      constraint))
          Clause(FALSE(), List(IAtom(p, preArgs)), constraint)
        }

        val clauses =
          List(initClause, transitionClause, assertionClause)

        println(lazabs.viewer.HornSMTPrinter(horn2Eldarica(clauses)))

        System.exit(0)

      } else {

        Console.err.println("Clauses are not linear")
        System.exit(0)

      }
}

////////////////////////////////////////////////////////////////////////////////

class HornTranslator {
  
  val predicates = MHashMap[String,Literal]().empty
  def getPrincessPredLiteral(r: HornLiteral): Literal = r match {
    case RelVar(varName,params) =>
      predicates.get(varName) match{
        case Some(p) => p
        case None =>
          predicates += (varName -> new Literal {
            val predicate = new IExpression.Predicate(varName, params.size)
            val relevantArguments = (0 until params.size)
          })
          predicates(varName)
      }
      case _ =>
        throw new Exception("Invalid relation symbol")
  }
  
  def global2bup (h: HornClause): ConstraintClause = new IConstraintClause {
    import lazabs.ast.ASTree._

    val head = h.head match {
      case Interp(BoolConst(false)) => 
        new Literal {
          val predicate = lazabs.horn.bottomup.HornClauses.FALSE
          val relevantArguments = List()
        }
      case rv@_ =>
        getPrincessPredLiteral(rv)
    }
    val headParams: List[Parameter] = h.head match {
      case RelVar(_,params) => params
      case _ => List()
    }
    val bodyRelVars = (for(rv@RelVar(_,_) <- h.body) yield rv)
    
    val body = bodyRelVars.map(getPrincessPredLiteral(_))
    
    val freeVariables = {
      val free = Set[String]() ++ (for(Interp(f@_) <- h.body) yield f).map(freeVars(_)).flatten.map(_.name)
      val bound = Set[String]() ++ headParams.map(_.name) ++ bodyRelVars.map(_.params.map(_.name)).flatten
      free.filterNot(bound.contains(_))
    }
    
    val localVariableNum = freeVariables.size     
       
    def iInstantiateConstraint(headArguments : Seq[ConstantTerm],
                                 bodyArguments: Seq[Seq[ConstantTerm]],
                                 localVariables : Seq[ConstantTerm]) : IFormula = {

      //println("This is the clause: " + lazabs.viewer.HornPrinter.printDebug(h))
      //println("This is the head arguments: " + headArguments + " and the body arguments: " + bodyArguments + " and the local arguments: " + localVariables)

      val symbolMap: LinkedHashMap[String,ConstantTerm] = LinkedHashMap[String,ConstantTerm]() ++ 
        (
          headParams.map(_.name).zip(headArguments) ++
          (bodyRelVars.zip(bodyArguments).map(x => x._1.params.map(_.name).zip(x._2)).flatten.toMap) ++
          freeVariables.zip(localVariables)
        )
      val constraint = lazabs.nts.NtsHorn.assignmentsToConjunction(for(Interp(f@_) <- h.body) yield f)
      val (princessFormula,_) = formula2Princess(List(constraint),symbolMap,true)
      princessFormula.head.asInstanceOf[IFormula]
      //println("instantiated constraint: " + res)      
    }
    override def toString = lazabs.viewer.HornPrinter.printDebug(h)
  }

  def horn2Eldarica(constraints: Seq[Clause]): Seq[HornClause] = {
    var varMap = Map[ConstantTerm,String]().empty
    var xcl = 0
    var x = 0
    
    def getVar(ct : ConstantTerm) = {
      varMap get ct match {
        case Some(n) => n
        case None =>
          //lazabs.ast.ASTree.Parameter(,lazabs.types.IntegerType())
          val n = "sc_"+xcl+"_"+x
          x = x+1;
          varMap += ct->n
          n
      }
    }
    def atom(a : IAtom) : HornLiteral = {
      a match {
        case IAtom(HornClauses.FALSE,_) =>
          lazabs.horn.global.Interp(lazabs.ast.ASTree.BoolConst(false))
        case _ =>
          RelVar(
            a.pred.name,
            (for (p <- a.args) yield 
                lazabs.ast.ASTree.Parameter(
                    getVar(p.asInstanceOf[IConstant].c),
                    lazabs.types.IntegerType()
                )
            ).toList
          )
      }
    }
    def horn2Eldarica(cl : Clause) : HornClause = {
      xcl = xcl + 1
      val clNorm = cl.normalize()
      val var_all = SymbolCollector constants (clNorm.constraint)
      val symbolMap_p2e = (for (v <- var_all) yield (v, getVar(v))).toMap
      val body_atoms = Interp(formula2Eldarica(clNorm.constraint,symbolMap_p2e,false))
      val body_constr = (for (a <- clNorm.body) yield atom(a))
      HornClause(atom(clNorm.head), body_atoms :: body_constr)
    }
    
    constraints map (horn2Eldarica(_))
  }
  
    var predPool = Map[(String,Int),ap.terfor.preds.Predicate]().empty
    def getPred(name: String, arity: Int): ap.terfor.preds.Predicate = predPool.get((name,arity)) match{
      case Some(p) => p
      case None => 
        val newPredicate = new ap.terfor.preds.Predicate(name, arity)
        predPool += (name,arity) -> newPredicate
        newPredicate
    }
    
    def transform(cl: HornClause): Clause = {

      val symbolMap = LinkedHashMap[String, ConstantTerm]().empty      
      lazabs.prover.PrincessWrapper.resetSymbolReservoir

      val headAtom = cl.head match {
        case Interp(lazabs.ast.ASTree.BoolConst(false)) => IAtom(HornClauses.FALSE, List())
        case RelVar(varName, params) =>
          val (ps,sym) = lazabs.prover.PrincessWrapper.formula2Princess(
            params.map(p => (lazabs.ast.ASTree.Variable(p.name).stype(lazabs.types.IntegerType()))),
            symbolMap,true)
          IAtom(getPred(varName, params.size),ps.asInstanceOf[List[ITerm]])
        case _ => throw new UnsupportedOperationException
      }

      var interpFormulas = List[IExpression]()
      var relVarAtoms = List[IAtom]()

      cl.body.foreach { lit => lit match {
        case Interp(e) => 
          val (interp,sym) = lazabs.prover.PrincessWrapper.formula2Princess(List(e),symbolMap,true)
          interpFormulas ::= interp.head
        case RelVar(varName, params)  =>
          val (ps,sym) = lazabs.prover.PrincessWrapper.formula2Princess(
            params.map(p => (lazabs.ast.ASTree.Variable(p.name).stype(lazabs.types.IntegerType()))),
            symbolMap,true)
          val relVarAtom = IAtom(getPred(varName, params.size),ps.asInstanceOf[List[ITerm]])
          relVarAtoms ::= relVarAtom
      }}

      Clause(headAtom,relVarAtoms, interpFormulas.size match {
        case 0 => true
        case 1 => interpFormulas.head.asInstanceOf[IFormula]
        case _ => interpFormulas.reduceLeft((a,b) => a.asInstanceOf[IFormula] & b.asInstanceOf[IFormula]).asInstanceOf[IFormula]      
      })
    }
  
}