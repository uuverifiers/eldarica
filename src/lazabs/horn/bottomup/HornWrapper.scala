/**
 * Copyright (c) 2011-2014 Hossein Hojjat and Philipp Ruemmer.
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

import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.global._
import lazabs.utils.Manip._
import ap.parser._
import IExpression._
import lazabs.prover.PrincessWrapper._
import lazabs.prover.Tree
import Util._
import HornPredAbs.{RelationSymbol}
import lazabs.horn.abstractions.{AbsLattice, TermSubsetLattice, ProductLattice,
                                 AbsReader, LoopDetector}

import scala.collection.mutable.{HashSet => MHashSet, HashMap => MHashMap,
                                 LinkedHashMap}


object HornWrapper {

  object NullStream extends java.io.OutputStream {
    def write(b : Int) = {}
  }

}

////////////////////////////////////////////////////////////////////////////////

class HornWrapper(constraints: Seq[HornClause], 
                  absMap: Option[Map[String, AbsLattice]],
                  lbe: Boolean,
                  log : Boolean,
                  disjunctive : Boolean,
                  interpolatorType : (Boolean, Boolean)) {

  import HornWrapper._

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
  private val converted = originalClauses map (transform(_))

//    if (lazabs.GlobalParameters.get.printHornSimplified)
//      printMonolithic(converted)

  private val simplified = Console.withErr(outStream) {
    var simplified =
      if (!lbe)
        new HornPreprocessor(converted).result
      else
        converted

    // problem: transforming back and forth doesn't produce  
    if (lazabs.GlobalParameters.get.printHornSimplified) {
      println("-------------------------------")
      printClauses(simplified)
      println("-------------------------------")
      println("simplified clauses:")
      //val aux = simplified map (horn2Eldarica(_))
      val aux = horn2Eldarica(simplified)
      println(lazabs.viewer.HornPrinter(aux))
      simplified = aux map (transform(_))
      println("-------------------------------")
      printClauses(simplified)
      println("-------------------------------")
    }

    simplified
  }

  //////////////////////////////////////////////////////////////////////////////

  private val hintsReader =
    lazabs.GlobalParameters.get.cegarHintsFile match {
      case "" =>
        None
      case hintsFile =>
        Some(new AbsReader (
               new java.io.BufferedReader (
                 new java.io.FileReader(hintsFile))))
  }

  private lazy val loopDetector = new LoopDetector(simplified)

  //////////////////////////////////////////////////////////////////////////////

  private val predGenerator = Console.withErr(outStream) {
    interpolatorType match {
      case (true, true) => {
        val Some(am) = absMap
        assert(!am.isEmpty)
        TemplateInterpolator.interpolatingPredicateGenCEXAbsUpp(am) _
      }
      case (_, false) => DagInterpolator.interpolatingPredicateGenCEXAndOr _
      case (false , true) => {
        val abstractionMap = constructAbstractionMap(simplified, hintsReader)
        TemplateInterpolator.interpolatingPredicateGenCEXAbsGen(
          abstractionMap,
          lazabs.GlobalParameters.get.templateBasedInterpolationTimeout)
//      TemplateInterpolator.interpolatingPredicateGenCEXAbs _
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def constructAbstractionMap(cs : Seq[Clause], hintsReader : Option[AbsReader])
                             : Map[Predicate, (Seq[Predicate], AbsLattice)] =
    hintsReader match {
      case Some(reader) if (!reader.templates.isEmpty) => {
        (for ((predName, lattice) <- reader.templates.iterator;
              pred = loopDetector.loopHeads.find((_.name == predName));
              if {
                if (!pred.isDefined)
                  Console.err.println("   Ignoring templates for " + predName + "\n" +
                                      "   (no loop head, or eliminated during simplification)")
                pred.isDefined
              }) yield {
           (pred.get, (loopDetector bodyPredicates pred.get, lattice))
         }).toMap
      }

      case _ => {
        new lazabs.horn.abstractions.StaticAbstractionBuilder(
          cs, lazabs.GlobalParameters.get.templateBasedInterpolationType).abstractions
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  private val initialPredicates : Map[Predicate, Seq[IFormula]] = hintsReader match {
    case Some(reader) if (!reader.initialPredicates.isEmpty) => {
      (for ((predName, formulas) <- reader.initialPredicates.iterator;
              pred = loopDetector.allPredicates.find((_.name == predName));
              if {
                if (!pred.isDefined)
                  Console.err.println("   Ignoring initial predicates for " + predName + "\n" +
                                      "   (might be unreachable or eliminated during simplification)")
                pred.isDefined
              }) yield {
           (pred.get, formulas)
         }).toMap
    }
    case _ =>
      Map()
  }

  //////////////////////////////////////////////////////////////////////////////

  val result : Either[Map[Predicate, IFormula], Dag[IAtom]] = {

    val counterexampleMethod =
      if (disjunctive)
        HornPredAbs.CounterexampleMethod.AllShortest
      else
        HornPredAbs.CounterexampleMethod.FirstBestShortest

    (Console.withOut(outStream)(
       new HornPredAbs(simplified,
                       initialPredicates, predGenerator,
                       counterexampleMethod))).result match {
      case Left(res) =>
        // only keep relation symbols that were also part of the orginal problem
        Left(res filterKeys predPool.values.toSet)
      case Right(cex) => Right(for (p <- cex) yield p._1)
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