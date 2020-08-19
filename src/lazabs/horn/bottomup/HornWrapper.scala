/**
  * Copyright (c) 2011-2020 Hossein Hojjat and Philipp Ruemmer.
  * All rights reserved.
  *
  * Redistribution and use in source and binary forms, with or without
  * modification, are permitted provided that the following conditions are met:
  *
  * * Redistributions of source code must retain the above copyright notice, this
  * list of conditions and the following disclaimer.
  *
  * * Redistributions in binary form must reproduce the above copyright notice,
  * this list of conditions and the following disclaimer in the documentation
  * and/or other materials provided with the distribution.
  *
  * * Neither the name of the authors nor the names of their
  * contributors may be used to endorse or promote products derived from
  * this software without specific prior written permission.
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
import ap.types.MonoSortedPredicate
import lazabs.GlobalParameters
import lazabs.ParallelComputation
import lazabs.Main.{StoppedException, TimeoutException}
import lazabs.horn.preprocessor.{DefaultPreprocessor, HornPreprocessor}
import HornPreprocessor.BackTranslator
import lazabs.horn.bottomup.HornClauses._
import lazabs.horn.global._
import lazabs.utils.Manip._
import lazabs.prover.PrincessWrapper
import PrincessWrapper._
import lazabs.prover.Tree
import lazabs.types.Type
import Util._
import HornPredAbs.RelationSymbol
import lazabs.horn.abstractions.{AbsLattice, AbsReader, AbstractionRecord, EmptyVerificationHints, LoopDetector, StaticAbstractionBuilder, VerificationHints}
import AbstractionRecord.AbstractionMap
import StaticAbstractionBuilder.AbstractionType
import lazabs.horn.abstractions.VerificationHints.VerifHintTplEqTerm
import lazabs.horn.concurrency.{DrawHornGraph, HintsSelection, ReaderMain}

import scala.collection.mutable.{LinkedHashMap, HashMap => MHashMap, HashSet => MHashSet}


object HornWrapper {

  object NullStream extends java.io.OutputStream {
    def write(b: Int) = {}
  }


  def verifySolution(fullSol : HornPreprocessor.Solution,
                     unsimplifiedClauses : Seq[Clause]) : Unit = {
          // verify correctness of the solution
          if (lazabs.Main.assertions) assert(SimpleAPI.withProver { p =>
            import p._
            unsimplifiedClauses forall { case clause@Clause(head, body, constraint) => scope {
                addConstants(clause.constants.toSeq.sortWith(_.name < _.name))

                for (c <- clause.constants) (Sort sortOf c) match {
                  case Sort.MultipleValueBool =>
                    // since we are making use of the equivalence
                    // x == False <=> x != True, we need to add bounds on Boolean
                    // variables (corresponding to the law of the excluded middle)
                    !! (Sort.Bool.membershipConstraint(c))
                  case _ =>
                    // nothing
                }

                !! (constraint)
                for (IAtom(pred, args) <- body)
                  !! (subst(fullSol(pred), args.toList, 0))
                ?? (if (head.pred == HornClauses.FALSE)
                      i(false)
                    else
                      subst(fullSol(head.pred), head.args.toList, 0))
                ??? == ProverStatus.Valid
              }}})
  }

  def verifyCEX(fullCEX: HornPreprocessor.CounterExample,
                unsimplifiedClauses: Seq[Clause]): Unit = {
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
                  c > 0 && dag(c)._1.pred == pred
              }) &&
              // semantic check: are clause constraints satisfied?
              scope {
                addConstants(clause.constants.toSeq.sortWith(_.name < _.name))
                !!(state.args === head.args)
                for ((c, IAtom(_, args)) <- children.iterator zip body.iterator)
                  !!(dag(c)._1.args === args)
                !!(constraint)
                ??? == ProverStatus.Sat
              }
        })
    })
  }

}

////////////////////////////////////////////////////////////////////////////////

class HornWrapper(constraints: Seq[HornClause],
                  uppaalAbsMap: Option[Map[String, AbsLattice]],
                  lbe: Boolean,
                  disjunctive: Boolean) {

  def printClauses(cs: Seq[Clause]) = {
    for (c <- cs) {
      println(c);
    }
  }

  private val translator = new HornTranslator

  import translator._

  //////////////////////////////////////////////////////////////////////////////

  GlobalParameters.get.setupApUtilDebug

  private val outStream =
    if (GlobalParameters.get.logStat)
      Console.err
    else
      HornWrapper.NullStream

  private val originalClauses = constraints
  private val unsimplifiedClauses = originalClauses map (transform(_))

  //    if (GlobalParameters.get.printHornSimplified)
  //      printMonolithic(unsimplifiedClauses)

  //////////////////////////////////////////////////////////////////////////////

  private def readHints(filename: String,
                        name2Pred: Map[String, Predicate])
  : VerificationHints = filename match {
    case "" =>
      EmptyVerificationHints
    case hintsFile => {
      val reader = new AbsReader(
        new java.io.BufferedReader(
          new java.io.FileReader(hintsFile)))
      val hints =
        (for ((predName, hints) <- reader.allHints.iterator;
              pred = name2Pred get predName;
              if {
                if (pred.isDefined) {
                  if (pred.get.arity != reader.predArities(predName))
                    throw new Exception(
                      "Hints contain predicate with wrong arity: " +
                        predName + " (should be " + pred.get.arity + " but is " +
                        reader.predArities(predName) + ")")
                } else {
                  Console.err.println(
                    "   Ignoring hints for " + predName + "\n")
                }
                pred.isDefined
              }) yield {
          (pred.get, hints)
        }).toMap
      VerificationHints(hints)
    }
  }

  private val hints: VerificationHints = {
    val name2Pred =
      (for (Clause(head, body, _) <- unsimplifiedClauses.iterator;
            IAtom(p, _) <- (head :: body).iterator)
        yield (p.name -> p)).toMap
    readHints(GlobalParameters.get.cegarHintsFile, name2Pred)
  }



  //////////////////////////////////////////////////////////////////////////////

  private val (simplifiedClauses, simpPreHints, preprocBackTranslator) =
    Console.withErr(outStream) {
      val (simplifiedClauses, simpPreHints, backTranslator) =
        if (lbe) {
          (unsimplifiedClauses, hints, HornPreprocessor.IDENTITY_TRANSLATOR)
        } else {
          val preprocessor = new DefaultPreprocessor
          preprocessor.process(unsimplifiedClauses, hints)
        }

      if (GlobalParameters.get.printHornSimplified) {
        //      println("-------------------------------")
        //      printClauses(simplifiedClauses)
        //      println("-------------------------------")

        println("Clauses after preprocessing:")
        for (c <- simplifiedClauses)
          println(c.toPrologString)

        //val aux = simplifiedClauses map (horn2Eldarica(_))
        //      val aux = horn2Eldarica(simplifiedClauses)
        //      println(lazabs.viewer.HornPrinter(aux))
        //      simplifiedClauses = aux map (transform(_))
        //      println("-------------------------------")
        //      printClauses(simplifiedClauses)
        //      println("-------------------------------")
      }

      (simplifiedClauses, simpPreHints, backTranslator)
    }


  //print horn graph in smt format
  val sortedHints = HintsSelection.sortHints(simpPreHints)
  if (GlobalParameters.get.getHornGraph == true) {
    //val argumentList = (for (p <- HornClauses.allPredicates(simplifiedClauses)) yield (p, p.arity)).toList
    //HintsSelection.writeArgumentScoreToFile(GlobalParameters.get.fileName, argumentList, sortedHints)
    DrawHornGraph.writeHornClausesGraphToFile(GlobalParameters.get.fileName, simplifiedClauses, sortedHints) //write horn graph and gnn to file
    //println(simplifiedClauses)
    //val hornGraph = new GraphTranslator(simpClauses, GlobalParameters.get.fileName)
    sys.exit()
  }


  private val postHints: VerificationHints = {
    val name2Pred =
      (for (Clause(head, body, _) <- simplifiedClauses.iterator;
            IAtom(p, _) <- (head :: body).iterator)
        yield (p.name -> p)).toMap
    readHints(GlobalParameters.get.cegarPostHintsFile, name2Pred)
  }


  val allHints = simpPreHints ++ postHints


  val params =
    if (lazabs.GlobalParameters.get.templateBasedInterpolationPortfolio)
      lazabs.GlobalParameters.get.withAndWOTemplates
    else
      List()

  val result: Either[Map[Predicate, IFormula], Dag[IAtom]] =
    ParallelComputation(params) {
      new InnerHornWrapper(unsimplifiedClauses, simplifiedClauses,
        allHints, preprocBackTranslator,
        disjunctive, outStream).result
    }



  //////////////////////////////////////////////////////////////////////////////

  def printMonolithic(converted: Seq[Clause]): Unit =
    if (converted forall { case Clause(_, body, _) => body.size <= 1 }) {
      Console.err.println("Clauses are linear; printing monolithic form")

      val preds =
        (for (Clause(head, body, _) <- converted.iterator;
              IAtom(p, _) <- (Iterator single head) ++ body.iterator)
          yield p).toList.distinct

      val predNum = preds.iterator.zipWithIndex.toMap
      val maxArity = (preds map (_.arity)).max

      val p = new Predicate("p", maxArity + 1)
      val preArgs = for (i <- 0 until (maxArity + 1))
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
      case _ => false
      })
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

class ArgumentReader(reader: java.io.Reader){

}

class InnerHornWrapper(unsimplifiedClauses: Seq[Clause],
                       simplifiedClauses: Seq[Clause],
                       simpHints: VerificationHints,
                       preprocBackTranslator: BackTranslator,
                       disjunctive: Boolean,
                       outStream: java.io.OutputStream) {



  /** Automatically computed interpolation abstraction hints */
  private val abstractionType =
    lazabs.GlobalParameters.get.templateBasedInterpolationType

  private lazy val absBuilder =
    new StaticAbstractionBuilder(simplifiedClauses, abstractionType)

  private lazy val autoAbstraction: AbstractionMap =
    absBuilder.abstractionRecords

  /** Manually provided interpolation abstraction hints */
  private lazy val hintsAbstraction: AbstractionMap =
    if (simpHints.isEmpty)
      Map()
    else
      absBuilder.loopDetector hints2AbstractionRecord simpHints

  /** Learned interpolation abstraction hints */
  //read ranks from file

  println("--------auto-generated-templates----------")
  absBuilder.abstractionHints.pretyPrintHints()

  val rankedArumentFileName=""
  private val learnedHints=learnedInterpolationAbstractionHints(rankedArumentFileName,simplifiedClauses,absBuilder.abstractionHints)

  private lazy val learnedHintsAbstraction: AbstractionMap =
    absBuilder.loopDetector hints2AbstractionRecord learnedHints


  private def learnedInterpolationAbstractionHints(filename: String,
                                  simplifiedClauses: Seq[Clause],
                                  hints:VerificationHints)
  : VerificationHints = filename match {
    case "" =>
      EmptyVerificationHints
    case hintsFile => {
      val argumentList=(for (p <- HornClauses.allPredicates(simplifiedClauses)) yield (p, p.arity)).toList
      val reader = new ArgumentReader(
        new java.io.BufferedReader(
          new java.io.FileReader(hintsFile)))

      //todo:change cost
      VerificationHints(Map())
    }
  }
  //////////////////////////////////////////////////////////////////////////////

  private val predGenerator = Console.withErr(outStream) {
    if (lazabs.GlobalParameters.get.templateBasedInterpolation) {
      val autoAndManualAbstractionMAP =
        AbstractionRecord.mergeMaps(hintsAbstraction, autoAbstraction)

      val fullAbstractionMap =
        AbstractionRecord.mergeMaps(autoAndManualAbstractionMAP, learnedHintsAbstraction)

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

  if (GlobalParameters.get.templateBasedInterpolationPrint &&
    !simpHints.isEmpty)
    ReaderMain.printHints(simpHints, name = "Manual verification hints:")

  //////////////////////////////////////////////////////////////////////////////


  val result: Either[Map[Predicate, IFormula], Dag[IAtom]] = {
    val counterexampleMethod =
      if (disjunctive)
        HornPredAbs.CounterexampleMethod.AllShortest
      else
        HornPredAbs.CounterexampleMethod.FirstBestShortest

    val result = Console.withOut(outStream) {
      println
      println(
        "----------------------------------- CEGAR --------------------------------------")


      (new HornPredAbs(simplifiedClauses,
        simpHints.toInitialPredicates, predGenerator,
        counterexampleMethod)).result

      val predAbs =
        new HornPredAbs(simplifiedClauses,
          simpHints.toInitialPredicates, predGenerator,
          counterexampleMethod)
      val result =
        predAbs.result

      lazabs.GlobalParameters.get.predicateOutputFile match {
        case "" =>
        // nothing
        case filename => {
          val predicates =
            VerificationHints(
              //for ((p, preds) <- absBuilder.abstractionHints) yield {
              for ((p, preds) <- predAbs.relevantPredicates) yield {
                val hints =
                  for (f <- preds) yield VerificationHints.VerifHintInitPred(f)
                p -> hints
              })

          println(
            "Saving CEGAR predicates to " + filename)

          val output = new java.io.FileOutputStream(filename)
          Console.withOut(output) {
            AbsReader.printHints(absBuilder.abstractionHints)
            //AbsReader.printHints(predicates)
          }
        }
      }

      result

    }


    result match {
      case Left(res) =>
        if (lazabs.GlobalParameters.get.needFullSolution) {
          val fullSol = preprocBackTranslator translate res
          HornWrapper.verifySolution(fullSol, unsimplifiedClauses)
          Left(fullSol)
        } else {
          // only keep relation symbols that were also part of the orginal problem
          Left(res filterKeys allPredicates(unsimplifiedClauses))
        }

      case Right(cex) =>
        if (lazabs.GlobalParameters.get.needFullCEX) {
          val fullCEX = preprocBackTranslator translate cex
          HornWrapper.verifyCEX(fullCEX, unsimplifiedClauses)
          Right(for (p <- fullCEX) yield p._1)
        } else {
          Right(for (p <- cex) yield p._1)
        }
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

class HornTranslator {

  val predicates = MHashMap[String, Literal]().empty

  def getPrincessPredLiteral(r: HornLiteral): Literal = r match {
    case RelVar(varName, params) =>
      predicates.get(varName) match {
        case Some(p) => p
        case None =>
          predicates += (varName -> new Literal {
            // TODO: we should generate a MonoSortedPredicate at this point
            val predicate = new IExpression.Predicate(varName, params.size)
            val relevantArguments = (0 until params.size)
          })
          predicates(varName)
      }
    case _ =>
      throw new Exception("Invalid relation symbol")
  }

  def global2bup(h: HornClause): ConstraintClause = new IConstraintClause {

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
      case RelVar(_, params) => params
      case _ => List()
    }
    val bodyRelVars = (for (rv@RelVar(_, _) <- h.body) yield rv)

    val body = bodyRelVars.map(getPrincessPredLiteral(_))

    val freeVariables = {
      val free = Set[String]() ++ (for (Interp(f@_) <- h.body) yield f).map(freeVars(_)).flatten.map(_.name)
      val bound = Set[String]() ++ headParams.map(_.name) ++ bodyRelVars.map(_.params.map(_.name)).flatten
      free.filterNot(bound.contains(_))
    }

    val localVariableNum = freeVariables.size

    def iInstantiateConstraint(headArguments: Seq[ConstantTerm],
                               bodyArguments: Seq[Seq[ConstantTerm]],
                               localVariables: Seq[ConstantTerm]): IFormula = {

      //println("This is the clause: " + lazabs.viewer.HornPrinter.printDebug(h))
      //println("This is the head arguments: " + headArguments + " and the body arguments: " + bodyArguments + " and the local arguments: " + localVariables)

      val symbolMap: LinkedHashMap[String, ConstantTerm] = LinkedHashMap[String, ConstantTerm]() ++
        (
          headParams.map(_.name).zip(headArguments) ++
            (bodyRelVars.zip(bodyArguments).map(x => x._1.params.map(_.name).zip(x._2)).flatten.toMap) ++
            freeVariables.zip(localVariables)
          )
      val constraint = lazabs.nts.NtsHorn.assignmentsToConjunction(for (Interp(f@_) <- h.body) yield f)
      val (princessFormula, _) = formula2Princess(List(constraint), symbolMap, true)
      princessFormula.head.asInstanceOf[IFormula]
      //println("instantiated constraint: " + res)      
    }

    override def toString = lazabs.viewer.HornPrinter.printDebug(h)
  }

  def horn2Eldarica(constraints: Seq[Clause]): Seq[HornClause] = {
    var varMap = Map[ConstantTerm, String]().empty
    var xcl = 0
    var x = 0

    def getVar(ct: ConstantTerm) = {
      varMap get ct match {
        case Some(n) => n
        case None =>
          //lazabs.ast.ASTree.Parameter(,lazabs.types.IntegerType())
          val n = "sc_" + xcl + "_" + x
          x = x + 1;
          varMap += ct -> n
          n
      }
    }

    def atom(a: IAtom): HornLiteral = {
      a match {
        case IAtom(HornClauses.FALSE, _) =>
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

    def horn2Eldarica(cl: Clause): HornClause = {
      xcl = xcl + 1
      val clNorm = cl.normalize()
      val var_all = SymbolCollector constants (clNorm.constraint)
      val symbolMap_p2e = (for (v <- var_all) yield (v, getVar(v))).toMap
      val body_atoms = Interp(formula2Eldarica(clNorm.constraint, symbolMap_p2e, false))
      val body_constr = (for (a <- clNorm.body) yield atom(a))
      HornClause(atom(clNorm.head), body_atoms :: body_constr)
    }

    constraints map (horn2Eldarica(_))
  }

  val predPool = new MHashMap[(String, Int), Predicate]

  def relVar2Atom(rv: RelVar,
                  symbolMap: LinkedHashMap[String, ConstantTerm]): IAtom = {
    val RelVar(varName, params) =
      rv
    val argExprs =
      params.map(p => (lazabs.ast.ASTree.Variable(p.name).stype(p.typ)))

    val (ps, _) = formula2Princess(argExprs, symbolMap, true)
    val pred = predPool.getOrElseUpdate((varName, params.size), {
      val sorts = for (p <- params) yield type2Sort(p.typ)
      MonoSortedPredicate(varName, sorts)
    })
    IAtom(pred, ps.asInstanceOf[List[ITerm]])
  }

  def transform(cl: HornClause): Clause = {

    val symbolMap = LinkedHashMap[String, ConstantTerm]().empty

    val headAtom = cl.head match {
      case Interp(lazabs.ast.ASTree.BoolConst(false)) =>
        IAtom(HornClauses.FALSE, List())
      case rv: RelVar =>
        relVar2Atom(rv, symbolMap)
      case _ =>
        throw new UnsupportedOperationException
    }

    var interpFormulas = List[IExpression]()
    var relVarAtoms = List[IAtom]()

    // first translate relation symbols in the body
    for (rv <- cl.body) rv match {
      case rv: RelVar =>
        relVarAtoms ::= relVar2Atom(rv, symbolMap)
      case _ =>
      // nothing
    }

    // and then interpreted constraints
    for (rv <- cl.body) rv match {
      case Interp(e) => {
        val (interp, sym) = formula2Princess(List(e), symbolMap, true)
        interpFormulas ::= interp.head
      }
      case _ =>
      // nothing
    }

    Clause(headAtom, relVarAtoms,
      and(interpFormulas map (PrincessWrapper expr2Formula _)))
  }

}
