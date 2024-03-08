/**
 * Copyright (c) 2011-2023 Hossein Hojjat, Filip Konecny, Philipp Ruemmer.
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

package lazabs.horn.parser

import java.io.{FileInputStream, InputStream, FileNotFoundException, Reader, BufferedReader, FileReader, File}

import lazabs.horn.global._
import lazabs.prover.PrincessWrapper
import lazabs.ast.ASTree._
import lazabs.types.IntegerType
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts

import ap.parser._
import ap.theories.{Theory, TheoryRegistry, TheoryCollector, ADT, SimpleArray,
                    MulTheory, ModuloArithmetic, ExtArray, Heap, DivZero}
import ap.theories.nia.GroebnerMultiplication
import ap.{SimpleAPI, Signature}
import SimpleAPI.ProverStatus
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.terfor.{TerForConvenience, TermOrder}
import ap.types.{SortedPredicate, MonoSortedPredicate, SortedIFunction,
                 TypeTheory}
import ap.parameters.{ParserSettings, PreprocessingSettings, Param}

import scala.collection.{Map => CMap}
import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer,
                                 HashSet => MHashSet, LinkedHashSet}

object HornReader {
  def apply(inputStream: Reader): Seq[HornClause] = {
    val lexer = new HornLexer(inputStream)
    val parser = new Parser(lexer)
    val tree = parser.parse()
    (scala.collection.JavaConversions.asScalaBuffer(
       tree.value.asInstanceOf[java.util.List[HornClause]]))
  }

  def fromSMT(fileName: String) : Seq[HornClause] = {
    val inputStream = new BufferedReader(new FileReader(new File(fileName)))
    fromSMT(inputStream)
  }

  def fromSMT(inputStream: Reader) : Seq[HornClause] = {
    SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>
      (new SMTHornReader(inputStream, p)).result
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  protected[parser] def cnf_if_needed(aF : IFormula) : Seq[IFormula] =
    PartialCNFConverter(aF).toList

  /**
   * Convert a formula in NNF to CNF, as far as necessary to isolate
   * all uninterpreted predicates.
   */
  object PartialCNFConverter
         extends CollectingVisitor[Unit, Seq[(IFormula, IFormula)]] {

    def apply(f : IFormula) : Seq[IFormula] =
      for ((f1, f2) <- visit(f, ())) yield (f1 ||| f2)

    override def preVisit(t : IExpression,
                          arg : Unit) : PreVisitResult = t match {
      case t@IAtom(p, _) if TheoryRegistry.lookupSymbol(p).isEmpty =>
        ShortCutResult(List((t, false)))
      case t@INot(IAtom(p, _)) if TheoryRegistry.lookupSymbol(p).isEmpty =>
        ShortCutResult(List((t, false)))
      case IBinFormula(IBinJunctor.And | IBinJunctor.Or, _, _) =>
        KeepArg
      case IBinFormula(IBinJunctor.Eqv, f1, f2) => {
        assert(false)
        KeepArg
      }
      case f : IQuantified =>
        // quantified formulas are handled later, we just keep them at
        // this point
        ShortCutResult(List((false, f)))
      case f : IFormula => {
        if(ContainsSymbol(f, (e : IExpression) => e match {
              case IAtom(p, _) => TheoryRegistry.lookupSymbol(p).isEmpty
              case _ : IExpression => false
                          }))
          throw new Exception(
            "Not able to isolate uninterpreted predicates, input is not Horn")
        ShortCutResult(List((false, f)))
      }
    }

    def postVisit(t      : IExpression,
                  arg    : Unit,
                  subres : Seq[Seq[(IFormula, IFormula)]])
        : Seq[(IFormula, IFormula)] = t match {
      case t@IBinFormula(j, _, _) => subres match {
        case Seq(Seq((IBoolLit(false), _)), Seq((IBoolLit(false), _))) =>
          List((false, t))
        case _ => j match {
          case IBinJunctor.And =>
            subres(0) ++ subres(1)
          case IBinJunctor.Or =>
            for ((f1, f2) <- subres(0); (g1, g2) <- subres(1))
            yield (f1 ||| g1, f2 ||| g2)
        }
      }
    }

  }

  //////////////////////////////////////////////////////////////////////////////

  object PredUnderQuantifierVisitor
         extends ContextAwareVisitor[Unit, Unit] {
    private object FoundPredUnderQuantifier extends Exception

    def apply(f : IExpression) : Boolean =
      try {
        visitWithoutResult(f, Context(()))
        false
      } catch {
        case FoundPredUnderQuantifier => true
      }

    override def preVisit(t : IExpression,
                          arg : Context[Unit]) : PreVisitResult = t match {
      case a : IAtom
          if !arg.binders.isEmpty &&
             (TheoryRegistry lookupSymbol a.pred).isEmpty =>
        throw FoundPredUnderQuantifier
      case _ =>
        super.preVisit(t, arg)
    }
   
    def postVisit(t : IExpression,
                  arg : Context[Unit],
                  subres : Seq[Unit]) : Unit = ()
  }

  /**
   * Check whether a clause contains quantified literals in the body
   */
  object QuantifiedBodyPredsVisitor
         extends ContextAwareVisitor[Unit, Unit] {
    private object FoundPredUnderQuantifier extends Exception

    def apply(f : IExpression) : Boolean =
      try {
        visitWithoutResult(f, Context(()))
        false
      } catch {
        case FoundPredUnderQuantifier => true
      }

    override def preVisit(t : IExpression,
                          ctxt : Context[Unit]) : PreVisitResult = t match {
      case a : IAtom
        if ctxt.polarity < 0 && (ctxt.binders contains Context.EX) &&
           (TheoryRegistry lookupSymbol a.pred).isEmpty =>
        throw FoundPredUnderQuantifier
      case _ =>
        super.preVisit(t, ctxt)
    }
   
    def postVisit(t : IExpression,
                  arg : Context[Unit],
                  subres : Seq[Unit]) : Unit = ()
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Visitor for eliminating the functions encoding division and
   * modulo by zero. Those functions (reflecting SMT-LIB semantics)
   * cannot be handle properly in Horn clauses.
   */
  object DivZeroEliminator extends CollectingVisitor[Unit, IExpression] {
    import IExpression._

    def apply(f : IFormula) = visit(f, ()).asInstanceOf[IFormula]

    def isDivZeroFunction(f : IFunction) : Boolean =
      TheoryRegistry.lookupSymbol(f) match {
        case Some(_ : DivZero) => true
        case _                 => false
      }

    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[IExpression]) : IExpression = t match {
      case IFunApp(f, Seq(t)) if isDivZeroFunction(f) => {
        val sort = Sort sortOf t
        println("Warning: eliminating div-zero function")
        sort.eps(false)
      }
      case _ =>
        t update subres
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

class SMTHornReader protected[parser] (
         inputStream: Reader,
         // we need a prover for some of the
         // clause preprocessing, in general
         p : SimpleAPI) {

  import IExpression._
  import HornReader.{cnf_if_needed, PredUnderQuantifierVisitor,
                     QuantifiedBodyPredsVisitor, DivZeroEliminator}

  private val outStream =
     if (lazabs.GlobalParameters.get.logStat)
       Console.err
     else
       lazabs.horn.bottomup.HornWrapper.NullStream

  Console.withOut(outStream) {
    println(
      "---------------------------------- Parsing -------------------------------------")
  }

  private val reader = new BufferedReader(inputStream)
  private val settings = Param.BOOLEAN_FUNCTIONS_AS_PREDICATES.set(
                   ParserSettings.DEFAULT, true)

  private val (oriF, _, oriSignature) =
    (new SMTParser2InputAbsy(new Environment, settings, null) {
      protected override def
        incrementalityMessage(thing : String, warnOnly : Boolean) : String =
          if (warnOnly) ("ignoring " + thing) else (thing + " is not supported")
      protected override def
        neverInline(expr : IExpression) : Boolean = false
    })(reader)

  reader.close

  //////////////////////////////////////////////////////////////////////////////
  // if necessary, introduce quantifiers for array arguments

  private val (f, unintPredicates, signature) = {
    val oriUnintPredicates = new LinkedHashSet[Predicate]

    for (p <- oriSignature.order.orderedPredicates.toSeq.sortBy(_.name))
      if (!(TheoryRegistry lookupSymbol p).isDefined)
        oriUnintPredicates += p

    lazabs.GlobalParameters.get.arrayQuantification match {
      case None =>
        (oriF, oriUnintPredicates, oriSignature)
        
      case Some(quanNum) => {
        val unintPredMapping = new MHashMap[Predicate, IFormula]
        val newPreds = new ArrayBuffer[Predicate]

        val unintPredicates = for (p <- oriUnintPredicates) yield {
          val sorts = predArgumentSorts(p)
          var quanCnt = 0
          val newSorts =
            (for (s <- sorts;
                  r <- s match {
                    case SimpleArray.ArraySort(1) => {
                      // replace every array argument with 2*quanNum arguments
                      quanCnt = quanCnt + quanNum
                      for (_ <- 0 until quanNum*2) yield Sort.Integer
                    }
                    case ExtArray.ArraySort(theory)
                      if (theory.indexSorts == Seq(Sort.Integer) &&
                          theory.objSort == Sort.Integer) => {
                      // replace every array argument with 2*quanNum arguments
                      quanCnt = quanCnt + quanNum
                      for (_ <- 0 until quanNum*2) yield Sort.Integer
                    }
                    case SimpleArray.ArraySort(_) | ExtArray.ArraySort(_) =>
                      throw new Exception (
                        "Only unary arrays over integers are supported")
                    case s => List(s)
                  })
             yield r).toList

          if (quanCnt == 0) {
            p
          } else {
            lazabs.GlobalParameters.get.didIncompleteTransformation = true
            
            val newP = MonoSortedPredicate(p.name, newSorts)
            newPreds += newP
            
            var quanInd = 0
            val newPArgs =
              (for ((s, n) <- sorts.iterator.zipWithIndex;
                    t <- s match {
                      case SimpleArray.ArraySort(1) =>
                        for (k <- 0 until quanNum;
                             qi = { quanInd = quanInd + 1; quanInd - 1 };
                             t <- List(v(qi),
                                       SimpleArray(1).select(
                                         v(n + quanCnt), v(qi))))
                        yield t
                      case ExtArray.ArraySort(theory) =>
                        for (k <- 0 until quanNum;
                             qi = { quanInd = quanInd + 1; quanInd - 1 };
                             t <- List(v(qi),
                                       theory.select(v(n + quanCnt), v(qi))))
                        yield t
                      case _ =>
                        Iterator single v(n + quanCnt)
                    })
               yield t).toList

            val quanAtom =
              quan(for (_ <- 0 until quanCnt) yield Quantifier.ALL,
                   IAtom(newP, newPArgs))

            unintPredMapping.put(p, quanAtom)
            newP
          }
        }

        val newOrder = oriSignature.order extendPred newPreds

        (UniformSubstVisitor(oriF, unintPredMapping),
         unintPredicates, oriSignature updateOrder newOrder)
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  val clauses = Console.withOut(outStream) {
    LineariseVisitor(Transform2NNF(DivZeroEliminator(!f)), IBinJunctor.And)
  }

  if (!signature.theories.isEmpty)
    Console.withOut(outStream) {
      println("Theories: " + (signature.theories mkString ", "))
    }

  if (signature.theories exists {
        case _ : SimpleArray  => false
        case _ : ExtArray     => false
        case _ : Heap         => false
        case _ : ADT          => false
        case _ : MulTheory    => false
        case _ : DivZero      => false
        case TypeTheory       => false
        case ModuloArithmetic => false
        case _                => true
      })
    throw new Exception ("Combination of theories is not supported: " +
                           signature.theories.mkString(", "))

  val canEliminateBodyQuantifiers =
    signature.theories forall {
      case _ : SimpleArray => true
      case _ : ExtArray    => true
      case _ : DivZero     => true
      case TypeTheory      => true
      case _               => false
    }

  lazabs.GlobalParameters.get.arrayQuantification match {
    case Some(num) if !canEliminateBodyQuantifiers =>
      throw new Exception ("Option -arrayQuans:" + num +
                             " is not supported in combination with" +
                             " the given theories. Use -arrayQuans:off")
    case _ =>
      // ok
  }

  val elimArrays =
    lazabs.GlobalParameters.get.arrayQuantification.isDefined ||
    (clauses exists (QuantifiedBodyPredsVisitor(_)))

  if (elimArrays && !canEliminateBodyQuantifiers)
    throw new Exception ("Cannot eliminate arrays in clauses due to theories")

  if (elimArrays)
    Console.withOut(outStream) {
      println("Eliminating arrays using instantiation (incomplete)")
    }

  private val eldClauses = for (cc <- clauses) yield {
    var symMap = Map[ConstantTerm, String]()
    var clause = cc

    def newConstantTerm(name : String, s : Sort) = {
      val const = s newConstant name
      symMap = symMap + (const -> name)
      const
    }

    if (ContainsSymbol(clause, (x:IExpression) => x match {
          case IFunApp(f, _) => !(TheoryRegistry lookupSymbol f).isDefined
          case _ => false
        }))
      throw new Exception ("Uninterpreted functions are not supported")

    clause =
      if (elimArrays) {
        // need full preprocessing, in particular to introduce triggers
        val (List(INamedPart(_, processedClause_aux)), _, _) =
          Preprocessing(clause,
                        List(),
                        signature,
                        Param.TRIGGER_STRATEGY.set(
                          PreprocessingSettings.DEFAULT,
                          Param.TriggerStrategyOptions.AllMaximal))
        processedClause_aux
      } else {
        EquivExpander(PartialEvaluator(clause))
      }

//    println
//    println(clause)
    // transformation to prenex normal form
    clause = Transform2Prenex(Transform2NNF(clause), Set(Quantifier.ALL))

    var sorts  = List[Sort]()

    while (clause.isInstanceOf[IQuantified]) {
      val ISortedQuantified(Quantifier.ALL, sort, d) = clause
      clause = d
      sorts = sort :: sorts
    }

    val groundClause =
      if (!sorts.isEmpty) {
        val parameterConsts =
          for (s <- sorts)
          yield IConstant((newConstantTerm("P" + symMap.size, s)))
        subst(clause, parameterConsts, 0)
      } else {
        clause
      }

//    println
//    println(groundClause)
    
    // transform to CNF and try to generate one clause per conjunct
    for (conjunctRaw <- cnf_if_needed(groundClause);
         conjunct <- elimQuansTheories(conjunctRaw,
                                       unintPredicates,
                                       signature.theories,
                                       elimArrays)) yield {

      for (c <- SymbolCollector constantsSorted conjunct;
           if (!(symMap contains c)))
        symMap = symMap + (c -> c.name)

      var head : RelVar = null
      var body = List[HornLiteral]()

      var litsTodo = LineariseVisitor(conjunct, IBinJunctor.Or).toList

      def translateAtom(a : IAtom) : RelVar = {
        val IAtom(pred, args) = a
        val argSorts = SortedPredicate.iArgumentSorts(pred, args)
        val newArgs =
          (for ((t, tSort) <-
                   args.iterator zip argSorts.iterator) yield t match {
            case IConstant(c) =>
              Parameter(c.name, PrincessWrapper.sort2Type(tSort))
            case t => {
              val newC = newConstantTerm("T" + symMap.size, tSort)
              litsTodo = (newC =/= t) :: litsTodo
              Parameter(newC.name, PrincessWrapper.sort2Type(tSort))
            }
          }).toList
        RelVar(pred.name, newArgs)
      }
      
      import Sort.:::

      while (!litsTodo.isEmpty) {
        val lit = litsTodo.head
        litsTodo = litsTodo.tail

        lit match {
          case INot(a@IAtom(p, _)) if (TheoryRegistry lookupSymbol p).isEmpty =>
            body = translateAtom(a) :: body
          case a@IAtom(p, _) if (TheoryRegistry lookupSymbol p).isEmpty => {
            if (head != null)
              throw new Exception (
                "Multiple positive literals in a clause: " +
                head + ", " + translateAtom(a))
            head = translateAtom(a)
          }

          case INot(a@IAtom(p, _)) if !((TheoryRegistry lookupSymbol p).isEmpty) => 
            body = Interp(PrincessWrapper.formula2Eldarica(a, symMap, false)) :: body

          case a@IAtom(p, _) if !(TheoryRegistry lookupSymbol p).isEmpty =>
            body = Interp(PrincessWrapper.formula2Eldarica(~a, symMap, false)) :: body

          case INot(GeqZ(IConstant(_) :::
                           ModuloArithmetic.UnsignedBVSort(_)) |
                    Geq(IIntLit(_),
                        IConstant(_) ::: ModuloArithmetic.UnsignedBVSort(_))) =>
            // inequality introduced by the parser that can be ignored
          
          case l => {
            body = Interp(PrincessWrapper.formula2Eldarica(~l, symMap, false)) :: body
          }          
        }
      }

//      val res =
      HornClause(if (head == null) Interp(lazabs.ast.ASTree.BoolConst(false))
                 else head,
                 if (body.isEmpty) List(Interp(lazabs.ast.ASTree.BoolConst(true))) 
                 else body)
//      println(" -> " + res)
//      res
    }
  }

  val result : Seq[HornClause] = eldClauses.flatten match {
    case Seq() => {
      // make sure to generate at least one clause
      List(HornClause(Interp(lazabs.ast.ASTree.BoolConst(false)),
                      List(Interp(lazabs.ast.ASTree.BoolConst(false)))))
    }
    case s => s
  }

  //////////////////////////////////////////////////////////////////////////////

  private class VarTypeInferrer(varNum : Int)
                extends ContextAwareVisitor[Unit, Unit] {
    val types = new Array[Sort](varNum)
    override def preVisit(t : IExpression,
                          ctxt : Context[Unit]) : PreVisitResult = {
      t match {
        case IAtom(pred, args) => {
          val argSorts = SortedPredicate.iArgumentSorts(pred, args)
          for ((IVariable(ind), sort) <- args.iterator zip argSorts.iterator)
            if (ind >= ctxt.binders.size)
              types(ind - ctxt.binders.size) = sort
        }
        case IFunApp(pred, args) => {
          val argSorts = SortedIFunction.iArgumentSorts(pred, args)
          for ((IVariable(ind), sort) <- args.iterator zip argSorts.iterator)
            if (ind >= ctxt.binders.size)
              types(ind - ctxt.binders.size) = sort
        }
        case _ =>
          // nothing
      }
      super.preVisit(t, ctxt)
    }
    def postVisit(t : IExpression,
                  arg : Context[Unit], subres : Seq[Unit]) : Unit = ()
  }

  //////////////////////////////////////////////////////////////////////////////

  private def elimQuansTheories(
                clause : IFormula,
                unintPredicates : LinkedHashSet[Predicate],
                allTheories : Seq[Theory],
                elimArrays : Boolean) : Seq[IFormula] = {

    val containsArraySymbol =
      ContainsSymbol(clause, (e : IExpression) => e match {
        case IFunApp(f, _) => (TheoryRegistry lookupSymbol f) match {
          case Some(_ : SimpleArray | _ : ExtArray) => true
          case _ => false
        }
        case IAtom(p, _) => (TheoryRegistry lookupSymbol p) match {
          case Some(_ : SimpleArray | _ : ExtArray) => true
          case _ => false
        }
        case _ => false
      })

    val quanNum = QuantifierCountVisitor(clause)

    if (quanNum == 0 && !(containsArraySymbol && elimArrays))
      return List(clause)

    if (containsArraySymbol || PredUnderQuantifierVisitor(clause))
      lazabs.GlobalParameters.get.didIncompleteTransformation = true

    import p._

    addTheories(allTheories)

    def additionalAxioms(instantiatedPreds : Set[Predicate]) : Conjunction = {
      val formula =
        or(for (literal@IQuantified(Quantifier.EX, _) <-
                  LineariseVisitor(clause, IBinJunctor.Or).iterator;
                if (ContainsSymbol(literal, (x:IExpression) => x match {
                      case IAtom(p, _) => (unintPredicates contains p) &&
                                          !(instantiatedPreds contains p)
                      case _ => false
                    })))
           yield {
               var quanNum = 0
               var formula : IFormula = literal
               while (formula.isInstanceOf[IQuantified]) {
                 val IQuantified(Quantifier.EX, h) = formula
                 quanNum = quanNum + 1
                 formula = h
               }

               val newMatrix =
                 or(for (h <- LineariseVisitor(formula, IBinJunctor.And).iterator)
                    yield h match {
                      case s@IAtom(p, _) => {
                        (TheoryRegistry lookupSymbol p) match {
                          case Some(t) if (t.functionalPredicates contains p) =>
                            // nothing
                          case _ =>
                            throw new Exception(
                              "Unexpected quantified clause literal: " + literal)
                        }
                        ~s
                      }
                      case s => s
                    })

               quan(for (_ <- 0 until quanNum) yield Quantifier.ALL, newMatrix)
             })
      asConjunction(formula)
    }

    val qfClauses = scope {
      val qfClauses = new ArrayBuffer[Conjunction]

      addRelations(unintPredicates)
      addConstantsRaw(SymbolCollector constantsSorted clause)

      // first eliminate quantifiers by instantiation

      setupTheoryPlugin(new Plugin {
        import Plugin.GoalState
        override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
          goalState(goal) match {
            case GoalState.Final => {
              val occurringPreds =
                (for (a <- goal.facts.predConj.positiveLits.iterator)
                 yield a.pred).toSet

              // check whether all quantified literals have been instantiated
              val axioms = additionalAxioms(occurringPreds)

              if (axioms.isFalse) {
                qfClauses += goal.facts
                List(Plugin.AddFormula(Conjunction.TRUE))
              } else {
                List(Plugin.AddFormula(axioms))
              }
            }
            case _ =>
              List()
          }
      })

      ?? (clause)
      checkSat(false)
      while (getStatus(100) == ProverStatus.Running)
        lazabs.GlobalParameters.get.timeoutChecker()

      qfClauses
    }

    // then eliminate theory symbols
    val resClauses = new ArrayBuffer[IFormula]

    for (c <- qfClauses) scope {
      lazabs.GlobalParameters.get.timeoutChecker()

      setMostGeneralConstraints(true)

      addConstantsRaw(c.order sort c.order.orderedConstants)

      val (unintBodyLits, theoryBodyLits) =
        c.predConj.positiveLits partition (unintPredicates contains _.pred)
      val (unintHeadLits, theoryHeadLits) =
        c.predConj.negativeLits partition (unintPredicates contains _.pred)

      if (unintHeadLits.size > 1)
        throw new Exception (
          "Multiple positive literals in a clause: " +
          (unintHeadLits mkString ", "))

      addAssertion(
        c.updatePredConj(
          c.predConj.updateLits(theoryBodyLits,
                                theoryHeadLits)(c.order))(c.order))

      // Create new existential constants for the arguments of the
      // individual atoms
      def existentialiseAtom(a : Atom) : IAtom = {
        val existConsts = createExistentialConstants(a.size)

        implicit val _ = order
        import TerForConvenience._

        addAssertion(a === (for (IConstant(c) <- existConsts) yield c))

        IAtom(a.pred, existConsts)
      }

      val newUnintHeadLits = unintHeadLits map (existentialiseAtom _)
      val newUnintBodyLits = unintBodyLits map (existentialiseAtom _)

      checkSat(false)
      while (getStatus(100) == ProverStatus.Running)
        lazabs.GlobalParameters.get.timeoutChecker()

      resClauses += (??? match {
        case ProverStatus.Unsat =>
          Transform2NNF(getMinimisedConstraint |||
                        ~and(newUnintBodyLits) |||
                        or(newUnintHeadLits))
        case ProverStatus.Sat | ProverStatus.Inconclusive =>
          // then the resulting constraint is false
          Transform2NNF(~and(newUnintBodyLits) |||
                        or(newUnintHeadLits))
      })
    }

    reset

    resClauses
  }
}
