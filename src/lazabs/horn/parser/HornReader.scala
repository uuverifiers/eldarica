/**
 * Copyright (c) 2011-2019 Hossein Hojjat, Filip Konecny, Philipp Ruemmer.
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

import java.io.{FileInputStream,InputStream,FileNotFoundException}

import lazabs.horn.global._
import lazabs.prover.PrincessWrapper
import lazabs.ast.ASTree._
import lazabs.types.IntegerType
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts

import ap.parser._
import ap.theories.{Theory, TheoryRegistry, TheoryCollector, ADT, SimpleArray,
                    MulTheory, ModuloArithmetic}
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
  def apply(fileName: String): Seq[HornClause] = {
    val in = new java.io.BufferedReader (
                 new java.io.FileReader(fileName))
    val lexer = new HornLexer(in)
    val parser = new Parser(lexer)
    val tree = parser.parse()
    (scala.collection.JavaConversions.asScalaBuffer(
       tree.value.asInstanceOf[java.util.List[HornClause]]))
  }

  def fromSMT(fileName: String) : Seq[HornClause] =
    SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>
      (new SMTHornReader(fileName, p)).result
    }

  //////////////////////////////////////////////////////////////////////////////

  def cnf_if_needed(aF : IFormula) : List[IFormula] = {
    val conjuncts = LineariseVisitor(aF, IBinJunctor.And)
    if (conjuncts.forall(
          LineariseVisitor(_, IBinJunctor.Or).forall(isLiteral(_))
        )) {
      conjuncts.toList
    } else {
      ccnf(aF)
    }
  }

  // conjunctive normal form (quantified subformulas are considered as atoms)
  private def ccnf(aF : ap.parser.IFormula) : List[ap.parser.IFormula] = {
    var cnf : List[IFormula] = Nil
    aF match {
      case IBinFormula(j,f1,f2) =>
        val cnf1 = ccnf(f1)
        val cnf2 = ccnf(f2)
        j match {
          case IBinJunctor.And =>
            cnf = cnf1 ::: cnf2
          case IBinJunctor.Or =>
            cnf = cnf_base(cnf1,cnf2)
          case IBinJunctor.Eqv =>
            assert(false)
        }
      case f@INot(IAtom(_,_)) => cnf = f :: Nil
      case f@INot(IBoolLit(_)) => cnf = f :: Nil
      case f@INot(IIntFormula(_,_)) => cnf = f :: Nil
      case f : IAtom => cnf = f :: Nil
      case f : IBoolLit => cnf = f :: Nil
      case f : IIntFormula => cnf = f :: Nil
      case f : IQuantified => cnf = f :: Nil
      case _ => 
        assert(false)
    }
    cnf
  }

  private def dnf_base(dnf1 : List[ap.parser.IFormula], dnf2 : List[ap.parser.IFormula]) = {
    var dnf : List[ap.parser.IFormula] = List()
    for (f1 <- dnf1) {
      for (f2 <- dnf2) {
        dnf = (f1 &&& f2) :: dnf
      }
    }
    dnf
  }

  private def cnf_base(cnf1 : List[ap.parser.IFormula], cnf2 : List[ap.parser.IFormula]) = {
    var cnf : List[ap.parser.IFormula] = List()
    for (f1 <- cnf1) {
      for (f2 <- cnf2) {
        cnf = (f1 ||| f2) :: cnf
      }
    }
    cnf
  }

  private def containsPredicate(aF : IFormula) : Boolean = {
    aF match {
        case IQuantified(q,f) => containsPredicate(f)
        case IBinFormula(j,f1,f2) => containsPredicate(f1) || containsPredicate(f2)
        case INot(f) => containsPredicate(f)
        case a : IAtom => true
        case _ =>false
    }
  }

  private def isLiteral(aF : IFormula) = {
    !containsPredicate(aF) || (aF match {
      case IAtom(_,_) => true
      case INot(IAtom(_,_)) => true
      case _ => false
    })
  }

  private def quantifiers(aF : IFormula) : List[ap.terfor.conjunctions.Quantifier] = {
      aF match {
        case IQuantified(q,f) =>
          q :: quantifiers(f)
        case IBinFormula(j,f1,f2) =>
          quantifiers(f1) ::: quantifiers(f2)
        case INot(f) =>
          quantifiers(f)
        case _ => Nil
      }
  }

  private def cnt_quantif(aF : IFormula) : Int = {
      quantifiers(aF).length
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
      case _ : IAtom if (!arg.binders.isEmpty) => throw FoundPredUnderQuantifier
      case _ => super.preVisit(t, arg)
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
      case _ : IAtom
        if ctxt.polarity < 0 && (ctxt.binders contains Context.EX)  =>
          throw FoundPredUnderQuantifier
      case _ =>
        super.preVisit(t, ctxt)
    }
   
    def postVisit(t : IExpression,
                  arg : Context[Unit],
                  subres : Seq[Unit]) : Unit = ()
  }
}

////////////////////////////////////////////////////////////////////////////////

class SMTHornReader protected[parser] (
         fileName: String,
         // we need a prover for some of the
         // clause preprocessing, in general
         p : SimpleAPI) {

  import IExpression._
  import HornReader.{cnf_if_needed, PredUnderQuantifierVisitor,
                     QuantifiedBodyPredsVisitor}

  private val reader = new java.io.BufferedReader (
                 new java.io.FileReader(new java.io.File (fileName)))
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
                    case SimpleArray.ArraySort(_) =>
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

  val clauses = LineariseVisitor(Transform2NNF(!f), IBinJunctor.And)

  if (!signature.theories.isEmpty)
    Console.err.println("Theories: " + (signature.theories mkString ", "))

  private val eldClauses = for (cc <- clauses) yield {
    var parameterConsts = List[ITerm]()
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

    signature.theories match {
      case theories if (theories forall {
                          case _ : ADT          => true
                          case _ : MulTheory    => true
                          case TypeTheory       => true
                          case ModuloArithmetic => true
                          case _                => false
                        }) =>
        // ok
      case theories if (theories forall {
                          case _ : SimpleArray => true
                          case TypeTheory      => true
                          case _               => false
                        }) => {
        // ok
      }
      case _ =>
        throw new Exception ("Combination of theories is not supported")
    }

    clause =
      if (QuantifiedBodyPredsVisitor(clause)) {
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

    var varNum = 0

    while (clause.isInstanceOf[IQuantified]) {
      val IQuantified(Quantifier.ALL, d) = clause
      clause = d
      varNum = varNum + 1
    }

    val groundClause =
      if (varNum > 0) {
        val inferrer = new VarTypeInferrer(varNum)
        inferrer.visitWithoutResult(clause, Context(()))
        for (s <- inferrer.types.reverseIterator) {
          parameterConsts =
            newConstantTerm("P" + symMap.size,
                            if (s == null) Sort.Integer else s) ::
              parameterConsts
        }
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
                                       signature.theories)) yield {

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
                allTheories : Seq[Theory]) : Seq[IFormula] = {

    val containsArraySymbol =
      ContainsSymbol(clause, (e : IExpression) => e match {
        case IFunApp(f, _) => (TheoryRegistry lookupSymbol f) match {
          case Some(_ : SimpleArray) => true
          case _ => false
        }
        case IAtom(p, _) => (TheoryRegistry lookupSymbol p) match {
          case Some(_ : SimpleArray) => true
          case _ => false
        }
        case _ => false
      })

    val quanNum = QuantifierCountVisitor(clause)

    if (quanNum == 0 &&
        !(containsArraySymbol &&
          lazabs.GlobalParameters.get.arrayQuantification.isDefined))
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
        def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] =
          goalState(goal) match {
            case GoalState.Final => {
              val occurringPreds =
                (for (a <- goal.facts.predConj.positiveLits.iterator)
                 yield a.pred).toSet

              // check whether all quantified literals have been instantiated
              val axioms = additionalAxioms(occurringPreds)

              if (axioms.isFalse) {
                qfClauses += goal.facts
                Some((Conjunction.FALSE, Conjunction.TRUE))
              } else {
                Some((axioms.negate, Conjunction.TRUE))
              }
            }
            case _ =>
              None
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
