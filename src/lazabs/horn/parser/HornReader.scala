/**
 * Copyright (c) 2011-2014 Hossein Hojjat, Filip Konecny, Philipp Ruemmer.
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
import ap.parser._
import ap.theories.{Theory, TheoryRegistry, TheoryCollector}
import ap.{SimpleAPI, Signature}
import SimpleAPI.ProverStatus
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.terfor.{TerForConvenience, TermOrder}
import lazabs.prover.PrincessWrapper
import lazabs.ast.ASTree.Parameter
import lazabs.types.IntegerType
import ap.parameters.{ParserSettings, PreprocessingSettings, Param}

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer,
                                 HashSet => MHashSet, LinkedHashSet}

object HornReader {
  def apply(fileName: String): Seq[HornClause] = {
    val in: InputStream = new FileInputStream(fileName)
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
}

////////////////////////////////////////////////////////////////////////////////

class SMTHornReader protected[parser] (
         fileName: String,
         // we need a prover for some of the
         // clause preprocessing, in general
         p : SimpleAPI) {

  import IExpression._

  private val reader = new java.io.BufferedReader (
                 new java.io.FileReader(new java.io.File (fileName)))
  private val settings = Param.BOOLEAN_FUNCTIONS_AS_PREDICATES.set(
                   ParserSettings.DEFAULT, true)
  private val (f, _, signature) = SMTParser2InputAbsy(settings)(reader)
  reader.close
  private val clauses = LineariseVisitor(Transform2NNF(!f), IBinJunctor.And)
  
  private val triggerFunctions =
    (for (t <- signature.theories.iterator;
          f <- t.triggerRelevantFunctions.iterator)
     yield f).toSet

  private val unintPredicates = new LinkedHashSet[Predicate]

  for (p <- signature.order.orderedPredicates.toSeq.sortBy(_.name))
    if (!(TheoryRegistry lookupSymbol p).isDefined)
      unintPredicates += p

  if (!signature.theories.isEmpty)
    Console.err.println("Theories: " + (signature.theories mkString ", "))

  private val eldClauses = for (cc <- clauses) yield {
    var parameterConsts = List[ITerm]()
    var symMap = Map[ConstantTerm, String]()
    var clause = cc

    def newConstantTerm(name : String) = {
      val const = new ConstantTerm (name)
      symMap = symMap + (const -> name)
      const
    }

    if (ContainsSymbol(clause, (x:IExpression) => x match {
          case IFunApp(f, _) => !(TheoryRegistry lookupSymbol f).isDefined
          case _ => false
        }))
      throw new Exception ("Uninterpreted functions are not supported")
    
    // preprocessing: e.g., encode functions as predicates
    val (List(INamedPart(_, processedClause_aux)), _, sig2) =
      Preprocessing(clause,
                    List(),
                    signature,
                    Param.TRIGGER_STRATEGY.set(
                    Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(
                      PreprocessingSettings.DEFAULT,
                      triggerFunctions),
                      Param.TriggerStrategyOptions.AllMaximal))
    clause = processedClause_aux
    
    // transformation to prenex normal form
    clause = Transform2Prenex(Transform2NNF(clause), Set(Quantifier.ALL))

    while (clause.isInstanceOf[IQuantified]) {
      val IQuantified(Quantifier.ALL, d) = clause
      clause = d
      parameterConsts = newConstantTerm("P" + symMap.size) :: parameterConsts
    }

    val groundClause = subst(clause, parameterConsts, 0)
    
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
        val newArgs = (for (t <- args.iterator) yield t match {
          case IConstant(c) =>
            Parameter(c.name, IntegerType())
          case t => {
            val newC = newConstantTerm("T" + symMap.size)
            litsTodo = (t =/= newC) :: litsTodo
            Parameter(newC.name, IntegerType())
          }
        }).toList
        RelVar(pred.name, newArgs)
      }

      while (!litsTodo.isEmpty) {
        val lit = litsTodo.head
        litsTodo = litsTodo.tail
        lit match {
          case INot(a : IAtom) =>
            body = translateAtom(a) :: body
          case a : IAtom => {
            //assert(head == null)
            if (head != null) {
              System.err.println(conjunct)
              throw new Exception ("Negated uninterpreted predicates in the body of a clause are not supported.")
            }
            head = translateAtom(a)
          }
          case f =>
            body = Interp(PrincessWrapper.formula2Eldarica(~f, symMap, false)) :: body
        }
      }

      HornClause(if (head == null) Interp(lazabs.ast.ASTree.BoolConst(false))
                 else head,
                 if (body.isEmpty) List(Interp(lazabs.ast.ASTree.BoolConst(true))) 
                 else body)
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

  private def elimQuansTheories(
                clause : IFormula,
                unintPredicates : LinkedHashSet[Predicate],
                allTheories : Seq[Theory]) : Seq[IFormula] = {

    val quanNum = QuantifierCountVisitor(clause)

    if (quanNum == 0 && allTheories.isEmpty)
      return List(clause)

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

      addAssertion(
        c.updatePredConj(
          c.predConj.updateLits(theoryBodyLits,
                                theoryHeadLits)(c.order))(c.order))

      assert(unintHeadLits.size <= 1)

      def existentialiseAtom(a : Atom) : IAtom = {
        val existConsts = createExistentialConstants(a.size)

        implicit val _ = order
        import TerForConvenience._

        addAssertion(a === (for (IConstant(c) <- existConsts) yield c))

        IAtom(a.pred, existConsts)
      }

      val newUnintHeadLits = unintHeadLits map (existentialiseAtom _)
      val newUnintBodyLits = unintBodyLits map (existentialiseAtom _)

      resClauses += (??? match {
        case ProverStatus.Unsat =>
          Transform2NNF(getMinimisedConstraint ||| ~and(newUnintBodyLits) ||| or(newUnintHeadLits))
        case ProverStatus.Sat =>
          // then the resulting constraint is false
          Transform2NNF(~and(newUnintBodyLits) ||| or(newUnintHeadLits))
      })
    }

    reset

    resClauses
  }
}
