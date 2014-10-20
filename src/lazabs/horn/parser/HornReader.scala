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
import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer}
import ap.parser._
import ap.theories.{Theory, TheoryRegistry, TheoryCollector}
import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.terfor.TerForConvenience

object HornReader {
  def apply(fileName: String): Seq[HornClause] = {
    val in: InputStream = new FileInputStream(fileName)
    val lexer = new HornLexer(in)
    val parser = new Parser(lexer)
    val tree = parser.parse()
    (scala.collection.JavaConversions.asScalaBuffer(tree.value.asInstanceOf[java.util.List[HornClause]]))
  }

//  def fromSMT(fileName: String): Seq[HornClause] = {
//    import ap.parameters.{ParserSettings, PreprocessingSettings, Param}
//    import ap.parser._
//    import ap.terfor.TermOrder
//    import ap.Signature
//    import IExpression._
//    import lazabs.prover.PrincessWrapper
//    import lazabs.ast.ASTree.Parameter
//    import lazabs.types.IntegerType
//    
//    import lazabs.prover.PrincessAPI_v1
//    val api = new PrincessAPI_v1
//
//    val reader = new java.io.BufferedReader (
//                   new java.io.FileReader(new java.io.File (fileName)))
//    val settings = Param.BOOLEAN_FUNCTIONS_AS_PREDICATES.set(
//                     ParserSettings.DEFAULT, true)
//    val (f, _, signature) = SMTParser2InputAbsy(settings)(reader)
//    val clauses = LineariseVisitor(Transform2NNF(!f), IBinJunctor.And)
//
//    val eldClauses = for (c <- clauses) yield {
//      val allConsts = new ArrayBuffer[ConstantTerm]
//      var parameterConsts = List[ITerm]()
//      var symMap = Map[ConstantTerm, String]()
//      var clause = c
//
//      def newConstantTerm(name : String) = {
//        val const = new ConstantTerm (name)
//        allConsts += const
//        symMap = symMap + (const -> name)
//        const
//      }
//
//      while (clause.isInstanceOf[IQuantified]) {
//        val IQuantified(Quantifier.ALL, d) = clause
//        clause = d
//        parameterConsts = newConstantTerm("P" + symMap.size) :: parameterConsts
//	/      }
//      
//
//      val groundClause = subst(clause, parameterConsts, 0)
//
//      if (ContainsSymbol(groundClause, (x:IExpression) => x match {
//        case _ : IFunApp => true
//        case _ => false
//      }))
//        throw new Exception ("Uninterpreted functions are not supported")
//
//      // preprocessing: e.g., encode functions as predicates
//      val (List(INamedPart(_, processedClause)), _, _) =
//        Preprocessing(groundClause,
//                      List(),
//                      signature,
//                      PreprocessingSettings.DEFAULT)
//
//      var head : RelVar = null
//
//      val aux = LineariseVisitor(processedClause, IBinJunctor.Or).toList
//      
//      var (l1,l2) = aux.partition(_ match { 
//        case _ : IAtom => true
//        case _ => false
//        })
//      assert(l1.size <= 1)
//
//      def translateAtom(a : IAtom) : (RelVar,IFormula) = {
//        val IAtom(pred, args) = a
//        var f : IFormula = IBoolLit(true)
//        val newArgs = (for (t <- args.iterator) yield t match {
//          case IConstant(c) =>
//            Parameter(c.name, IntegerType())
//          case t => {
//            val newC = newConstantTerm("T" + symMap.size)
//            f = f & (t === newC)
//            Parameter(newC.name, IntegerType())
//          }
//        }).toList
//        (RelVar(pred.name, newArgs),f)
//      }
//      
//      if (l1.size == 1) {
//        val List(h) = l1
//        val (aux1,aux2) = translateAtom(h.asInstanceOf[IAtom])
//        head = aux1
//        l2 = !aux2 :: l2
//      }
//      
//      // \/ litsTodo \/ head
//      // !(\/ litsTodo) => head
//      // d1 \/ .. \/ dn => head  // apply DNF
//      // (d1 => head) /\ ... /\ (dn => head)
//      
//      val fbody = !l2.foldLeft[IFormula](IBoolLit(false))(_|_)
//      //val symbols = (SymbolCollector constants (fbody)).toSeq
//      //val fdnf = api.dnfSimplify(fbody, symbols)
//      //var disjuncts = LineariseVisitor(fdnf, IBinJunctor.Or).toList
//      var disjuncts = ddnf(nnf(fbody))
//      
//      
//      for (disj <- disjuncts) yield {
//        var conjuncts = LineariseVisitor(disj, IBinJunctor.And).toList
//        var body = List[HornLiteral]()
//        while (!conjuncts.isEmpty) {
//          val conjunct = conjuncts.head
//          conjuncts = conjuncts.tail
//          conjunct match {
//            case INot(a : IAtom) =>
//              assert(false)
//            case a : IAtom => {
//              val (aux1,aux2) = translateAtom(a)
//              conjuncts = aux2 :: conjuncts;
//              body = aux1 :: body
//            }
//            case f =>
//              body = Interp(PrincessWrapper.formula2Eldarica(f, symMap, false)) :: body
//          }
//        }
//        HornClause(if (head == null)
//                   Interp(lazabs.ast.ASTree.BoolConst(false))
//                 else
//                   head, body)
//      }
//    }
//
//    eldClauses.flatten
//  }
  
  def fromSMT(fileName: String): Seq[HornClause] = {
    import ap.parameters.{ParserSettings, PreprocessingSettings, Param}
    //import ap.parser._
    import ap.terfor.TermOrder
    import ap.Signature
    import IExpression._
    import lazabs.prover.PrincessWrapper
    import lazabs.ast.ASTree.Parameter
    import lazabs.types.IntegerType

    val reader = new java.io.BufferedReader (
                   new java.io.FileReader(new java.io.File (fileName)))
    val settings = Param.BOOLEAN_FUNCTIONS_AS_PREDICATES.set(
                     ParserSettings.DEFAULT, true)
    val (f, _, signature) = SMTParser2InputAbsy(settings)(reader)
    val clauses = LineariseVisitor(Transform2NNF(!f), IBinJunctor.And)
    
    val triggerFunctions =
      (for (t <- signature.theories.iterator;
            f <- t.triggerRelevantFunctions.iterator)
       yield f).toSet

    val unintPredicates =
      for (p <- signature.order.orderedPredicates.toSeq.sortBy(_.name);
           if (!(TheoryRegistry lookupSymbol p).isDefined))
      yield p

    if (!signature.theories.isEmpty)
      Console.err.println("Theories: " + (signature.theories mkString ", "))

    val eldClauses = for (cc <- clauses) yield {
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
                      Param.TRIGGER_GENERATOR_CONSIDERED_FUNCTIONS.set(
                        PreprocessingSettings.DEFAULT,
                        triggerFunctions))
      clause = processedClause_aux
      
      // transformation to prenex normal form
      clause = Transform2Prenex(Transform2NNF(clause), Set(Quantifier.ALL))

      while (clause.isInstanceOf[IQuantified]) {
        val IQuantified(Quantifier.ALL, d) = clause
        clause = d
        parameterConsts = newConstantTerm("P" + symMap.size) :: parameterConsts
      }

      val groundClause = subst(clause, parameterConsts, 0)
      
      def isLiteral(aF : IFormula) = {
        !containsPredicate(aF) || (aF match {
          case IAtom(_,_) => true
          case INot(IAtom(_,_)) => true
          case _ => false
        })
      }
      def cnf_if_needed(aF : IFormula) : List[IFormula] = {
        val conjuncts = LineariseVisitor(aF, IBinJunctor.And)
        if (conjuncts.forall(
            LineariseVisitor(_, IBinJunctor.Or).forall(
                isLiteral(_)
                )
            )) {
          conjuncts.toList
        } else {
          ccnf(aF)
        }
      }
      
      // transform to CNF and try to generate one clause per conjunct
      
      for (conjunctRaw <- cnf_if_needed(groundClause);
           conjunctRaw2 <- elimQuansTheories(conjunctRaw,
                                             unintPredicates,
                                             signature.theories);
           conjunct <- cnf_if_needed(conjunctRaw2)) yield {

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
                   else body )
      }
    }

    eldClauses.flatten
  }

  //////////////////////////////////////////////////////////////////////////////

  def elimEqv(aF : ap.parser.IFormula) : ap.parser.IFormula = {
    aF match {
      case f@IBinFormula(IBinJunctor.Eqv,f1,f2) =>
        val ff1 = elimEqv(f1)
        val ff2 = elimEqv(f2)
        IBinFormula(IBinJunctor.And,
        		IBinFormula(IBinJunctor.Or,INot(ff1),ff2),
        		IBinFormula(IBinJunctor.Or,INot(ff2),ff1))
      case f => f
    }
  }
  def nnf(aF : ap.parser.IFormula, b : Boolean) : ap.parser.IFormula = {
    aF match {
      case INot(f) => 
        nnf(f,!b)
      case IQuantified(q,f) => 
        val qq = if (!b) q else q.dual
        IQuantified(qq,nnf(f,b))
      case IBinFormula(j,f1,f2) =>
        j match {
          case IBinJunctor.And =>
            val jj = if (!b) IBinJunctor.And else IBinJunctor.Or
            IBinFormula(jj,nnf(f1,b),nnf(f2,b))
          case IBinJunctor.Or =>
            val jj = if (!b) IBinJunctor.Or else IBinJunctor.And
            IBinFormula(jj,nnf(f1,b),nnf(f2,b))
          case IBinJunctor.Eqv =>
            assert(false)
            IBoolLit(true)
        }
      case f : IAtom => if (!b) f else INot(f)
      case f : IBoolLit => if (!b) f else INot(f)
      case f : IIntFormula => if (!b) f else INot(f)
      case _ =>
        assert(false)
        IBoolLit(true)
    }
  }
  // negation normal form
  def nnf(aF : ap.parser.IFormula) : ap.parser.IFormula = {
    val f_noEqv = elimEqv(aF)
    nnf(f_noEqv,false)
  }   

  def dnf_base(dnf1 : List[ap.parser.IFormula], dnf2 : List[ap.parser.IFormula]) = {
    var dnf : List[ap.parser.IFormula] = List()
    for (f1 <- dnf1) {
      for (f2 <- dnf2) {
        dnf = (f1 &&& f2) :: dnf
      }
    }
    dnf
  }
  def cnf_base(cnf1 : List[ap.parser.IFormula], cnf2 : List[ap.parser.IFormula]) = {
    var cnf : List[ap.parser.IFormula] = List()
    for (f1 <- cnf1) {
      for (f2 <- cnf2) {
        cnf = (f1 ||| f2) :: cnf
      }
    }
    cnf
  }
  // disjunctive normal form (quantified subformulas are considered as atoms)
  def ddnf(aF : ap.parser.IFormula) : List[ap.parser.IFormula] = {
    var dnf : List[IFormula] = Nil
    aF match {
      case IBinFormula(j,f1,f2) =>
        val dnf1 = ddnf(f1)
        val dnf2 = ddnf(f2)
        j match {
          case IBinJunctor.And =>
            dnf = dnf_base(dnf1,dnf2)
          case IBinJunctor.Or =>
            dnf = dnf1 ::: dnf2
          case IBinJunctor.Eqv =>
            assert(false)
        }
      case f@INot(IAtom(_,_)) => dnf = f :: Nil
      case f@INot(IBoolLit(_)) => dnf = f :: Nil
      case f@INot(IIntFormula(_,_)) => dnf = f :: Nil
      case f : IAtom => dnf = f :: Nil
      case f : IBoolLit => dnf = f :: Nil
      case f : IIntFormula => dnf = f :: Nil
      case f : IQuantified => dnf = f :: Nil
      case _ =>
        assert(false)
    }
    dnf
  }
  // conjunctive normal form (quantified subformulas are considered as atoms)
  def ccnf(aF : ap.parser.IFormula) : List[ap.parser.IFormula] = {
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
  def containsPredicate(aF : IFormula) : Boolean = {
    aF match {
        case IQuantified(q,f) => containsPredicate(f)
        case IBinFormula(j,f1,f2) => containsPredicate(f1) || containsPredicate(f2)
        case INot(f) => containsPredicate(f)
        case a : IAtom => true
        case _ =>false
    }
  }
  def quantifiers(aF : IFormula) : List[ap.terfor.conjunctions.Quantifier] = {
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
  def cnt_quantif(aF : IFormula) : Int = {
      quantifiers(aF).length
  }
  // prenex normal form
  // aF -- a formula formed only by atoms, quantifiers, not, and, or, eqv
  def pnf(aF : ap.parser.IFormula) : ap.parser.IFormula = {
    val f_nnf = nnf(aF)
    var x = cnt_quantif(f_nnf)
    // quantifier prefix of PNF
    var q_prefix = List[IExpression.Quantifier]()
    // aInx -- de Bruijn index
    def remove_quant(aF : IFormula, aInx : Int) : IFormula = {
      aF match {
        case IQuantified(q,f) =>
          val ff = remove_quant(f,aInx+1)
          q_prefix = q :: q_prefix
          x = x-1
          // _aInx becomes _x
          // for each i in 0..(aInx-1), _i stays _i
          var ll = List[IVariable]()
          ll = IExpression.v(x) :: ll
          for (i <- aInx-1 to 0 by -1) {
            ll = IExpression.v(i) :: ll
          }
          val aux = VariableSubstVisitor(ff,(ll,0))
          aux
        case IBinFormula(j,f1,f2) =>
          val ff1 = remove_quant(f1,aInx)
          val ff2 = remove_quant(f2,aInx)
          IBinFormula(j,ff1,ff2)
        case INot(f) =>
          val ff = remove_quant(f,aInx)
          INot(ff)
        case f => f
      }
    }
    // new de Bruijn indices: 0,1,...,x-1
    // renaming of variables in post-order traversal, starting with x-1
    var f_pnf = remove_quant(f_nnf,0)    
    // add the quantifier prefix
    // quantifiers (q1,q2,...) in q_prefix have de Bruijn indices (0,1,...) 
    for (q <- q_prefix.reverse) {
      f_pnf = IQuantified(q,f_pnf)
    }
    f_pnf
  }

  //////////////////////////////////////////////////////////////////////////////

  private def elimQuansTheories(
                f : IFormula,
                unintPredicates : Seq[IExpression.Predicate],
                allTheories : Seq[Theory]) : Seq[IFormula] = {

    if (QuantifierCountVisitor(f) == 0 && allTheories.isEmpty)
      return List(f)

    SimpleAPI.withProver(enableAssert = lazabs.Main.assertions) { p =>
      import p._

      addTheories(allTheories)

      // first eliminate quantifiers by instantiation
      val qfClauses = new ArrayBuffer[Conjunction]

      scope {
        setupTheoryPlugin(new Plugin {
          import Plugin.GoalState
          def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] =
            goalState(goal) match {
              case GoalState.Final => {
                qfClauses += goal.facts
                Some((Conjunction.FALSE, Conjunction.TRUE))
              }
              case _ =>
                None
            }
        })

        addRelations(unintPredicates)
        addConstantsRaw(SymbolCollector constantsSorted f)
        ?? (f)
        ???
      }

      // then eliminate theory symbols
      val resClauses = new ArrayBuffer[IFormula]

      for (c <- qfClauses) scope {
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

          for ((lc, IConstant(c)) <- a.iterator zip existConsts.iterator)
            addAssertion(lc === c)
          IAtom(a.pred, existConsts)
        }

        val newUnintHeadLits = unintHeadLits map (existentialiseAtom _)
        val newUnintBodyLits = unintBodyLits map (existentialiseAtom _)

        import IExpression._

        val r = ???
        assert(r == ProverStatus.Unsat)

        // turn the resulting formula into CNF
        for (g <- LineariseVisitor(CNFSimplifier(getConstraint),
                                   IBinJunctor.And))
          resClauses += g ||| ~and(newUnintBodyLits) ||| or(newUnintHeadLits)
      }

      resClauses
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private object CNFSimplifier extends Simplifier {
    import IExpression._

    override protected def furtherSimplifications(expr : IExpression) =
      expr match {
        case IBinFormula(IBinJunctor.Or, f,
                         IBinFormula(IBinJunctor.And, g1, g2)) =>
          (f | g1) & (f | g2)
        case IBinFormula(IBinJunctor.Or,
                         IBinFormula(IBinJunctor.And, g1, g2),
                         f) =>
          (g1 | f) & (g2 | f)
        case expr => expr
      }
  }
}
