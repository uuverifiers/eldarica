package lazabs.horn.graphs

import ap.SimpleAPI
import ap.parser.{IAtom, IConstant, IFormula, ITerm, SymbolCollector}
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.preprocessor.ConstraintSimplifier
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}

import scala.collection.mutable.HashSet

object GraphUtils {
  val cs = new ConstraintSimplifier

  def normalizeClauses(clauses: Clauses, templates: VerificationHints): Clauses = {
    val uniqueClauses = distinctByString(clauses)
    val (csSimplifiedClauses, _, _) = cs.process(uniqueClauses.distinct, templates)
    val constraintSimplifiedClauses= for (c<-csSimplifiedClauses) yield simplifyConstraint(c)
    val normalizedClauses = for (c <- constraintSimplifiedClauses) yield c.normalize()
    val bodyReplacedClauses = (for ((c, i) <- normalizedClauses.zipWithIndex) yield replaceMultiSamePredicateInBody(c, i)).flatten // replace multiple same predicate in body
    val finalNormalizedClauses = for (c <- bodyReplacedClauses) yield replaceIntersectArgumentInBody(c)
    finalNormalizedClauses
  }
  def simplifyClauses(clauses: Clauses, templates: VerificationHints): Unit ={
    val uniqueClauses = distinctByString(clauses)
    val (csSimplifiedClauses, _, _) = cs.process(uniqueClauses.distinct, templates)
    val constraintSimplifiedClauses = for (c <- csSimplifiedClauses) yield simplifyConstraint(c)
    constraintSimplifiedClauses
  }

  def distinctByString[A](formulas: Seq[A]): Seq[A] = {
    val FormulaStrings = new HashSet[String]
    val uniqueFormulas = formulas filter { f => FormulaStrings.add(f.toString) } //de-duplicate formulas
    uniqueFormulas
  }


  def replaceMultiSamePredicateInBody(clause: Clause, clauseIndex: Int): Clauses = {
    //if head == body: p(x)<-p(a) => p(x)<-p'(a), p'(a)<-p(a)
    //if multiple same relation symbos in the body: p(x)<-p'(a),p'(b)=> p(x)<-p'(a),p''(b), p''(b)<-p'(b)
    var originalBodyPredicatesList: List[IAtom] = List()
    var renamedBodyPredicatesList: List[IAtom] = List()
    val pbodyStrings = new HashSet[String]
    pbodyStrings.add(clause.head.pred.name)
    var count = 1
    val renamedClauseBodys = for (b <- clause.body) yield {
      if (!pbodyStrings.add(b.pred.name)) { //if there is repeatative body name
        val newPredicateName = b.pred.name + "_" + clauseIndex.toString + "_" + count.toString

        //val renamedBodyPredicate=IAtom(new Predicate(newPredicateName,b.pred.arity),b.args)
        val monosortedPredicate = MonoSortedPredicate(newPredicateName, predArgumentSorts(b.pred))
        val renamedBodyPredicate = IAtom(monosortedPredicate, b.args)

        renamedBodyPredicatesList = renamedBodyPredicatesList :+ renamedBodyPredicate
        originalBodyPredicatesList = originalBodyPredicatesList :+ b
        count = count + 1
        renamedBodyPredicate
      } else {
        b
      }
    }

    val supplementaryClauses = for ((rb, ob) <- renamedBodyPredicatesList zip originalBodyPredicatesList) yield {
      Clause(rb, List(ob), true)
    }
    Seq(Clause(clause.head, renamedClauseBodys, clause.constraint)) ++ supplementaryClauses
  }

  def replaceIntersectArgumentInBody(clause: Clause): Clause = {
    var f: IFormula = clause.constraint

    def replaceArgumentInBody(body: IAtom): IAtom = {
      var argList: Seq[ITerm] = Seq()
      for ((arg, s) <- body.args zip predArgumentSorts(body.pred)) {
        if ((for (a <- clause.head.args) yield a.toString).contains(arg.toString)) {
          //val ic = IConstant(newConstant(arg.toString + "__"))
          val ic = IConstant(new SortedConstantTerm((arg.toString + "__"), s))
          //replace argument
          argList :+= ic
          //add equation in constrains
          f = f &&& (arg === ic)
        } else
          argList :+= arg
      }
      //val monosortedPredicate = MonoSortedPredicate(body.pred.name, predArgumentSorts(body.pred))
      IAtom(body.pred, argList)
    }

    Clause(IAtom(clause.head.pred, clause.head.args),
      for (body <- clause.body) yield replaceArgumentInBody(body),
      f)
  }

  def simplifyConstraint(clause: Clause): Clause = {
    val simplifyedConstraints = clauseConstraintQuantify(clause)
    Clause(clause.head, clause.body, simplifyedConstraints)
  }

  def clauseConstraintQuantify(clause: Clause): IFormula = {
    //println(Console.BLUE + "clauseConstraintQuantify begin")
    SimpleAPI.withProver { p =>
      p.scope {
        p.addConstantsRaw(clause.constants.toSeq.sortBy(_.toString()))
        val constants = for (a <- clause.allAtoms; c <- SymbolCollector.constants(a)) yield c
        try {
          p.withTimeout(5 * 1000) {
            p.projectEx(clause.constraint, constants)
          }
        }
        catch {
          case SimpleAPI.TimeoutException => clause.constraint
          case _ => clause.constraint
        }
      }
    }
  }

}

