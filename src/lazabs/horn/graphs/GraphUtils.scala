package lazabs.horn.graphs

import ap.SimpleAPI
import ap.parser.{IAtom, IConstant, IFormula, ITerm, SymbolCollector}
import ap.terfor.ConstantTerm
import ap.terfor.preds.Predicate
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.bottomup.HornPredAbs.predArgumentSorts
import lazabs.horn.preprocessor.ConstraintSimplifier
import lazabs.horn.preprocessor.HornPreprocessor.{Clauses, VerificationHints}

import java.io.PrintWriter
import scala.collection.mutable
import scala.collection.mutable.HashSet

object GraphUtils {
  val cs = new ConstraintSimplifier


  def unifyClauseElements(clauses: Clauses): Clauses = {
    var uniqueIntegerIdentifier = 0

    def constructNewName(name: String): String = {
      val newName = uniqueIntegerIdentifier.toString + ":" + name
      uniqueIntegerIdentifier += 1
      newName
    }


    for (c <- clauses) yield {
      //rename head
      val newHeadPredName = constructNewName(c.head.pred.name)
      val newHeadPred = new Predicate(newHeadPredName, c.head.args.length)

      val newHeadArgs = for (a <- c.head.args) yield {
        IConstant(new ConstantTerm(constructNewName(a.toString)))
      }
      //todo should rename constraint

      val newHead = IAtom(newHeadPred, newHeadArgs)


      Clause(newHead, c.body, c.constraint)
    }

  }


  def normalizeClauses(clauses: Clauses, templates: VerificationHints): (Clauses,Seq[Clauses]) = {
    val normalizedClauses = simplifyClauses(clauses,templates)
    val bodyReplacedClauses = (for ((c, i) <- normalizedClauses.zipWithIndex) yield replaceMultiSamePredicateInBody(c, i)) // replace multiple same predicate in body
    val flattenBodyReplacedClauses=bodyReplacedClauses.flatten
    val argumentReplacedClauses = for (c <- flattenBodyReplacedClauses) yield replaceIntersectArgumentInBody(c)
    (argumentReplacedClauses,bodyReplacedClauses)
  }

  def simplifyClauses(clauses: Clauses, templates: VerificationHints): Clauses = {
    //val uniqueClauses = distinctByString(clauses)
    val (csSimplifiedClauses, _, _) = cs.process(clauses, templates)
    val constraintSimplifiedClauses = for (c <- csSimplifiedClauses) yield simplifyConstraint(c)
    val normalizedClauses = for (c <- constraintSimplifiedClauses) yield c.normalize()
    normalizedClauses
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

  def printCurrentNodeMap(nodeMap: Map[Int, Node], nodeTypeList: Seq[String] = NodeAndEdgeType.nodeTypes): Unit = {
    println("-" * 10 + "node list" + "-" * 10)
    for (n <- nodeMap.values; if nodeTypeList.contains(n.typeName))
      println(n.nodeID, n.typeName, n.readName, n.rsName, n.argumentIndex)
    println("-" * 10)
  }


  def getCanonicalName(nodeType: String, canonicalID: Int): String = {
    nodeType + "_" + canonicalID.toString
  }

  def getAbbrevCanonicalName(nodeType: String, canonicalID: Int): String = {
    NodeAndEdgeType.nodeTypesAbbrev(nodeType) + "_" + canonicalID.toString
  }

  def getNodeAttributeMap(updateMap: Map[String, String], elementTypes: Seq[String], defaultAttribute: String): Map[String, String] = {
    (for (n <- elementTypes) yield {
      if (updateMap.keys.toSeq.contains(n))
        n -> updateMap(n)
      else
        n -> defaultAttribute
    }).toMap
  }

  def rgb(a: Int, b: Int, c: Int): String = {
    "\"" + "#" + a.toHexString.toUpperCase + b.toHexString.toUpperCase + c.toHexString.toUpperCase + "\""
  }

  def seqToString(s: String): String = {
    if (s.contains("("))
      "[" + s.substring(s.indexOf("(") + 1, s.indexOf(")")) + "]"
    else
      s
  }

  def graphFileNameMap(hgt: HornGraphType.Value): String = hgt match {
    case HornGraphType.CDHG => "hyperEdgeGraph"
    case HornGraphType.CG => "monoDirectionLayerGraph"
  }


}

