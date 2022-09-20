/**
 * Copyright (c) 2022 Jesper Amilon, Zafer Esen, Philipp Ruemmer.
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

package lazabs.horn.preprocessor

import ap.parser._
import ap.theories.ExtArray
import ap.types.{MonoSortedPredicate, SortedConstantTerm}
import lazabs.horn.bottomup.HornClauses
import lazabs.horn.bottomup.HornClauses.Clause
import IExpression._
import lazabs.horn.preprocessor.AbstractAnalyser.{AbstractDomain, AbstractTransformer}

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}

object ExtendedQuantifierPreprocessor {
  object RelatedArrayTermsAndExtendedQuantifiersDomain extends AbstractDomain {
    val name = "related array terms and extended quantifier theories"

    // This abstract domain tries to infer the extended quantifier theories for
    // (array) terms appearing in a clause (Left[ITerm]) and
    // (predicate - predicate argument index) pairs (Left(Predicate, Int)).
    // Since each term might be associated with multiple extended quantifiers,
    // a set of theories is returned.
    type Element =
      Option[Seq[(Set[Either[ITerm, (Predicate, Int)]], Set[ExtendedQuantifier])]]

    def bottom(p : Predicate) : Element = None
    def isBottom(b : Element) : Boolean = b.isEmpty

    // join merges the sets of an element if the intersection of their terms
    // is not empty.
    def join(a : Element, b : Element) : Element =
      a match {
        case None => b
        case Some(aArgs) => b match {
          case None => a
          case Some(bArgs) =>
            val mergedArgs: Set[(Set[Either[ITerm, (Predicate, Int)]], Set[ExtendedQuantifier])] =
              (for ((aTerms, aTheories) <- aArgs) yield {
                (for((bTerms, bTheories) <- bArgs) yield {
                  if ((aTerms intersect bTerms).nonEmpty) {
                    Seq((aTerms union bTerms, aTheories union bTheories))
                  } else {
                    aArgs ++ bArgs
                  }
                }).flatten
              }).flatten.toSet

            // mergedArgs might contain elements with same terms, merge them too
            var changed = true
            val toBeDropped =
              new MHashSet[(Set[Either[ITerm, (Predicate, Int)]],
                Set[ExtendedQuantifier])]
            val toBeAdded =
              new MHashSet[(Set[Either[ITerm, (Predicate, Int)]],
                Set[ExtendedQuantifier])]
            while(changed) {
              changed = false
              for (Seq(merged1@(aTerms, aTheories),
                    merged2@(bTerms, bTheories)) <-
                     mergedArgs.toSeq.combinations(2)) {
                if ((aTerms intersect bTerms).nonEmpty) {
                  toBeDropped += merged1
                  toBeDropped += merged2
                  changed = toBeAdded.add(
                    ((aTerms union bTerms, aTheories union bTheories)))
                } else {
                  // nothing needed
                }
              }
            }
            Some((toBeAdded.toSet ++
              (mergedArgs diff toBeDropped.toSet)).toSeq)
        }
      }

    def transformerFor(clause : Clause) = new AbstractTransformer[Element] {
      val Clause(head, body, constraint) = clause

      def transform(bodyVals : Seq[Element]) : Element =
        if (bodyVals exists (_.isEmpty)) {
          None
        } else {
          val conjuncts : Seq[IFormula] =
            LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)

          // first we join the elements coming from the body elements
          val elemFromBody : Element =
            bodyVals.reduceOption((a, b) => join(a, b)).getOrElse(None)

          // the elements we merged in the previous step will not contain the
          // local terms of this clause, those we obtain by iterating over all
          // (Predicate, Int) pairs, and adding terms at those indices
          // from literals with those predicates.
          val elemFromBodyInThisClause : Element = {
            elemFromBody match {
              case Some(elem) =>
                val newTermsAndTheories =
                  for ((terms, theories : Set[ExtendedQuantifier]) <- elem) yield {
                    val newTerms : Set[Either[ITerm, (Predicate, Int)]] =
                      (for (Right((pred, argInd)) <- terms) yield {
                        for (literal <- Seq(head) ++ body if literal.pred == pred)
                          yield Left(literal.args(argInd))
                      }).flatten
                    (newTerms, theories)
                  }
                join(Some(newTermsAndTheories), elemFromBody)
              case None =>
                elemFromBody
            }
          }

          // We also add any elements from the head literal.
          // Note that the head argument terms are added in the previous step,
          // so no need to do it here again.
          val elemFromHead : Element = {
            val termSets =
              for((a@IConstant(SortedConstantTerm(_, sort)), argInd) <-
                    head.args.zipWithIndex
                  if sort.isInstanceOf[ExtArray.ArraySort])
                yield Set(Left(a.asInstanceOf[ITerm]).
                  asInstanceOf[Either[ITerm, (Predicate, Int)]],
                  Right((head.pred, argInd)))
            Some(termSets.map(termSet => (termSet, Set[ExtendedQuantifier]())))
          }

          // collects a set of (Pred, Int) pairs if term appears as argument
          // to any predicate in the clause.
          def getPredArgsMatchingTerm(term : ITerm) :
          Set[Either[ITerm, (Predicate, Int)]] =
            (for(literal <- Seq(clause.head) ++ clause.body
                 if literal.args.contains(term)) yield {
              Right(literal.pred, literal.args.indexOf(term))
            }).toSet

          var newElement = join(elemFromHead, elemFromBodyInThisClause)
          var changed = true

          // this loop runs to fixed point inside a clause, applying the
          // abstract transformer.
          while(changed) {
            changed = false
            val oldElement = newElement
            for (conjunct <- conjuncts) conjunct match {
              case Eq(IFunApp(f@ExtArray.Store(_), Seq(a, _, _)), b) =>
                val termSet : Set[Either[ITerm, (Predicate, Int)]] =
                  Set(Left(a), Left(b))
                val theorySet : Set[ExtendedQuantifier] = Set()
                val predArgSet = getPredArgsMatchingTerm(a) ++
                  getPredArgsMatchingTerm(b)
                val conjunctElem : Element =
                  Some(Seq((termSet ++ predArgSet, theorySet)))
                newElement = join (newElement,
                  join (conjunctElem, elemFromBodyInThisClause))
              case Eq(IConstant(SortedConstantTerm(a, s1)),
              IConstant(SortedConstantTerm(b, s2)))
                if s1 == s2 && s1.isInstanceOf[ExtArray.ArraySort] =>
                val termSet : Set[Either[ITerm, (Predicate, Int)]] =
                  Set(Left(a), Left(b))
                val theorySet : Set[ExtendedQuantifier] = Set()
                val predArgSet =
                  getPredArgsMatchingTerm(a) ++ getPredArgsMatchingTerm(b)
                val conjunctElem : Element =
                  Some(Seq((termSet ++ predArgSet, theorySet)))
                newElement = join (newElement,
                  join (conjunctElem, elemFromBodyInThisClause))
              case Eq(IFunApp(f@ExtendedQuantifier.ExtendedQuantifierFun(exq),
                              Seq(a, _, _)), _) =>
                val termSet : Set[Either[ITerm, (Predicate, Int)]] =
                  Set(Left(a))
                val theorySet : Set[ExtendedQuantifier] = Set(exq)
                val predArgSet = getPredArgsMatchingTerm(a)
                val conjunctElem : Element =
                  Some(Seq((termSet ++ predArgSet, theorySet)))
                newElement = join (newElement,
                  join (conjunctElem, elemFromBodyInThisClause))
              case _ =>
              // nothing
            }
            changed = oldElement != newElement
          }
          newElement
        }
    }
  }

  /**
   * A Horn preprocessor that adds instrumentation code for extended quantifiers.
   */

  val funAppBackTranslation = new MHashMap[Predicate, Seq[IFormula]]

  class Instrumenter extends HornPreprocessor {

    val name: String = "Extended quantifier instrumenter"

    import HornPreprocessor._

    /**
     * Enabled for clauses that have extended quantifiers.
     */
    // todo: might need to be updated for recursive instrumentation.
    override def isApplicable(clauses: Clauses,
                              frozenPredicates : Set[Predicate]): Boolean =
      clauses.flatMap(c => c.theories).exists(t =>
        t.isInstanceOf[ExtendedQuantifier])

    /**
     * Transformer method
     */
    def process(clauses: Clauses, hints: VerificationHints,
                frozenPredicates : Set[Predicate])
    : (Clauses, VerificationHints, BackTranslator) = {
      // ghost variables should have been added by GhostVariableAdder at this point

      val clauseBackMapping = new MHashMap[Clause, Clause]

      // todo:
      //  1. Our instrumentation adds several new variables to a program P:
      //     int ar_lo, ar_hi, ar_max, ar_aggregate_res;
      // (this is done in GhostVariableAdder)

      // todo:
      //  2. We add initialization code in the beginning of the program:
      //     ar_lo = ar_hi = 0
      // (should be done here - todo!)

      // todo:
      //  3: We pick some subset of select and store equations in the program,
      //     and add the corresponding instrumentation code.
      // (done below)

      // todo:
      //  4: Pick some subset of assertions containing the aggregate operator,
      //     and rewrite them.

      /*FIRST PASS: Gather theory for each array*/

      val goalClausesWithHeadPred =
        for (HornClauses.Clause(_, body, constraint)
               <- clauses.filter(c => c.head.pred == HornClauses.FALSE))
          yield HornClauses.Clause(body.head, body, constraint)

      val predToRelatedTermsAndExtQuanTheories =
        new AbstractAnalyser(clauses ++ goalClausesWithHeadPred,
          RelatedArrayTermsAndExtendedQuantifiersDomain, Set()).result

      // Returns the extended quantifiers for a given term in a clause.
      // The term is either an ITerm, or a (Predicate, Int) pair.
      def getTheoriesForTerm(clause : HornClauses.Clause,
                             term : Either[ITerm, (Predicate, Int)]) :
      Set[ExtendedQuantifier] = {
        // Finds any predicate that is not FALSE and uses it.
        // This works because all predicates should have the same abstract
        // element at fixed point.
        val pred : Predicate =
          (Seq(clause.head) ++
            clause.body).filter(_.pred != HornClauses.FALSE).head.pred
        predToRelatedTermsAndExtQuanTheories(pred).getOrElse(Set()).find{
          case (terms, _) =>
            terms contains term
        } match {
          case Some((_, theories)) => theories
          case None => Set()
        }
      }

      val newClauses =
        for (clause@HornClauses.Clause(head, body, constraint) <- clauses) yield {
          var newHead = head

          val conjuncts =
            LineariseVisitor(Transform2NNF(constraint), IBinJunctor.And)

          // start from the whole constraint
          var newConstraint : IFormula = constraint

          // handle (4) - this will rewrite ext. quantifier applications
          val extQuantifierApps =
            ExtQuantifierFunctionApplicationCollector(constraint)


          if (extQuantifierApps.nonEmpty) {
            // rewrite this constraint
            for (app@IFunApp(f, Seq(a, lo, hi)) <- extQuantifierApps) {
              // todo: below code is experimental and will not work in most cases!
              val arrayInd = body.head.args.indexOf(a)
              val loInd = arrayInd + 1
              val hiInd = arrayInd + 2
              val resInd = arrayInd + 3
              val blo = body.head.args(loInd)
              val bhi = body.head.args(hiInd)
              val result = body.head.args(resInd)

              funAppBackTranslation += ((body.head.pred, funAppBackTranslation.
                getOrElse(body.head.pred, Nil) ++
                Seq(f(v(arrayInd), v(loInd), v(hiInd)) === v(resInd))))

              newConstraint = ExpressionReplacingVisitor(
                newConstraint,
                replaced = app,
                replaceWith =
                  ite(blo === lo & bhi === hi,
                    result,
                    IConstant(new SortedConstantTerm("unknownRes",
                      body.head.pred.asInstanceOf[MonoSortedPredicate].argSorts((arrayInd + 3)))))
              )
            }
          }
          // end of handling (4)

          var instrumented = false

          for (conjunct <- conjuncts) {
            conjunct match {
              // we can assume f(a, i) = o due to normalization of clauses
              // select(a, i) = o
              case c@Eq(IFunApp(ExtArray.Select(arrayTheory), Seq(a:ITerm, i)), o)
              if //getTheoriesForTerm(clause, Left(a)).nonEmpty &&
                head.pred.isInstanceOf[MonoSortedPredicate] &&
                body.forall(_.pred.isInstanceOf[MonoSortedPredicate]) => // todo: this is not a proper fix, but should prevent an exception for getting ghost vars in simple programs
                val exqs = getTheoriesForTerm(clause, Left(a))
                val exq : ExtendedQuantifier = exqs.head // todo: taking the first theory for now
                val ((blo, iblo), (bhi, ibhi), (bres, ibres)) = getGhostVarTriplet( // todo: fix
                  body.head.pred.asInstanceOf[MonoSortedPredicate], body.head.args).head
                val ((_, ihlo), (_, ihhi), (_, ihres)) = getGhostVarTriplet( // todo: fix
                  head.pred.asInstanceOf[MonoSortedPredicate], head.args).head
                val indexSort = arrayTheory.indexSorts.head
                val (hlo, hhi, hres) =
                  (IConstant(new SortedConstantTerm("lo'",indexSort)),
                    IConstant(new SortedConstantTerm("hi'",indexSort)),
                    IConstant(new SortedConstantTerm("res'",arrayTheory.objSort))
                  )
                val instConstraint =
                  ite(blo === bhi,
                    (hlo === i) & (hhi === i + 1) & (hres === o),
                    ite((blo - 1 === i),
                      (hres === exq.redOp(bres, o)) & (hlo === i) & hhi === bhi,
                      ite(bhi === i,
                        (hres === exq.redOp(bres, o)) & (hhi === i + 1 & hlo === blo),
                        ite(blo <= i & bhi > i,
                          hres === bres & hlo === blo & hhi === bhi, // no change within bounds
                          (hlo === i) & (hhi === i + 1) & (hres === o))))) // outside bounds, reset
                newConstraint = newConstraint &&& instConstraint
                val newHeadArgs : Seq[ITerm] =
                  for ((arg : ITerm, ind : Int) <- newHead.args.zipWithIndex) yield {
                    ind match {
                      case `ihlo`  => hlo
                      case `ihhi`  => hhi
                      case `ihres` => hres
                      case _ => arg
                    }
                  }
                newHead = IAtom(head.pred, newHeadArgs)
                // update head atom with new lo, hi and res
                instrumented = true

              // store(a1, i, o) = a2
              case c@Eq(IFunApp(ExtArray.Store(arrayTheory), Seq(a1, i, o)), a2)
                if //getTheoriesForTerm(clause, Left(a1)).nonEmpty &&
                  head.pred.isInstanceOf[MonoSortedPredicate] &&
                  body.forall(_.pred.isInstanceOf[MonoSortedPredicate]) => // todo: this is not a proper fix, but should prevent an exception for getting ghost vars
                val exqs = getTheoriesForTerm(clause, Left(a1))
                val exq : ExtendedQuantifier = exqs.head // todo: taking the first theory for now
                val ((blo, _), (bhi, _), (bres, _)) = getGhostVarTriplet( // todo: fix
                  body.head.pred.asInstanceOf[MonoSortedPredicate], body.head.args).head
                val ((_, ihlo), (_, ihhi), (_, ihres)) = getGhostVarTriplet( // todo: fix
                  head.pred.asInstanceOf[MonoSortedPredicate], head.args).head
                val indexSort = arrayTheory.indexSorts.head
                val (hlo, hhi, hres) =
                  (IConstant(new SortedConstantTerm("lo'",indexSort)),
                    IConstant(new SortedConstantTerm("hi'",indexSort)),
                    IConstant(new SortedConstantTerm("res'",arrayTheory.objSort))
                  )
                /*def ifInsideBounds_help(o:ITerm, o_prev:ITerm, res:ITerm) =
                  exq.invRedOp match {
                    case Some(f) => exq.redOp(f(res, o_prev), o)
                    case _ => ??? //TODO: Implement non-cancellative case
                  }*/
                val instConstraint =
                  ite(blo === bhi,
                    (hlo === i) & (hhi === i + 1) & (hres === o),
                    ite((blo - 1 === i),
                      (hres === exq.redOp(bres, o)) & (hlo === i) & hhi === bhi,
                      ite(bhi === i,
                        (hres === exq.redOp(bres, o)) & (hhi === i + 1 & hlo === blo),
                        ite(blo <= i & bhi > i,
                          exq.invRedOp match {
                            case Some(f) => hres === exq.redOp(f(bres, arrayTheory.select(a1, i)), o) & hlo === blo & hhi === bhi
                            case _ => (hlo === i) & (hhi === i + 1) & (hres === o)//??? //TODO: Implement non-cancellative case
                          },
                          //hres === ifInsideBounds_help(o, arrayTheory.select(a1, i), bres) & hlo === blo & hhi === bhi, //relate to prev val
                          (hlo === i) & (hhi === i + 1) & (hres === o))))) // outside bounds, reset
                newConstraint = newConstraint &&& instConstraint
                val newHeadArgs : Seq[ITerm] =
                  for ((arg : ITerm, ind : Int) <- newHead.args.zipWithIndex) yield {
                    ind match {
                      case `ihlo`  => hlo
                      case `ihhi`  => hhi
                      case `ihres` => hres
                      case _ => arg
                    }
                  }
                newHead = IAtom(head.pred, newHeadArgs)
                instrumented = true
//                // f : (a : array, lo : Int, hi : Int) => Obj
//                val newConjuncts =
//                  for ((f, theory) <- extQuantifierFuns zip extQuantifierTheories) yield {
//                  FunctionReplacingVisitor(conjunct, Map(
              case _ =>
              // we might need to match more cases
              // todo: we will need to add clauses too in some cases
            }
          }

          // handle (1)
          if (body.isEmpty && !instrumented) { // an entry clause

            for (((lo,_), (hi,_), (res,_)) <- getGhostVarTriplet(
              head.pred.asInstanceOf[MonoSortedPredicate], head.args))
              newConstraint = newConstraint &&& lo === 0 & hi === 0
          } else if (body.isEmpty && instrumented) {
            // if we have an entry clause like p(...) :- o = select/store(...)
            ???
          }

          // todo : handle (4)

          val newClause = Clause(newHead, body, newConstraint)
          clauseBackMapping.put(newClause, clause)

          newClause
        }

      val translator = new BackTranslator {
        def translate(solution : Solution) =
          solution.map{
            case (pred, formula) if funAppBackTranslation contains pred =>
              var newF = formula
              for (funApp <- funAppBackTranslation(pred))
                newF = formula & funApp
              (pred, newF)
            case other => other
          }

        def translate(cex : CounterExample) =
          for (p <- cex) yield (p._1, clauseBackMapping(p._2))
      }

      (newClauses, hints, translator)
    }

    // todo: refactor this, should not have side effects...
    private def getGhostVarTriplet (pred : MonoSortedPredicate,
                                     args : Seq[ITerm]) :
                                                  Seq[((ITerm, Int), (ITerm, Int), (ITerm, Int))] = {
      val headArrayInds =
        pred.argSorts.zipWithIndex.filter(
          sort => sort._1.isInstanceOf[ExtArray.ArraySort]).map(_._2)
      // todo: below code is very fragile, implement better way to extract (lo, hi, res)
      //  it works because the ghost vars are always added after the array term
      //  but some of them might get deleted during other preprocessing stages
      for (arrayInd <- headArrayInds) yield {
        val lo = arrayInd + 1
        val hi = arrayInd + 2
        val res = arrayInd + 3
        ((args(lo),lo), (args(hi),hi), (args(res),res))
      }
    }

    /**
     * Class for collecting the extended quantifier applications
     * occurring in an expression.
     */
    object ExtQuantifierFunctionApplicationCollector {
      def apply(t : IExpression) : scala.collection.Set[IFunApp] = {
        val apps = new MHashSet[IFunApp]
        val c = new ExtQuantifierFunctionApplicationCollector (apps)
        c.visitWithoutResult(t, 0)
        apps
      }
      def apply(ts : Iterable[IExpression]) : scala.collection.Set[IFunApp] = {
        val apps = new MHashSet[IFunApp]
        val c = new ExtQuantifierFunctionApplicationCollector (apps)
        for (t <- ts)
          c.visitWithoutResult(t, 0)
        apps
      }
    }
    class ExtQuantifierFunctionApplicationCollector(applications : scala.collection.mutable.Set[IFunApp])
      extends CollectingVisitor[Int, Unit] {
      def postVisit(t : IExpression, boundVars : Int, subres : Seq[Unit]) : Unit =
        t match {
          case app@IFunApp(ExtendedQuantifier.ExtendedQuantifierFun(_), _) =>
            applications += app
          case _ => // nothing
        }
    }

  }

  /**
   * Class to introduce ghost variables to predicates
   * todo: currently kept very simple, adds ghost variables to *every* predicate
   * todo: unused variables should be pruned away by other preprocessors
   */
  class GhostVariableAdder extends ArgumentExpander {

    import IExpression._
    import HornPreprocessor.Clauses

    val name = "ghost variable adder"

    val ghostVarsInPred = new MHashMap[Predicate, Seq[ConstantTerm]]

    def expand(pred: Predicate, argNum: Int, sort: Sort)
    : Option[(Seq[(ITerm, Sort, String)], Option[ITerm])] = {
      val arraySort = sort.asInstanceOf[ExtArray.ArraySort]
      import arraySort.theory._
      val indexSort = indexSorts.head
      val loName = argNum + "_lo"
      val hiName = argNum + "_hi"
      val resName = argNum + "_res"

      val ghostVars : Seq[(ITerm, Sort, String)] = Seq(
        (new SortedConstantTerm(loName, indexSort), indexSort, loName),
        (new SortedConstantTerm(hiName, indexSort), indexSort, hiName),
        (new SortedConstantTerm(resName, objSort), objSort, resName))

      ghostVarsInPred.put(pred, ghostVars.map(_._1.asInstanceOf[IConstant].c))

      Some(ghostVars, None)
    }

    override def setup(clauses: Clauses,
                       frozenPredicates : Set[Predicate]): Unit = {
      //    usedTheories.clear
      //    for (clause <- clauses)
      //      usedTheories ++= clause.theories
    }

    //  private val usedTheories = new MHashSet[Theory]

    // ghost variables will be added to predicates with array sorts
    override def isExpandableSort(s: Sort): Boolean =
      s.isInstanceOf[ExtArray.ArraySort]

    override def postprocessSolution(p : Predicate, f : IFormula) : IFormula = {
      ghostVarsInPred get p match {
        case Some(ghostVars) =>
          val quanF = quanConsts(IExpression.Quantifier.EX, ghostVars, f)
          (new Simplifier) (quanF)
        case None => f
      }
    }
  }
}
