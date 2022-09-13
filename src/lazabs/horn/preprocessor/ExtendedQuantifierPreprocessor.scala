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
import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}

object ExtendedQuantifierPreprocessor {
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
    override def isApplicable(clauses: Clauses): Boolean =
      clauses.flatMap(c => c.theories).exists(t =>
        t.isInstanceOf[ExtendedQuantifier])

    /**
     * Transformer method
     */
    def process(clauses: Clauses, hints: VerificationHints)
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
      val arrToFunHashmap = new MHashMap[String, ExtendedQuantifier]() //Keep track of what kind of extended quantifier used for each array
      for (clause@HornClauses.Clause(head, body, constraint) <- clauses) yield {
        val extQuantifierApps = ExtQuantifierFunctionApplicationCollector(constraint)
        for (IFunApp(f, Seq(a, _, _)) <- extQuantifierApps) {
          f match {
            case ExtendedQuantifier.ExtendedQuantifierFun(exq) =>
              arrToFunHashmap += (a.toString() -> exq)
            case _ => //nothing
          }
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
              case c@Eq(IFunApp(ExtArray.Select(arrayTheory), Seq(a:ITerm, i)), o) =>
                val exq = arrToFunHashmap.get(a.toString()) match {
                  case Some(e:ExtendedQuantifier) => e
                  case _ => ??? //TODO: if no theory found then I guess no instrumentation needed?
                }
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
                      (hres === exq.redOp(bres, o)) & (hlo === i) & hhi === bhi, // todo: use  actual fun from theory
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
              case c@Eq(IFunApp(ExtArray.Store(arrayTheory), Seq(a1, i, o)), a2) =>
                val exq = arrToFunHashmap.get(a1.toString()) match {
                  case Some(e:ExtendedQuantifier) => e
                  case _ => ??? //TODO: if no theory found then I guess no instrumentation needed?
                }
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
                      (hres === exq.redOp(bres, o)) & (hlo === i) & hhi === bhi, // todo: use  actual fun from theory
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

    override def setup(clauses: Clauses): Unit = {
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
