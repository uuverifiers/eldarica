package lazabs.horn.preprocessor

import ap.api.SimpleAPI
import ap.parser._
import ap.parser.IExpression.{ConstantTerm, Eq, Predicate, and, i, toFunApplier, toPredApplier}
import ap.terfor.conjunctions.Quantifier
import ap.theories.Heap.{HeapFunExtractor, HeapPredExtractor}
import ap.theories.{ADT, Heap}
import ap.types._
import lazabs.horn.Util.{DagEmpty, DagNode}
import lazabs.horn.abstractions.VerificationHints.VerifHintInitPred
import lazabs.horn.bottomup.HornClauses.Clause
import lazabs.horn.preprocessor.HornPreprocessor.{BackTranslator, Clauses, CounterExample, Solution, VerificationHints}

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

class HeapUpdateSitesTagSetAnalysis extends HornPreprocessor {
  override val name : String = "heap TagSet analysis"

  private val predBackMapping = new MHashMap[Predicate, Predicate]
  private val intermediateClauseBackMapping = new MHashMap[Clause, Clause]
  private val clauseBackMapping = new MHashMap[Clause, Clause]

  /**
   * Only applicable when the input CHCs contain heap theories.
   */
  override def isApplicable(clauses          : Clauses,
                            frozenPredicates : Set[Predicate]) : Boolean = {
    clauses.flatMap(c => c.theories).toSet.exists(_.isInstanceOf[Heap])
  }

  override def process(clauses          : Clauses,
                       hints            : VerificationHints,
                       frozenPredicates : Set[Predicate]) : (Clauses,
    VerificationHints, HornPreprocessor.BackTranslator) = {
    val heaps : Set[Heap] =
      clauses.flatMap(c => c.theories).collect{case h : Heap => h}.toSet

    /** 1) Create a tuple sort to rewrite the heap sort within the CHCs. */
    val heapToHeapTuple : Map[Heap, ADT] = (for (heap <- heaps) yield {
      val heapName = heap.HeapSort.name
      val tupleName = s"${heapName}Tuple"
      val ctorSignatures : Seq[(String, ADT.CtorSignature)] = Seq(
        tupleName -> ADT.CtorSignature(
          arguments = Seq(
            s"h$heapName" -> ADT.OtherSort(heap.HeapSort),
            s"lastTag$heapName" -> ADT.OtherSort(Sort.Integer),
            s"pg$heapName" -> ADT.OtherSort(heap.AddressSort)
          ),
          result = ADT.ADTSort(0)
        )
      )
      heap -> new ADT(Seq(tupleName), ctorSignatures)
    }).toMap

    /** 2) Rewrite all clauses to clauses where every heap term is rewritten to
     *     a heap-tuple term. This rewriting also redeclares non-theory
     *     predicates.
     */
    val oldUnintPreds = clauses.flatMap(_.predicates)

    val oldToNewSortMap : Map[Sort, Sort] = heapToHeapTuple.flatMap{
      case (heap, tuple) => Map(
        heap.HeapSort -> tuple.sorts.head)
    }

    for (oldPred <- oldUnintPreds) {
      val newPred = oldPred match {
        case sortedPred : MonoSortedPredicate =>
          val newSorts : Seq[Sort] =
            for (oldSort <- sortedPred.argSorts) yield
              oldToNewSortMap get oldSort match {
                case Some(newSort) => newSort
                case None => oldSort
              }
          if (newSorts.diff(sortedPred.argSorts) nonEmpty)
            new MonoSortedPredicate(oldPred.name, newSorts)
          else oldPred
        case _ => oldPred
      }
      predBackMapping += newPred -> oldPred
    }

    val oldToNewPredMap = Map() ++ predBackMapping.map(_.swap)
    val clausesWithHeapToTuple = for (clause <- clauses) yield {
      val newClause =
        (new SortRewriter(oldToNewPredMap, oldToNewSortMap, clause)).res
      intermediateClauseBackMapping += newClause -> clause
      newClause
    }

    /** 3) Apply the rewrite rules over all clauses. */
    var tagSetPredCounter = 0
    for (clause <- clausesWithHeapToTuple) {
      val conjuncts = LineariseVisitor(Transform2NNF(
        new ValidAtomRewriter(heapToHeapTuple).visit(clause.constraint, ())
          .asInstanceOf[IFormula]), IBinJunctor.And)
      val newConjuncts = new ArrayBuffer[IFormula]
      val additionalBodyAtoms = new ArrayBuffer[IAtom]
      val tagSetAssertions = new ArrayBuffer[(Clause, Boolean)]
      for (conjunct <- conjuncts) conjunct match {
        /** emptyHeap() = t */
        case Eq(IFunApp(f@HeapFunExtractor(hp), _), t) if f == hp.emptyHeap =>
          val tupleCtor = heapToHeapTuple(hp).constructors.head
          val pg = IConstant(new SortedConstantTerm("pg", hp.AddressSort))
          newConjuncts += t === tupleCtor(hp.emptyHeap(), -1, pg)

        /** write(t1, a, TaggedObject(o, i)) = t2 */
        case Eq(IFunApp(f@HeapFunExtractor(hp),
               Seq(t1, a, tagO@IFunApp(_, Seq(o, i)))), t2) if f == hp.write =>
          val tupleCtor  = heapToHeapTuple(hp).constructors.head
          val getHeap    = heapToHeapTuple(hp).selectors(0)(0)
          val getLastTag = heapToHeapTuple(hp).selectors(0)(1)
          val getPg      = heapToHeapTuple(hp).selectors(0)(2)
          val newTag     = IConstant(new ConstantTerm("newTag"))
          newConjuncts +=
            t2 === tupleCtor(hp.write(getHeap(t1), a, tagO), newTag, getPg(t1))
//          newConjuncts +=
//            (getPg(t1) =/= a ||| newTag === i) &&&
//              (getPg(t1) === a ||| newTag === getLastTag(t1))
          newConjuncts += newTag === IExpression.ite(getPg(t1) === a, i, getLastTag(t1))

        /** allocHeap(t1, TaggedObject(o, i)) = t2 */
        case Eq(IFunApp(f@HeapFunExtractor(hp),
                        Seq(t1, tagO@IFunApp(_, Seq(o, i)))), t2) if f == hp.allocHeap =>
          val tupleCtor  = heapToHeapTuple(hp).constructors.head
          val getHeap    = heapToHeapTuple(hp).selectors(0)(0)
          val getLastTag = heapToHeapTuple(hp).selectors(0)(1)
          val getPg      = heapToHeapTuple(hp).selectors(0)(2)
          val a = hp.allocAddr(getHeap(t1), tagO)
          val newTag = IConstant(new ConstantTerm("newTag"))
          newConjuncts +=
            t2 === tupleCtor(hp.allocHeap(getHeap(t1), tagO), newTag, getPg(t1))
//          newConjuncts +=
//            (getPg(t1) =/= a ||| newTag === i) &&& // a = pg ==> tag = i
//              (getPg(t1) === a ||| newTag === getLastTag(t1)) // a != pg ==> tag = lastTag
          newConjuncts += newTag === IExpression.ite(getPg(t1) === a, i, getLastTag(t1))

        /** allocAddr(t, TaggedObject(o, i)) = a */
        case Eq(IFunApp(f@HeapFunExtractor(hp),
                        Seq(t, tagO@IFunApp(_, Seq(o, i)))), a) if f == hp.allocAddr =>
          val getHeap = heapToHeapTuple(hp).selectors(0)(0)
          newConjuncts += hp.allocAddr(getHeap(t), tagO) === a

        /** counter(t) = c --> counter(h) = c */
        case Eq(IFunApp(f@HeapFunExtractor(hp), Seq(t)), c) if f == hp.counter =>
          val getHeap = heapToHeapTuple(hp).selectors(0)(0)
          newConjuncts += hp.counter(getHeap(t)) === c

        /** ex tag. read(t, a) = TaggedObject(o, tag) */
        case IQuantified(Quantifier.EX,
                         Eq(IFunApp(fun@HeapFunExtractor(hp), Seq(t, a)),
                            IFunApp(taggedObjCtor, Seq(o, IVariable(0)))))
          if fun == hp.read =>
          /** Create a new TagSet predicate and assert it if pg == a */
          val tagSetPred = new Predicate(s"TagSet$tagSetPredCounter", 1)
          tagSetPredCounter += 1
          val getHeap    = heapToHeapTuple(hp).selectors(0)(0)
          val getLastTag = heapToHeapTuple(hp).selectors(0)(1)
          val getPg      = heapToHeapTuple(hp).selectors(0)(2)
          val oldLastTag = IConstant(new ConstantTerm("oldLastTag"))
          val (tagSetAssertionConjunct, needsFullConstraint) =
            if (clause.body.flatMap(_.args) contains t) {
              (getPg(t) === a &&& getLastTag(t) === oldLastTag, false)
            } else {
              (getPg(t) === a, true)
            }
          // note that these assertion clauses are incomplete, they are
          // completed after the conjuncts are fully rewritten
          tagSetAssertions +=
            ((Clause(tagSetPred(oldLastTag), clause.body, tagSetAssertionConjunct), needsFullConstraint))
          val tagC = new ConstantTerm("tag")
          additionalBodyAtoms += tagSetPred(tagC)
          newConjuncts += hp.read(getHeap(t), a) === taggedObjCtor(o, tagC)

        case Eq(IFunApp(f@HeapFunExtractor(hp), _), _) if f == hp.nullAddr =>
          newConjuncts += conjunct

        case IAtom(f@HeapPredExtractor(hp), _) if f == hp.isAlloc =>
          newConjuncts += conjunct

        case INot(IAtom(f@HeapPredExtractor(hp), _)) if f == hp.isAlloc =>
          newConjuncts += conjunct

        case Eq(IFunApp(f@HeapFunExtractor(hp), _), _) =>
          assert(false, "Unhandled " + SimpleAPI.pp(conjunct))

        case IAtom(HeapPredExtractor(hp), _) =>
          assert(false, "Unhandled " + SimpleAPI.pp(conjunct))

        case _ => newConjuncts += conjunct
      }

      val newConstraint = IExpression.and(newConjuncts)
      val newClause = Clause(clause.head,
                             clause.body ++ additionalBodyAtoms, newConstraint)
      clauseBackMapping += newClause -> clause
      for ((Clause(head, body, c), needsFullConstraint) <- tagSetAssertions) {
        clauseBackMapping += Clause(head, body, c &&&
          (if(needsFullConstraint) newConstraint else i(true))
                                    ) -> clause
      }
    }

    /**
     * Update the hints to use the new predicates.
     * todo: Do we need to update formulas when hints are [[VerifHintInitPred]]?
     */
    val newHints = hints.renamePredicates(oldToNewPredMap)

    val backTranslator = new BackTranslator {
      override def translate(solution : Solution) : Solution =
        for((pred, sol) <- solution) yield predBackMapping(pred) -> sol

      override def translate(cex : CounterExample) : CounterExample =
        translateCEX(cex).collapseNodes

      val sortBackMapping = oldToNewSortMap.map(_.swap)
      private def translateCEX(dag : CounterExample) : CounterExample =
        dag match {
          case DagNode((a, clause), children, next) =>
//            val newPred = predBackMapping(a.pred)
//            val newArgs = a.args // todo: update args with the new sorts
            assert(clauseBackMapping contains clause)
            DagNode((a, //todo: update a with IAtom(newPred, newArgs),
                      clauseBackMapping(clause)), children, translateCEX(next))
          case DagEmpty => DagEmpty
        }
    }

    (clauseBackMapping.keys.toSeq, newHints, backTranslator)
  }
}

class SortRewriter(oldToNewPredMap   : Map[Predicate, Predicate],
                   oldToNewSortMap   : Map[Sort, Sort],
                   clause            : Clause)
  extends CollectingVisitor[Unit, IExpression] {

  assert(clause.predicates.forall(oldToNewPredMap contains))

  private val oldNewTermMap : Map[ConstantTerm, ConstantTerm] =
    clause.constantsSorted.map{
      case c : SortedConstantTerm if oldToNewSortMap contains c.sort =>
        c -> new SortedConstantTerm(c.name, oldToNewSortMap(c.sort))
      case c => c -> c
    }.toMap

  override def postVisit(t : IExpression, arg : Unit,
                         subres : Seq[IExpression]) : IExpression = {
    t match {
      /** Rewrite constant terms */
      case IConstant(SortedConstantTerm(c, _)) =>
        assert(oldNewTermMap contains c)
        IConstant(oldNewTermMap(c))

      /** Rewrite uninterpreted predicates */
      case IAtom(pred, _) if oldToNewPredMap contains pred =>
        IAtom(oldToNewPredMap(pred), subres.map(_.asInstanceOf[ITerm]))

      /** Do not rewrite anything else */
      case _ => t update subres
    }
  }

  val res = {
    val newConstraint = visit(clause.constraint, ()).asInstanceOf[IFormula]
    val newHead       = visit(clause.head, ()).asInstanceOf[IAtom]
    val newBody       = clause.body.map(a => visit(a, ()).asInstanceOf[IAtom])
    Clause(newHead, newBody, newConstraint)
  }
}

class ValidAtomRewriter(heapToHeapTuple : Map[Heap, ADT])
  extends CollectingVisitor[Unit, IExpression] {
  override def postVisit(t      : IExpression, arg : Unit,
                         subres : Seq[IExpression]) : IExpression = {
    t match {
      /** valid(t,a) */
      case IAtom(p@HeapPredExtractor(hp), Seq(t, a)) if p == hp.isAlloc =>
        val getHeap = heapToHeapTuple(hp).selectors(0)(0)
        hp.isAlloc(getHeap(subres(0).asInstanceOf[ITerm]),
                           subres(1).asInstanceOf[ITerm])
      case _ => t update subres
    }
  }
}