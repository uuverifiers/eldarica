package lazabs.horn.preprocessor
import ap.SimpleAPI
import ap.parser.IExpression.{ConstantTerm, Predicate}
import ap.parser._
import ap.theories.Heap.HeapFunExtractor
import ap.theories.{ADT, Heap}
import ap.types.{MonoSortedIFunction, MonoSortedPredicate, Sort, SortedConstantTerm}
import lazabs.horn.Util.{DagEmpty, DagNode}
import lazabs.horn.abstractions.VerificationHints._
import lazabs.horn.bottomup.HornClauses.Clause
import IExpression.{toFunApplier, toPredApplier, Eq}

import scala.collection.mutable.{HashMap => MHashMap}

object HeapUpdateSiteTagger extends HornPreprocessor {
  import HornPreprocessor._
  override val name : String = "adding heap update site tags"
  private val clauseBackMapping = new MHashMap[Clause, Clause]
  private val predBackMapping = new MHashMap[Predicate, Predicate]

  /**
   * Only applicable when the input CHCs contain heap theories.
   */
  override def isApplicable(clauses          : Clauses,
                            frozenPredicates : Set[Predicate]) : Boolean = {
    clauses.flatMap(c => c.theories).toSet.exists(_.isInstanceOf[Heap])
  }

  case class TaggedHeapInfo(theory : Heap,
                            redeclaredObjSortInd : Int) {
    val taggedObjSort : Sort = theory.ObjectSort
    val taggedObjCtor : IFunction = theory.userADTCtors(theory.objectSortId)
    val taggedObjContents : IFunction = theory.userADTSels(theory.objectSortId)(0)
    val taggedObjTag  : IFunction = theory.userADTSels(theory.objectSortId)(1)
    val addrSort      : Sort = theory.AddressSort
    val heapSort      : Sort = theory.HeapSort
    val allocResSort  : Sort = theory.allocResSort
    val redeclaredObjSort : Sort = theory.userADTSorts(redeclaredObjSortInd)
    val redeclaredObjCtor : IFunction = theory.userADTCtors(redeclaredObjSortInd)
  }
  override def process(clauses          : Clauses,
                       hints            : VerificationHints,
                       frozenPredicates : Set[Predicate]) : (Clauses,
    VerificationHints, BackTranslator) = {
    val heapTheories = clauses.flatMap(c => c.theories)
      .filter(theory => theory.isInstanceOf[Heap])
      .map(theory => theory.asInstanceOf[Heap])
      .toSet

    /**
     * Declare the new heap theories, such that it has a new object sort
     * TaggedObject(contents : Object, tag : Int).
     */
    val oldHeapToNewHeap : Map[Heap, TaggedHeapInfo] =
      (for (heap <- heapTheories) yield {
        /**
         * Collect signatures from the original heap to be redeclared.
         * Note that the `object` of the new heap is the tagged object, however,
         * the object sort of the old heap needs to be redeclared and tracked
         * for later rewriting.
         */
        val objSortName = heap.ObjectSort.name
        val oldCtorSignatures = heap.userCtorSignatures
        val oldSortNames = heap.userSortNames

        /**
         * Prepare the signature of the new theory. Appending tagged object to
         * the signature, so its index is the last one.
         */
        val taggedObjSortInd = oldCtorSignatures.size
        val taggedObjSortName = s"Tagged${heap.ObjectSort.name}"

        /**
         * The index of the old object sort is unchanged in order to avoid
         * rewriting oldCtorSignatures.
         */
        val redeclaredObjSortInd = heap.userSortNames.indexOf(objSortName)

        val ctorSignatures = oldCtorSignatures ++
          Seq((taggedObjSortName, Heap.CtorSignature(
            Seq(s"contents$objSortName" -> Heap.ADTSort(redeclaredObjSortInd),
                s"tag$objSortName" -> Heap.OtherSort(Sort.Integer)),
            Heap.ADTSort(taggedObjSortInd))))
        val sortNames = oldSortNames ++ Seq(taggedObjSortName)

        /**
         * todo: make public the original defObjCtor and use that,
         *       we cannot use the defObj term directly.
         */
        def defObjCtor(adtCtors : Seq[MonoSortedIFunction],
                       heapADTS : ADT) : ITerm = {
          /**
           * Create a default object with an invalid tag (-1)
           */
          adtCtors(taggedObjSortInd)(heap._defObj, -1)
        }

        val newHeap = new Heap(heapSortName = heap.HeapSort.name,
                               addressSortName = heap.AddressSort.name,
                               objectSort = Heap.ADTSort(taggedObjSortInd),
                               sortNames = sortNames,
                               ctorSignatures = ctorSignatures,
                               defaultObjectCtor = defObjCtor)
        heap -> TaggedHeapInfo(newHeap, redeclaredObjSortInd)
      }).toMap

    /**
     * First create new preds as needed, and create a map from old preds
     */

    val oldUnintPreds = clauses.flatMap(_.predicates)

    /**
     * We could extract the sorts inside [[HeapClauseRewriter]], but we need the
     * sorts here to create the predicates before calling the rewriter as the
     * rewriter is for a single clause and the predicates need to be rewritten
     * for all clauses at once.
     * Dropping the last sort from the new heap as that does not exist in the old heap.
     */
    val oldToNewSortMap : Map[Sort, Sort] = oldHeapToNewHeap.flatMap{
      case (oldHeap, newHeap) =>
        Map(oldHeap.HeapSort -> newHeap.heapSort,
            oldHeap.AddressSort -> newHeap.addrSort,
            oldHeap.ObjectSort -> newHeap.redeclaredObjSort) ++
          (oldHeap.heapADTs.sorts zip
            newHeap.theory.heapADTs.sorts.filterNot(_ == newHeap.taggedObjSort))
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

    val oldPredToNewPred = Map() ++ predBackMapping.map(_.swap)

    for ((oldHeap, newHeap) <- oldHeapToNewHeap) {
      for ((clause, tag) <- clauses zipWithIndex) {
        val rewriter = new HeapClauseRewriter(
          oldHeap, newHeap, oldPredToNewPred, oldToNewSortMap, clause, tag)
        val newClause : Clause = rewriter.rewriteClause
        assert(!newClause.theories.contains(oldHeap))
        clauseBackMapping += newClause -> clause
      }
    }

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

    /**
     * Update the hints to use the new predicates.
     * todo: Do we need to update formulas when hints are [[VerifHintInitPred]]?
     */
    val newHints = hints.renamePredicates(oldPredToNewPred)

    (clauseBackMapping.keys.toSeq, newHints, backTranslator)
  }

  /**
   * Rewrites formulas over the oldHeap to formulas over the newHeap, while
   * also adding tags to alloc and write operations. Reads are also rewritten
   * to a special form to allow replacing phi with a formula that will be
   * guessed by an oracle (e.g., by [[HeapAddressUpdateSitesAnalysis]].
   * Returns a map from old constants to new constants.
   */
  class HeapClauseRewriter(oldHeap         : Heap,
                           newHeap         : TaggedHeapInfo,
                           oldToNewPredMap : Map[Predicate, Predicate],
                           oldToNewSortMap : Map[Sort, Sort],
                           clause          : Clause,
                           tagId           : Int)
    extends CollectingVisitor[Unit, IExpression] {

    assert(clause.predicates.forall(oldToNewPredMap contains))

    private val oldNewTermMap : Map[ConstantTerm, ConstantTerm] =
      clause.constantsSorted.map{
        case c : SortedConstantTerm if oldToNewSortMap contains c.sort =>
          c -> new SortedConstantTerm(c.name, oldToNewSortMap(c.sort))
        case c => c -> c
      }.toMap

    private val oldToNewFunMap : Map[IFunction, IFunction] = {
      ((oldHeap.functions zip newHeap.theory.functions) ++
        oldHeap.heapADTs.functions.map(
          oldF => oldF ->
            newHeap.theory.heapADTs.functions.find(_.name == oldF.name).get)).toMap
    }

    val oldToNewTheoryPredMap : Map[Predicate, Predicate] =
      (oldHeap.predefPredicates zip newHeap.theory.predefPredicates).toMap

    def rewriteClause : Clause = {
      val newConstraint = visit(clause.constraint, ()).asInstanceOf[IFormula]
      val newHead = visit(clause.head, ()).asInstanceOf[IAtom]
      val newBody = clause.body.map(a => visit(a, ()).asInstanceOf[IAtom])
      Clause(newHead, newBody, newConstraint)
    }

    override def postVisit(t : IExpression, arg : Unit,
                           subres : Seq[IExpression]) : IExpression = {
      t match {
        case IConstant(SortedConstantTerm(c, _)) =>
          assert(oldNewTermMap contains c)
          IConstant(oldNewTermMap(c))

        // Rewrite uninterpreted predicates using the provided map
        case IAtom(pred, _) if oldToNewPredMap contains pred =>
          IAtom(oldToNewPredMap(pred), subres.map(_.asInstanceOf[ITerm]))

        // Rewrite theory predicates
        case IAtom(pred, _) if oldToNewTheoryPredMap contains pred =>
          IAtom(oldToNewTheoryPredMap(pred), subres.map(_.asInstanceOf[ITerm]))

        // Rewrite functions using the provided map
        case IFunApp(f, _) if oldToNewFunMap contains f =>
          IFunApp(oldToNewFunMap(f), subres.map(_.asInstanceOf[ITerm]))

        // Note that hp is still oldHeap in below check, because we do not look
        // at subargs where the heap is the newHeap.
        case Eq(IFunApp(f@HeapFunExtractor(hp), _), _) if hp == oldHeap =>
          val funApp = subres(0).asInstanceOf[IFunApp]
          val rhs = subres(1).asInstanceOf[ITerm]
          f match {
            case hp.read =>
              /**
               * ex t. read(h,a) = TaggedObject(o,t) \wedge phi[t]
               * This rewriting leaves out phi[t], it should be added by the
               * next analysis.
               */
              Sort.Integer.ex(t => newHeap.theory.read(funApp.args : _*) ===
                newHeap.taggedObjCtor(rhs, t))
            case hp.write =>
              val Seq(h, a, o) = funApp.args.map(_.asInstanceOf[IConstant])
              newHeap.theory.write(
                h, a, newHeap.taggedObjCtor(o, tagId)) === rhs
            case hp.alloc =>
              val Seq(h, o) = funApp.args.map(_.asInstanceOf[IConstant])
              newHeap.theory.alloc(h, newHeap.taggedObjCtor(o, tagId)) === rhs
            case hp.allocHeap =>
              val Seq(h, o) = funApp.args.map(_.asInstanceOf[IConstant])
              newHeap.theory.allocHeap(
                h, newHeap.taggedObjCtor(o, tagId)) === rhs
            case hp.allocAddr =>
              val Seq(h, o) = funApp.args.map(_.asInstanceOf[IConstant])
              newHeap.theory.allocAddr(
                h, newHeap.taggedObjCtor(o, tagId)) === rhs
            case _ =>
              t update subres
          }
        case _ =>
          t update subres
      }
    }
  }
}
