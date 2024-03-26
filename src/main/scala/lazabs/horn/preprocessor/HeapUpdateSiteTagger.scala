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

        val newHeap = new Heap(heapSortName = s"Tagged${heap.HeapSort.name}",
                               addressSortName = s"Tagged${heap.AddressSort.name}",
                               objectSort = Heap.ADTSort(taggedObjSortInd),
                               sortNames = sortNames,
                               ctorSignatures = ctorSignatures,
                               defaultObjectCtor = defObjCtor)
        heap -> TaggedHeapInfo(newHeap, redeclaredObjSortInd)
      }).toMap

    /**
     * First create new preds as needed, and create a map from old preds
     */

    val oldPreds = clauses.flatMap(_.predicates)
    val oldToNewSortMap : Map[Sort, Sort] = oldHeapToNewHeap.flatMap{
      case (oldHeap, newHeap) =>
        Map(oldHeap.HeapSort -> newHeap.heapSort,
            oldHeap.AddressSort -> newHeap.addrSort,
            oldHeap.ObjectSort -> newHeap.redeclaredObjSort,
            oldHeap.allocResSort -> newHeap.allocResSort)
        // todo batchAllocResSort
    }

    for (oldPred <- oldPreds) {
      val newPred = oldPred match {
        case sortedPred : MonoSortedPredicate =>
          val newSorts : Seq[Sort] =
            for (oldSort <- sortedPred.argSorts) yield oldSort match {
              case s@Heap.HeapSortExtractor(oldHeap) =>
                oldToNewSortMap get s match {
                  case Some(newSort) => newSort
                  case None => oldSort
                }
              case _ => oldSort
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
        val rewriter =
          new HeapClauseRewriter(oldHeap, newHeap, oldToNewSortMap, clause, tag,
                                 oldPredToNewPred)
        val newClause : Clause = rewriter.rewriteClause
        clauseBackMapping += newClause -> clause
      }
    }

    val backTranslator = new BackTranslator {
      override def translate(solution : Solution) : Solution = {
        ???
      }
      override def translate(cex : CounterExample) : CounterExample =
        translateCEX(cex).collapseNodes

      private def translateCEX(dag : CounterExample) : CounterExample =
        dag match {
          case DagNode((a, clause), children, next) =>
            // TODO: update the atom `a`!
            assert(clauseBackMapping contains clause)
            DagNode((a, clauseBackMapping(clause)), children, translateCEX(next))
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
                           oldToNewSortMap : Map[Sort, Sort],
                           clause          : Clause,
                           tagId           : Int,
                           oldNewPredMap   : Map[Predicate, Predicate])
    extends CollectingVisitor[Unit, IExpression] {

    assert(clause.predicates.forall(oldNewPredMap contains))

    private val oldHeapSorts : Set[Sort] = Set(oldHeap.HeapSort, oldHeap.AddressSort)
    private val oldNewTermMap : Map[ConstantTerm, ConstantTerm] =
      clause.constantsSorted.map{
        case c : SortedConstantTerm if oldToNewSortMap contains c.sort =>
          c -> new SortedConstantTerm(c.name, oldToNewSortMap(c.sort))
        case c => c -> c
      }.toMap

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

        case IAtom(oldHeap.isAlloc, _) =>
          IAtom(newHeap.theory.isAlloc, subres.map(_.asInstanceOf[ITerm]))

        case IAtom(pred, _) =>
          oldNewPredMap(pred)(subres.map(_.asInstanceOf[ITerm]):_*)

        case Eq(IFunApp(f@HeapFunExtractor(hp), _), _) if hp == oldHeap =>
          val funApp = subres(0).asInstanceOf[IFunApp]
          val rhs = subres(1).asInstanceOf[ITerm]
          f match {
            case hp.emptyHeap =>
              newHeap.theory.emptyHeap(funApp.args : _*) === rhs
            case hp.nullAddr =>
              newHeap.theory.nullAddr(funApp.args : _*) === rhs
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
            case hp.allocResCtor =>
              val Seq(h, a) = funApp.args.map(_.asInstanceOf[IConstant])
              newHeap.theory.allocResCtor(h, a) === rhs
            case _ =>
              println("Not rewriting " + SimpleAPI.pp(t))
              t update subres
          }
        case _ =>
          println("Not rewriting " + SimpleAPI.pp(t))
          t update subres
      }
    }
  }
}
