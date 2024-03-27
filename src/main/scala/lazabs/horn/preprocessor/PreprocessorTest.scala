package lazabs.horn.preprocessor

import ap.api.SimpleAPI
import ap.parser._
import ap.parser.IExpression._
import ap.theories.{ADT, Heap}
import ap.types.MonoSortedIFunction
import lazabs.horn.abstractions.EmptyVerificationHints
import lazabs.horn.bottomup.HornClauses.toPrologSyntax

object PreprocessorTest extends App {
  lazabs.GlobalParameters.get.assertions = true

  SimpleAPI.withProver(enableAssert = true){pp =>
    import pp._

    def defObjCtor(adtCtors : Seq[MonoSortedIFunction],
                   heapADTS : ADT) : ITerm = {
      adtCtors.head(0)
    }
    val heap = new Heap("Heap", "Addr", Heap.ADTSort(0),
                        Seq("Obj"),
                        Seq(("boxInt", Heap.CtorSignature(
                          Seq(("getInt", Heap.OtherSort(Sort.Integer))),
                          Heap.ADTSort(0)))),
                        defObjCtor)

    val p  = createConstant("p", heap.AddressSort)
    val p1 = createConstant("p1", heap.AddressSort)
    val q  = createConstant("q", heap.AddressSort)
    val q1 = createConstant("q1", heap.AddressSort)
    val h  = createConstant("h", heap.HeapSort)
    val h1 = createConstant("h1", heap.HeapSort)
    val o  = createConstant("o", heap.ObjectSort)

    val I = (0 to 10).map(i => createRelation(
      s"I$i", Seq(heap.HeapSort, heap.AddressSort, heap.AddressSort)))

    val clauses = {
      import ap.parser.IExpression._
      import heap._
      List(
        I(0)(h, p, q) :- (emptyHeap() === h),
        I(1)(h, p1, q) :- (p1 === nullAddr(), I(0)(h, p, q)),
        I(2)(h, p, q1) :- (q1 === nullAddr(), I(1)(h, p, q)),
        I(3)(h1, p1, q) :- (h1 === allocHeap(h, o), allocAddr(h, o) === p1, I(2)(h, p, q)),
        I(4)(h1, p, q1) :- (h1 === allocHeap(h, o), allocAddr(h, o) === q1, I(3)(h, p, q)),
        I(5)(h1, p, q) :- (h1 === write(h, p, o), I(4)(h, p, q)),
        false :- (read(h,p) === read(h,q), I(5)(h, p, q))
        )
    }

    val preprocessor = new DefaultPreprocessor

    lazabs.GlobalParameters.get.heapInvariantEncoding = true

    val (flattenedClauses, _, _) =
      (new ConstraintSimplifier).process(clauses, EmptyVerificationHints)

    val (simplifiedClauses, _, _) = {
      HeapUpdateSiteTagger.process(flattenedClauses, EmptyVerificationHints)
      //preprocessor.process(clauses, EmptyVerificationHints)
    }

    val updateSiteTags : Set[Int] = HeapUpdateSiteTagger.getUpdateSiteIds

    val (analysedClauses, _, _) =
      SimplePropagators.HeapAddressUpdateSitePropagator(updateSiteTags).process(
        simplifiedClauses, EmptyVerificationHints)

    println("Flattened")
    flattenedClauses.sortBy(_.head.toString()).map(_.toPrologString).foreach(println)
    println
    println("Tagged")
    simplifiedClauses.sortBy(_.head.toString()).map(_.toPrologString).foreach(println)
    println
    println("Analysed & augmented")
    analysedClauses.sortBy(_.head.toString()).map(_.toPrologString).foreach(println)
  }
}
