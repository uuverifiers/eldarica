(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (defObj)
  )
))
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main4 (Heap Addr Addr) Bool)
(assert (inv_main2 (as emptyHeap Heap)))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap)) (or (not (and (inv_main2 var1) (and (= var2 (newHeap (alloc var1 (O_Int 0)))) (= var0 (newAddr (alloc var1 (O_Int 0))))))) (inv_main4 var2 var0 0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main4 var1 var0 var2) (not (is-O_Int (read var1 var2)))))))
(check-sat)
