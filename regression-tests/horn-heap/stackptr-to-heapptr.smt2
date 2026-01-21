(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-heap Heap Addr Range HeapObject
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
(declare-fun inv_main6 (Heap Addr Addr) Bool)
(assert (inv_main2 (as heap.empty Heap)))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap) (var3 Heap) (var4 Addr) (var5 Addr)) (or (not (and (inv_main4 var3 var1 var0) (and (and (= var2 (heap.write var3 var0 (O_Int 42))) (= var4 var1)) (= var5 var0)))) (inv_main6 var2 var5 var4))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr)) (or (not (and (inv_main2 var1) (and (= var0 (heap.heapAddrPair_1 (heap.alloc var1 (O_Int 0)))) (= var2 (heap.heapAddrPair_2 (heap.alloc var1 (O_Int 0))))))) (inv_main4 (heap.heapAddrPair_1 (heap.alloc var0 (O_Int 0))) var2 (heap.heapAddrPair_2 (heap.alloc var0 (O_Int 0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main4 var2 var1 var0) (not (is-O_Int (heap.read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main6 var2 var1 var0) (not (is-O_Int (heap.read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main6 var2 var1 var0) (and (= (getInt (heap.read var2 var1)) 42) (not (is-O_Int (heap.read var2 var0))))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main6 var2 var1 var0) (or (not (= (getInt (heap.read var2 var1)) 42)) (not (= (getInt (heap.read var2 var0)) 0)))))))
(check-sat)
