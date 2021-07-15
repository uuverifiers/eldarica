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
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main5 (Heap Addr) Bool)
(declare-fun inv_main6 (Heap Addr Int) Bool)
(declare-fun inv_main7 (Heap Addr Int) Bool)
(assert (inv_main2 (as emptyHeap Heap)))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (or (not (inv_main6 var2 var1 var0)) (inv_main7 var2 var1 (+ var0 (getInt (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main4 var1 var0)) (inv_main5 (write var1 var0 (O_Int 3)) var0))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main5 var1 var0)) (inv_main6 var1 var0 (getInt (read var1 var0))))))
(assert (forall ((var0 Addr) (var1 Heap)) (or (not (inv_main3 var1 var0)) (inv_main4 (write var1 var0 (O_Int 42)) var0))))
(assert (forall ((var0 Heap)) (or (not (inv_main2 var0)) (inv_main3 (newHeap (alloc var0 (O_Int 0))) (newAddr (alloc var0 (O_Int 0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main3 var1 var0) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main4 var1 var0) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap)) (not (and (inv_main5 var1 var0) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap)) (not (and (inv_main6 var2 var1 var0) (not (is-O_Int (read var2 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int)) (not (and (inv_main7 var1 var0 var2) (and (and (and (and (and (not (= var2 0)) (not (= var2 3))) (not (= var2 6))) (not (= var2 42))) (not (= var2 45))) (not (= var2 84)))))))
(check-sat)
