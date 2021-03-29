(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (S 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (O_S (getS S))
   (defObj)
  )
  (
   (S (f Int))
  )
))
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main5 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main6 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr Addr Addr) Bool)
(declare-fun inv_main8 (Heap Addr Addr Addr) Bool)
(assert (inv_main2 (as emptyHeap Heap)))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (inv_main7 var1 var0 var3 var2)) (inv_main8 var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap)) (or (not (and (inv_main2 var1) (and (= var2 (newHeap (alloc var1 (O_Int 0)))) (= var0 (newAddr (alloc var1 (O_Int 0))))))) (inv_main5 var2 var0 var0 var0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (inv_main5 var1 var0 var3 var2)) (inv_main6 var1 var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (or (not (inv_main6 var1 var0 var3 var2)) (inv_main7 (write var1 var0 (O_Int 42)) var0 var3 var2))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main5 var1 var0 var3 var2) (not (is-O_Int (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main5 var1 var0 var3 var2) (not (= (getInt (read var1 var2)) 0))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main6 var1 var0 var3 var2) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main7 var1 var0 var3 var2) (not (is-O_Int (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main7 var1 var0 var3 var2) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main7 var1 var0 var3 var2) (not (= (getInt (read var1 var2)) (getInt (read var1 var0))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main8 var1 var0 var3 var2) (not (is-O_Int (read var1 var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Addr)) (not (and (inv_main8 var1 var0 var3 var2) (not (= (getInt (read var1 var2)) 42))))))
(check-sat)
