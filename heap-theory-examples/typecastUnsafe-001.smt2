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
(declare-fun inv_main4 (Heap Addr Addr) Bool)
(declare-fun inv_main5 (Heap Addr Addr) Bool)
(assert (inv_main2 (as emptyHeap Heap)))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap)) (or (not (and (inv_main2 var0) (and (= var2 (newHeap (alloc var0 (O_Int 0)))) (= var1 (newAddr (alloc var0 (O_Int 0))))))) (inv_main4 var2 var1 var1))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (or (not (inv_main4 var2 var1 var0)) (inv_main5 (write var2 var0 (O_S (S 42))) var1 var0))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main4 var2 var1 var0) (not (is-O_S (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main5 var2 var1 var0) (not (is-O_S (read var2 var0)))))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Heap)) (not (and (inv_main5 var2 var1 var0) (not (= (f (getS (read var2 var0))) 42))))))
(check-sat)
