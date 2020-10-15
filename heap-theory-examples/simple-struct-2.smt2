(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (.AS0 0) (S 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (O_.AS0 (get.AS0 .AS0))
   (O_S (getS S))
   (defObj)
  )
  (
   (.AS0 (z Int))
  )
  (
   (S (x Int) (y .AS0))
  )
))
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main3 (Heap Addr) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main5 (Heap Addr Int) Bool)
(assert (inv_main2 (as emptyHeap Heap)))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main4 var0 var1)) (inv_main5 var0 var1 (z (y (getS (read var0 var1))))))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main3 var0 var1)) (inv_main4 (write var0 var1 (O_S (S (x (getS (read var0 var1))) (.AS0 42)))) var1))))
(assert (forall ((var0 Heap)) (or (not (inv_main2 var0)) (inv_main3 (newHeap (alloc var0 (O_S (S 0 (.AS0 0))))) (newAddr (alloc var0 (O_S (S 0 (.AS0 0)))))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main3 var0 var1) (not (is-O_S (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main4 var0 var1) (not (is-O_S (read var0 var1)))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 Addr)) (not (and (inv_main5 var1 var2 var0) (and (not (= var0 0)) (not (= var0 42)))))))
(check-sat)
