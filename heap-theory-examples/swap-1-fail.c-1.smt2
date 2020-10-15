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
(declare-fun inv_main10 (Heap Int Addr Int Addr Int) Bool)
(declare-fun inv_main11 (Heap Int Addr Int Addr Int) Bool)
(declare-fun inv_main3 (Heap Int) Bool)
(declare-fun inv_main4 (Heap Int Addr) Bool)
(declare-fun inv_main6 (Heap Int Addr) Bool)
(assert (forall ((var0 Heap)) (or (not (= var0 (as emptyHeap Heap))) (inv_main3 var0 3))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Addr) (var4 Int) (var5 Heap)) (or (not (and (inv_main4 var2 var4 var1) (and (and (= var5 (write var2 var1 (O_Int 42))) (= var0 var4)) (= var3 var1)))) (inv_main10 var5 var0 var3 1 var3 var0))))
(assert (forall ((var0 Addr) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Heap) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int)) (or (not (and (inv_main11 var3 var5 var2 var1 var9 var8) (and (and (and (and (= var6 (write var3 var9 (O_Int var8))) (= var4 var5)) (= var0 var2)) (= var10 var1)) (= var7 var9)))) (inv_main6 var6 var4 var0))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Int) (var3 Int) (var4 Addr) (var5 Heap) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Int) (var11 Addr) (var12 Addr)) (or (not (and (inv_main10 var5 var7 var4 var3 var11 var10) (and (and (and (and (and (and (= var6 var5) (= var2 var7)) (= var12 var4)) (= var9 var3)) (= var1 var11)) (= var0 var10)) (= var8 (getInt (read var5 var11)))))) (inv_main11 var6 var8 var12 var9 var1 var0))))
(assert (forall ((var0 Heap) (var1 Int)) (or (not (inv_main3 var0 var1)) (inv_main4 (newHeap (alloc var0 (O_Int 0))) var1 (newAddr (alloc var0 (O_Int 0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int)) (not (and (inv_main4 var1 var2 var0) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr)) (not (and (inv_main10 var2 var3 var1 var0 var5 var4) (not (is-O_Int (read var2 var5)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr)) (not (and (inv_main11 var2 var3 var1 var0 var5 var4) (not (is-O_Int (read var2 var5)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int)) (not (and (inv_main6 var1 var2 var0) (not (= var2 42))))))
(check-sat)
