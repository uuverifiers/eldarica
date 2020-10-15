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
(assert (forall ((var0 Addr) (var1 Heap) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr)) (or (not (and (inv_main4 var1 var4 var0) (and (and (= var2 (write var1 var0 (O_Int 42))) (= var3 var4)) (= var5 var0)))) (inv_main10 var2 var3 var5 1 var5 var3))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Int) (var7 Addr) (var8 Int) (var9 Addr) (var10 Int)) (or (not (and (inv_main11 var4 var5 var3 var2 var9 var8) (and (and (and (and (= var1 (write var4 var9 (O_Int var8))) (= var10 var5)) (= var7 var3)) (= var6 var2)) (= var0 var9)))) (inv_main6 var1 var10 var7))))
(assert (forall ((var0 Int) (var1 Int) (var2 Addr) (var3 Addr) (var4 Int) (var5 Addr) (var6 Heap) (var7 Int) (var8 Int) (var9 Int) (var10 Addr) (var11 Heap) (var12 Int)) (or (not (and (inv_main10 var6 var7 var5 var4 var10 var9) (and (and (and (and (and (and (= var11 var6) (= var12 var7)) (= var2 var5)) (= var0 var4)) (= var3 var10)) (= var1 var9)) (= var8 (getInt (read var6 var10)))))) (inv_main11 var11 var8 var2 var0 var3 var1))))
(assert (forall ((var0 Heap) (var1 Int)) (or (not (inv_main3 var0 var1)) (inv_main4 (newHeap (alloc var0 (O_Int 0))) var1 (newAddr (alloc var0 (O_Int 0)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int)) (not (and (inv_main4 var1 var2 var0) (not (is-O_Int (read var1 var0)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr)) (not (and (inv_main10 var2 var3 var1 var0 var5 var4) (not (is-O_Int (read var2 var5)))))))
(assert (forall ((var0 Int) (var1 Addr) (var2 Heap) (var3 Int) (var4 Int) (var5 Addr)) (not (and (inv_main11 var2 var3 var1 var0 var5 var4) (not (is-O_Int (read var2 var5)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int)) (not (and (inv_main6 var1 var2 var0) (and (and (not (= var2 0)) (not (= var2 3))) (not (= var2 42)))))))
(check-sat)
