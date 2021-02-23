(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unsat)
(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (TData 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (O_TData (getTData TData))
   (defObj)
  )
  (
   (TData (lo Addr) (hi Addr))
  )
))
(declare-fun inv_main0 (Heap Int) Bool)
(declare-fun inv_main10 (Heap TData Int) Bool)
(declare-fun inv_main12 (Heap TData Int) Bool)
(declare-fun inv_main18 (Heap TData Int Addr Addr) Bool)
(declare-fun inv_main22 (Heap TData Int Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap TData) Bool)
(assert (forall ((var0 Heap) (var1 TData)) (or (not (= var0 emptyHeap)) (inv_main3 var0 var1))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Heap) (var4 Int) (var5 Int) (var6 Addr) (var7 Heap) (var8 Int) (var9 TData) (var10 TData) (var11 TData) (var12 Addr) (var13 Addr)) (or (not (and (inv_main22 var0 var10 var5 var12 var13 var4) (and (and (and (and (and (and (= var7 var0) (= var11 (TData nullAddr (hi var10)))) (= var8 var5)) (= var6 var12)) (= var2 var13)) (not (<= 0 (+ var4 (* (- 1) (getInt (read var0 var13))))))) (and (and (= var3 var7) (= var9 (TData (lo var11) nullAddr))) (= var1 var8))))) (inv_main0 var3 0))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Heap) (var4 Addr) (var5 Heap) (var6 Addr) (var7 Heap) (var8 Int) (var9 TData) (var10 Int) (var11 TData) (var12 Int) (var13 Int) (var14 Int) (var15 Heap) (var16 Addr) (var17 TData) (var18 TData) (var19 Addr) (var20 TData) (var21 Addr) (var22 Addr) (var23 Addr)) (or (not (and (inv_main22 var1 var17 var12 var19 var23 var10) (and (and (and (and (and (and (and (= var7 var15) (= var11 (TData nullAddr (hi var18)))) (= var13 var14)) (= var16 var0)) (= var6 var22)) (and (<= 0 (+ var10 (* (- 1) (getInt (read var1 var23))))) (and (and (and (and (= var5 (write var1 var19 defObj)) (= var20 var17)) (= var8 var12)) (= var4 var19)) (= var21 var23)))) (and (and (and (and (= var15 (write var5 var21 defObj)) (= var18 var20)) (= var14 var8)) (= var0 var4)) (= var22 var21))) (and (and (= var3 var7) (= var9 (TData (lo var11) nullAddr))) (= var2 var13))))) (inv_main0 var3 0))))
(assert (forall ((var0 TData) (var1 Int) (var2 Heap) (var3 Int) (var4 TData) (var5 TData) (var6 Heap) (var7 Addr) (var8 Heap) (var9 Int)) (or (not (and (inv_main12 var2 var5 var1) (and (and (and (and (= var6 var8) (= var4 var0)) (= var9 1)) (= var7 (lo var0))) (and (and (= var8 (write var2 (hi var5) (O_Int 8))) (= var0 var5)) (= var3 var1))))) (inv_main18 var6 var4 var9 var7 (hi var4)))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 TData) (var3 TData) (var4 Int) (var5 Int) (var6 Int) (var7 Heap) (var8 Heap) (var9 Int) (var10 TData) (var11 Int) (var12 Heap) (var13 Addr) (var14 TData)) (or (not (and (inv_main3 var0 var10) (and (and (and (and (and (= var8 (newHeap (alloc var12 (O_Int var5)))) (= var2 var3)) (= var4 var9)) (= var1 (newAddr (alloc var12 (O_Int var5))))) (and (and (and (= var7 (newHeap (alloc var0 (O_Int var6)))) (= var14 var10)) (= var11 1)) (= var13 (newAddr (alloc var0 (O_Int var6)))))) (and (and (= var12 var7) (= var3 (TData var13 (hi var14)))) (= var9 var11))))) (inv_main10 var8 (TData (lo var2) var1) var4))))
(assert (forall ((var0 Heap) (var1 TData) (var2 Addr) (var3 Int) (var4 Addr)) (or (not (inv_main18 var0 var1 var3 var2 var4)) (inv_main22 var0 var1 var3 var2 var4 (getInt (read var0 var2))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 TData)) (or (not (inv_main10 var1 var2 var0)) (inv_main12 (write var1 (lo var2) (O_Int 4)) var2 var0))))
(assert (forall ((var0 Int) (var1 Heap) (var2 TData)) (not (and (inv_main10 var1 var2 var0) (not (is-O_Int (read var1 (lo var2))))))))
(assert (forall ((var0 Int) (var1 Heap) (var2 TData)) (not (and (inv_main12 var1 var2 var0) (not (is-O_Int (read var1 (hi var2))))))))
(assert (forall ((var0 Heap) (var1 TData) (var2 Addr) (var3 Int) (var4 Addr)) (not (and (inv_main18 var0 var1 var3 var2 var4) (not (is-O_Int (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 TData) (var2 Int) (var3 Addr) (var4 Int) (var5 Addr)) (not (and (inv_main22 var0 var1 var4 var3 var5 var2) (not (is-O_Int (read var0 var5)))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int)) (not (and (inv_main0 var0 var2) (not (= (read var0 var1) defObj))))))
(check-sat)
