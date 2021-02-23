(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status sat)
;===============================================================================
; Encoding of Heap sorts and operations
;-------------------------------------------------------------------------------
(define-sort Addr() Int)
(declare-datatypes ((HeapObject 0) (TData 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_TData (getTData TData)) (defObj))
                   ((TData (lo Addr) (hi Addr)))))
(declare-datatypes ((AllocResHeap 0) (Heap 0))
                   (((AllocResHeap   (newHeap Heap) (newAddr Addr)))
                    ((HeapCtor (HeapSize Int)
                               (HeapContents (Array Addr HeapObject))))))
(define-fun nullAddr  () Addr 0)
(define-fun defHeapObject    () HeapObject defObj)
(define-fun valid     ((h Heap) (p Addr)) Bool
  (and (>= (HeapSize h) p) (> p 0)))
(define-fun emptyHeap () Heap (
  HeapCtor 0 (( as const (Array Addr HeapObject)) defHeapObject)))
(define-fun read ((h Heap) (p Addr)) HeapObject
  (ite (valid h p)
       (select (HeapContents h) p)
       defHeapObject))
(define-fun write ((h Heap) (p Addr) (o HeapObject)) Heap
  (ite (valid h p)
       (HeapCtor (HeapSize h) (store (HeapContents h) p o))
       h))
(define-fun alloc   ((h Heap) (o HeapObject)) AllocResHeap
  (AllocResHeap (HeapCtor (+ 1 (HeapSize h))
                    (store (HeapContents h) (+ 1 (HeapSize h)) o))
          (+ 1 (HeapSize h))))

;===============================================================================
(declare-fun inv_main10 (Heap TData Int) Bool)
(declare-fun inv_main12 (Heap TData Int) Bool)
(declare-fun inv_main18 (Heap TData TData Addr Addr) Bool)
(declare-fun inv_main22 (Heap TData TData Addr Addr Int) Bool)
(declare-fun inv_main3 (Heap TData) Bool)
(assert (forall ((var0 Heap) (var1 TData)) (or (not (= var0 emptyHeap)) (inv_main3 var0 var1))))
(assert (forall ((var0 TData) (var1 Int) (var2 Heap)) (or (not (inv_main10 var2 var0 var1)) (inv_main12 (write var2 (lo var0) (O_Int 4)) var0 var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 TData) (var4 Heap) (var5 TData) (var6 Int) (var7 Heap) (var8 TData) (var9 TData)) (or (not (and (inv_main12 var7 var3 var6) (and (and (and (and (= var4 var0) (= var9 var8)) (= var5 var8)) (= var1 (lo var8))) (and (and (= var0 (write var7 (hi var3) (O_Int 8))) (= var8 var3)) (= var2 var6))))) (inv_main18 var4 var9 var5 var1 (hi var5)))))
(assert (forall ((var0 TData) (var1 Addr) (var2 Int) (var3 Heap) (var4 Heap) (var5 TData) (var6 Heap) (var7 Int) (var8 TData) (var9 Addr) (var10 Int) (var11 Int) (var12 TData) (var13 Heap) (var14 Int)) (or (not (and (inv_main3 var13 var0) (and (and (and (and (and (= var6 (newHeap (alloc var4 (O_Int var7)))) (= var5 var8)) (= var2 var11)) (= var1 (newAddr (alloc var4 (O_Int var7))))) (and (and (and (= var3 (newHeap (alloc var13 (O_Int var14)))) (= var12 var0)) (= var10 1)) (= var9 (newAddr (alloc var13 (O_Int var14)))))) (and (and (= var4 var3) (= var8 (TData var9 (hi var12)))) (= var11 var10))))) (inv_main10 var6 (TData (lo var5) var1) var2))))
(assert (forall ((var0 TData) (var1 TData) (var2 Addr) (var3 Addr) (var4 Heap)) (or (not (inv_main18 var4 var0 var1 var3 var2)) (inv_main22 var4 var0 var1 var3 var2 (getInt (read var4 var3))))))
(assert (forall ((var0 TData) (var1 Int) (var2 Heap)) (not (and (inv_main10 var2 var0 var1) (not (is-O_Int (read var2 (lo var0))))))))
(assert (forall ((var0 TData) (var1 Int) (var2 Heap)) (not (and (inv_main12 var2 var0 var1) (not (is-O_Int (read var2 (hi var0))))))))
(assert (forall ((var0 TData) (var1 TData) (var2 Addr) (var3 Addr) (var4 Heap)) (not (and (inv_main18 var4 var0 var1 var3 var2) (not (is-O_Int (read var4 var3)))))))
(assert (forall ((var0 TData) (var1 TData) (var2 Addr) (var3 Addr) (var4 Heap) (var5 Int)) (not (and (inv_main22 var4 var0 var1 var3 var2 var5) (not (is-O_Int (read var4 var2)))))))
(check-sat)
