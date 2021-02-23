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
(declare-datatypes ((HeapObject 0) (item 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_item (getitem item)) (defObj))
                   ((item (next Addr) (data Addr)))))
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
(declare-fun inv_main10 (Heap Addr Int Addr) Bool)
(declare-fun inv_main12 (Heap Addr Int Addr Addr) Bool)
(declare-fun inv_main15 (Heap Addr) Bool)
(declare-fun inv_main17 (Heap Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main21 (Heap Addr) Bool)
(declare-fun inv_main9 (Heap Addr Int Addr) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 item)) (or (not (and (inv_main2 var2) (and (= var0 var2) (= var1 nullAddr)))) (inv_main9 (newHeap (alloc var0 (O_item var3))) var1 1 (newAddr (alloc var0 (O_item var3)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Int) (var4 Heap) (var5 Int) (var6 item) (var7 Addr) (var8 Int) (var9 Addr) (var10 Addr)) (or (not (and (inv_main12 var4 var10 var5 var9 var0) (and (not (= var8 0)) (and (and (and (= var1 (write var4 var9 (O_item (item (next (getitem (read var4 var9))) var0)))) (= var7 var10)) (= var3 var5)) (= var2 var9))))) (inv_main9 (newHeap (alloc var1 (O_item var6))) var2 1 (newAddr (alloc var1 (O_item var6)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr)) (or (not (inv_main9 var0 var3 var1 var2)) (inv_main10 (write var0 var2 (O_item (item var3 (data (getitem (read var0 var2)))))) var3 var1 var2))))
(assert (forall ((var0 Addr) (var1 Addr) (var2 Addr) (var3 Heap) (var4 Heap) (var5 Heap) (var6 Addr) (var7 Addr) (var8 Addr)) (or (not (and (inv_main17 var3 var8 var1) (and (not (= var6 nullAddr)) (and (and (and (= var4 (write var3 (data (getitem (read var3 var8))) defObj)) (= var2 var8)) (= var7 var1)) (and (and (= var5 (write var4 var2 defObj)) (= var0 var2)) (= var6 var7)))))) (inv_main21 var5 var6))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr) (var3 Heap) (var4 Addr) (var5 Addr) (var6 Heap) (var7 Addr)) (or (not (and (inv_main21 var1 var7) (and (not (= var4 nullAddr)) (and (and (and (= var6 var1) (= var5 var7)) (= var2 (next (getitem (read var1 var7))))) (and (and (= var3 (write var6 var5 defObj)) (= var0 var5)) (= var4 var2)))))) (inv_main21 var3 var4))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (inv_main12 var4 var9 var5 var7 var0) (and (not (= var3 nullAddr)) (and (= var3 nullAddr) (and (= var8 0) (and (and (and (= var1 (write var4 var7 (O_item (item (next (getitem (read var4 var7))) var0)))) (= var6 var9)) (= var2 var5)) (= var3 var7))))))) (inv_main21 var1 var3))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr)) (or (not (and (inv_main10 var0 var3 var1 var2) (not (= (next (getitem (read var0 var2))) nullAddr)))) (inv_main12 var0 var3 var1 var2 (data (getitem (read var0 (next (getitem (read var0 var2))))))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 item) (var3 Addr) (var4 Addr)) (or (not (and (inv_main10 var0 var4 var1 var3) (= (next (getitem (read var0 var3))) nullAddr))) (inv_main12 (newHeap (alloc var0 (O_item var2))) var4 var1 var3 (newAddr (alloc var0 (O_item var2)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Heap) (var5 Int) (var6 Addr) (var7 Addr) (var8 Int) (var9 Addr)) (or (not (and (inv_main12 var4 var9 var5 var7 var0) (and (not (= var3 nullAddr)) (and (= var8 0) (and (and (and (= var1 (write var4 var7 (O_item (item (next (getitem (read var4 var7))) var0)))) (= var6 var9)) (= var2 var5)) (= var3 var7)))))) (inv_main15 var1 var3))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main15 var0 var1)) (inv_main17 var0 var1 (next (getitem (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr)) (not (and (inv_main9 var0 var3 var1 var2) (not (is-O_item (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr)) (not (and (inv_main10 var0 var3 var1 var2) (not (is-O_item (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr)) (not (and (inv_main10 var0 var3 var1 var2) (and (not (= (next (getitem (read var0 var2))) nullAddr)) (not (is-O_item (read var0 var2))))))))
(assert (forall ((var0 Heap) (var1 Int) (var2 Addr) (var3 Addr)) (not (and (inv_main10 var0 var3 var1 var2) (and (not (= (next (getitem (read var0 var2))) nullAddr)) (not (is-O_item (read var0 (next (getitem (read var0 var2)))))))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Int) (var3 Addr) (var4 Addr)) (not (and (inv_main12 var1 var4 var2 var3 var0) (not (is-O_item (read var1 var3)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main15 var0 var1) (not (is-O_item (read var0 var1)))))))
(assert (forall ((var0 Addr) (var1 Heap) (var2 Addr)) (not (and (inv_main17 var1 var2 var0) (not (is-O_item (read var1 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main21 var0 var1) (not (is-O_item (read var0 var1)))))))
(check-sat)
