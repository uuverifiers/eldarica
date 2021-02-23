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
(declare-datatypes ((HeapObject 0) (node 0))
                   (((O_Int (getInt Int)) (O_Addr (getAddr Addr)) (O_node (getnode node)) (defObj))
                   ((node (next Addr)))))
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
(declare-fun inv_main10 (Heap Addr Int) Bool)
(declare-fun inv_main14 (Heap Addr) Bool)
(declare-fun inv_main16 (Heap Addr Addr) Bool)
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main22 (Heap Addr Addr Int) Bool)
(declare-fun inv_main25 (Heap Addr) Bool)
(declare-fun inv_main26 (Heap Addr node) Bool)
(assert (inv_main2 emptyHeap))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr) (var3 Addr) (var4 Addr) (var5 node) (var6 node) (var7 Heap)) (or (not (and (inv_main2 var0) (and (and (not (= nullAddr var4)) (and (and (= var7 (newHeap (alloc var1 (O_node var6)))) (= var2 var3)) (= var4 (newAddr (alloc var1 (O_node var6)))))) (and (not (= nullAddr var3)) (and (= var1 (newHeap (alloc var0 (O_node var5)))) (= var3 (newAddr (alloc var0 (O_node var5))))))))) (inv_main16 var7 var2 var4))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main16 var0 var2 var1)) (inv_main14 (write var0 var2 (O_node (node var1))) var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int) (var3 Addr)) (or (not (inv_main22 var0 var3 var1 var2)) (inv_main22 var0 var3 var1 var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 node) (var3 Addr) (var4 Heap) (var5 node) (var6 Heap) (var7 Addr)) (or (not (and (inv_main2 var0) (and (and (= nullAddr var7) (and (and (= var4 (newHeap (alloc var6 (O_node var2)))) (= var1 var3)) (= var7 (newAddr (alloc var6 (O_node var2)))))) (and (not (= nullAddr var3)) (and (= var6 (newHeap (alloc var0 (O_node var5)))) (= var3 (newAddr (alloc var0 (O_node var5))))))))) (inv_main22 var4 var1 var7 1))))
(assert (forall ((var0 Heap) (var1 Addr)) (or (not (inv_main14 var0 var1)) (inv_main26 var0 var1 (getnode (read var0 var1))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Int)) (or (not (inv_main10 var0 var1 var2)) (inv_main10 var0 var1 var2))))
(assert (forall ((var0 Heap) (var1 Heap) (var2 node) (var3 Addr)) (or (not (and (inv_main2 var0) (and (= nullAddr var3) (and (= var1 (newHeap (alloc var0 (O_node var2)))) (= var3 (newAddr (alloc var0 (O_node var2)))))))) (inv_main10 var1 var3 1))))
(assert (forall ((var0 Heap) (var1 node) (var2 Addr)) (or (not (inv_main26 var0 var2 var1)) (inv_main25 (write var0 var2 (O_node var1)) var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main16 var0 var2 var1) (not (is-O_node (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main14 var0 var1) (not (is-O_node (read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 node) (var2 Addr)) (not (and (inv_main26 var0 var2 var1) (not (is-O_node (read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main25 var0 var1) (not (is-O_node (read var0 var1)))))))
(check-sat)
