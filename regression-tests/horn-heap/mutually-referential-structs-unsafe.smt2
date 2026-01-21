(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-heap Heap Addr Range HeapObject
 defObj
 ((HeapObject 0) (parent 0) (child 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (O_parent (getparent parent))
   (O_child (getchild child))
   (defObj)
  )
  (
   (parent (child1 Addr) (child2 Addr))
  )
  (
   (child (p Addr))
  )
))
(declare-fun inv_main2 (Heap) Bool)
(declare-fun inv_main4 (Heap Addr) Bool)
(declare-fun inv_main5 (Heap Addr Addr) Bool)
(declare-fun inv_main7 (Heap Addr) Bool)
(declare-fun inv_main8 (Heap Addr Addr) Bool)
(assert (inv_main2 (as heap.empty Heap)))
(assert (forall ((var0 Heap) (var1 Heap) (var2 Addr)) (or (not (and (inv_main2 var0) (and (= var1 (heap.heapAddrPair_1 (heap.alloc var0 (O_parent (parent (as heap.null Addr) (as heap.null Addr)))))) (= var2 (heap.heapAddrPair_2 (heap.alloc var0 (O_parent (parent (as heap.null Addr) (as heap.null Addr))))))))) (inv_main5 (heap.heapAddrPair_1 (heap.alloc var1 (O_child (child (as heap.null Addr))))) var2 (heap.heapAddrPair_2 (heap.alloc var1 (O_child (child (as heap.null Addr)))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Heap) (var3 Addr)) (or (not (and (inv_main4 var0 var3) (and (= var2 (heap.write var0 (child1 (getparent (heap.read var0 var3))) (O_child (child var3)))) (= var1 var3)))) (inv_main8 (heap.heapAddrPair_1 (heap.alloc var2 (O_child (child (as heap.null Addr))))) var1 (heap.heapAddrPair_2 (heap.alloc var2 (O_child (child (as heap.null Addr)))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main8 var0 var2 var1)) (inv_main7 (heap.write var0 var2 (O_parent (parent (child1 (getparent (heap.read var0 var2))) var1))) var2))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (or (not (inv_main5 var0 var1 var2)) (inv_main4 (heap.write var0 var1 (O_parent (parent var2 (child2 (getparent (heap.read var0 var1)))))) var1))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main5 var0 var1 var2) (not (is-O_parent (heap.read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main4 var0 var1) (not (is-O_parent (heap.read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main4 var0 var1) (not (is-O_child (heap.read var0 (child1 (getparent (heap.read var0 var1))))))))))
(assert (forall ((var0 Heap) (var1 Addr) (var2 Addr)) (not (and (inv_main8 var0 var2 var1) (not (is-O_parent (heap.read var0 var2)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main7 var0 var1) (not (is-O_parent (heap.read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main7 var0 var1) (not (is-O_child (heap.read var0 (child1 (getparent (heap.read var0 var1))))))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main7 var0 var1) (not (is-O_parent (heap.read var0 var1)))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main7 var0 var1) (not (is-O_child (heap.read var0 (child2 (getparent (heap.read var0 var1))))))))))
(assert (forall ((var0 Heap) (var1 Addr)) (not (and (inv_main7 var0 var1) (not (= (p (getchild (heap.read var0 (child1 (getparent (heap.read var0 var1)))))) (p (getchild (heap.read var0 (child2 (getparent (heap.read var0 var1))))))))))))
(check-sat)
