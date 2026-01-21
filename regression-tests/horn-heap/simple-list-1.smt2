
(declare-heap Heap Addr Range HeapObject
 defObj
 ((HeapObject 0) (node 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (O_node (getnode node))
   (defObj)
  )
  (
   (node (data Int) (next Addr))
  )
))

(declare-fun I1 (Heap) Bool)
(declare-fun I2 (Heap Addr Int) Bool)
(declare-fun I3 (Heap Addr Int) Bool)

(assert (I1 (as heap.empty Heap)))
(assert (forall ((h Heap)) (=>
            (I1 h)
            (I2 (heap.heapAddrPair_1 (heap.alloc h (O_node (node 0 (as heap.null Addr)))))
                (heap.heapAddrPair_2 (heap.alloc h (O_node (node 0 (as heap.null Addr)))))
                0))))
(assert (forall ((h Heap) (p Addr) (i Int)) (=>
            (and (I2 h p i) (< i 10))
            (I2 (heap.heapAddrPair_1 (heap.alloc h (O_node (node (+ (data (getnode (heap.read h p))) 1) p))))
                (heap.heapAddrPair_2 (heap.alloc h (O_node (node (+ (data (getnode (heap.read h p))) 1) p))))
                (+ i 1)))))
(assert (forall ((h Heap) (p Addr) (i Int)) (=>
            (and (I2 h p i) (>= i 10))
            (I3 h p i))))
(assert (forall ((h Heap) (p Addr) (i Int)) (=>
            (I3 h p i)
            (heap.valid h p))))
(assert (forall ((h Heap) (p Addr) (i Int)) (=>
            (I3 h p i)
            (= i (data (getnode (heap.read h p)))))))

