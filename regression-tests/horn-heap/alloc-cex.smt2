
(declare-heap Heap Addr Range HeapObject
 defObj
 ((HeapObject 0)) (
  (
   (O_Int (getInt Int))
   (O_Addr (getAddr Addr))
   (defObj)
  )
))

(declare-fun I1 (Heap) Bool)
(declare-fun I2 (Heap Addr) Bool)
(declare-fun I3 (Heap Addr) Bool)
(declare-fun I4 (Heap Addr) Bool)

(assert (I1 (as heap.empty Heap)))

(assert (forall ((h Heap)) (=>
            (I1 h)
            (I2 (heap.heapAddrPair_1 (heap.alloc h (O_Int 0)))
                (heap.heapAddrPair_2 (heap.alloc h (O_Int 0)))
                ))))
(assert (forall ((h Heap)) (=>
            (I1 h)
            (I3 (heap.heapAddrPair_1 (heap.alloc h (O_Int 1)))
                (heap.heapAddrPair_2 (heap.alloc h (O_Int 1)))
                ))))

(assert (forall ((h Heap) (a Addr)) (=>
            (I2 h a)
            (I4 h a))))
(assert (forall ((h Heap) (a Addr)) (=>
            (I3 h a)
            (I4 h a))))

(assert (forall ((h Heap) (a Addr)) (=>
            (and (I4 h a) (>= (getInt (heap.read h a)) 0)) false)))

