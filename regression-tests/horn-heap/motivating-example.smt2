(declare-heap
 Heap
 Addr
 Object
 O_Empty                                   ; the default Object
 ((Object 0) (IntList 0) (Cons 0) (Nil 0))
 (((O_Cons (getCons Cons))
   (O_Nil (getNil Nil))
   (O_Empty))
  ((IntList (size Int)))
  ((Cons (parentCons IntList) (hd Int) (tl Addr)))
  ((Nil (parentNil IntList)))))
                                           ; invariant declarations
(declare-fun I1 (Heap)      Bool)          ; <h>
(declare-fun I2 (Heap Addr) Bool)          ; <h,p>
(declare-fun I3 (Heap Addr) Bool)          ; <h,l>
(declare-fun I4 (Heap Addr) Bool)          ; <h,l>

(assert (I1 emptyHeap))
(assert (forall ((h Heap) (h1 Heap) (p1 Addr) (ar AllocResHeap))
  (=> (and (I1 h) (= ar (alloc h (O_Nil (Nil (IntList 0))))))
     (I2 h1 p1))))
(assert (forall ((h Heap) (h1 Heap) (p1 Addr))
                (=> (and (I1 h) (= (AllocResHeap h1 p1) (alloc h (O_Nil (Nil (IntList 0))))))
                   (I2 h1 p1))))
(assert (forall ((h Heap) (h1 Heap) (p Addr) (p1 Addr))
  (=> (and (I2 h p)
           (= (AllocResHeap h1 p1) (alloc h (O_Cons (Cons (IntList 1) 42 p)))))
      (I3 h1 p1))))
(assert (forall ((h Heap) (h1 Heap) (l Addr) (head Int) (tail Addr)
                 (prn IntList))
  (=> (and (I3 h l) (= h1 (write h l (O_Cons (Cons prn (+ 1 head) tail))))
           (= (O_Cons (Cons prn head tail)) (read h l))) (I4 h1 l))))
(assert (forall ((h Heap) (l Addr) (prn IntList))
  (=> (and (I3 h l) (= (O_Nil (Nil prn)) (read h l))) false)))
(assert (forall ((h Heap) (l Addr) (head Int) (tail Addr) (prn IntList))
  (=> (and (I4 h l) (= (O_Cons (Cons prn head tail)) (read h l))
           (not (= head 43))) false)))
(assert (forall ((h Heap) (l Addr))
  (=> (and (I4 h l) (not (is-O_Cons (read h l)))) false)))
(assert (forall ((h Heap) (l Addr))
  (=> (and (I4 h l) (not (valid h l))) false)))
