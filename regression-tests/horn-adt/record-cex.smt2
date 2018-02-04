(set-logic HORN)

(declare-datatype ArRec0 ( (ArRec0 (default Int)) ))

(define-fun storeRec0 ((new ArRec0) (old ArRec0) (ind Int) (val Int)) Bool
   (and (= val (default old)) (= old new)))
(define-fun selectRec0 ((rec ArRec0) (ind Int)) Int
   (default rec))

(declare-fun p0 ( Int ArRec0 ArRec0) Bool)
(declare-fun p1 ( Int ArRec0 ArRec0 Int) Bool)
(declare-fun p2 ( Int ArRec0 ArRec0 Int) Bool)
(declare-fun p3 ( Int ArRec0 ArRec0 Int) Bool)
(declare-fun p4 ( Int ArRec0 ArRec0 Int) Bool)
(declare-fun p5 ( Int ArRec0 ArRec0) Bool)
(declare-fun p6 ( Int ArRec0 ArRec0 Int) Bool)
(declare-fun p7 ( Int ArRec0 ArRec0 Int) Bool)
(declare-fun p8 ( Int ArRec0 ArRec0) Bool)

(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0))(=> (= n 1) (p0 n a1 a2))))
(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0) (a Int))(=> (and (p0 n a1 a2) (= a 0)) (p1 n a1 a2 a))))
(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0) (a Int))(=> (and (p1 n a1 a2 a) (<= a (- n 1))) (p2 n a1 a2 a))))
(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0) (a Int) (a1_p ArRec0))(=> (and (p2 n a1 a2 a) (storeRec0 a1_p a1 a 1)) (p3 n a1_p a2 a))))
(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0) (a Int) (a2_p ArRec0))(=> (and (p3 n a1 a2 a) (storeRec0 a2_p a2 a 1)) (p4 n a1 a2_p a))))

(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0) (a Int))(=> (p4 n a1 a2 a) (let ((ap (+ a 1))) (p1 n a1 a2 ap)))))

(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0) (a Int))(=> (and (p1 n a1 a2 a) (>= a n)) (p5 n a1 a2))))

(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0) (a Int))(=> (and (p5 n a1 a2) (= a 0)) (p6 n a1 a2 a))))
(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0) (a Int))(=> (and (p6 n a1 a2 a) (<= a (- n 1))) (p7 n a1 a2 a))))
(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0) (a Int))(=> (p7 n a1 a2 a) (not (= (selectRec0 a1 a) (selectRec0 a2 a))))))
(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0) (a Int))(=> (and (p6 n a1 a2 a) (>= a n)) (p8 n a1 a2))))

(assert (forall ( (n Int) (a1 ArRec0) (a2 ArRec0) (a Int))(=> (p7 n a1 a2 a) (let ((ap (+ a 1))) (p6 n a1 a2 ap)))))

(check-sat)
