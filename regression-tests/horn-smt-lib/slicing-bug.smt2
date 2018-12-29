; Case in which the slicer previously, erroneously removed the
; first argument of p

(set-logic HORN)

(declare-fun p (Int Int) Bool)

(assert (forall ((x Int) (y Int)) (=> (>= x y) (p x y))))
(assert (forall ((x Int) (y Int)) (=> (p x y) (p x (- y 1)))))
(assert (forall ((x Int)) (=> (p x (+ x 4)) false)))

(check-sat)
