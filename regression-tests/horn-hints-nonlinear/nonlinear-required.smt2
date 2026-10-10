; Problem where invariant y = x*x is genuinely required
; Without the template hint providing (* x x), Eldarica returns unknown
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 1) (= y 1)) (inv x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (inv x y) (= x1 (+ x 1)) (= y1 (+ y (+ (* 2 x) 1))))
      (inv x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (not (= y (* x x)))) false)))
(check-sat)
