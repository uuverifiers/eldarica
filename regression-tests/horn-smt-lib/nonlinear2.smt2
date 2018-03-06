(set-logic HORN)

(declare-fun Inv (Int Int) Bool)

(assert (forall ((x Int)) (=> (and (>= x 2) (<= x 5)) (Inv x 1))))
(assert (forall ((x Int) (y Int)) (=> (Inv x y) (Inv x (* x y)))))

(assert (forall ((x Int) (y Int)) (=> (Inv x y) (> y 0))))

(check-sat)
