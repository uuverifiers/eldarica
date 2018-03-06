(set-logic HORN)

(declare-fun Inv (Int Int) Bool)

(assert (Inv 5 1))
(assert (forall ((x Int) (y Int)) (=> (Inv x y) (Inv x (* x y)))))

(assert (forall ((x Int) (y Int)) (=> (Inv x y) (> y 0))))

(check-sat)
