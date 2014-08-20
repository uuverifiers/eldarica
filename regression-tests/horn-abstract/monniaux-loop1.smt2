
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (inv 0 0))
(assert (forall ((I Int) (J Int)) (or (> I 1000) (not (inv I J)) (inv (+
I 1) (+ J 2)))))
(assert (forall ((I Int) (J Int)) (=> (inv I J) (<= J 3000))))
(check-sat)
(get-model)
