
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (inv 0))
(assert (forall ((I Int)) (=> (and (<= I 1000) (inv I)) (inv (+ I 1)))))
(assert (forall ((I Int)) (=> (inv I) (<= I 10000))))
(check-sat)
(get-model)
