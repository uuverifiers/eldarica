(set-logic HORN)

(declare-fun I (Real) Bool)

(assert (I 1.0))
(assert (forall ((x Real)) (=> (I x) (I (/ x 2)))))
(assert (not (I 0.0)))

(check-sat)
