(set-logic HORN)

(declare-fun I (Real) Bool)

(assert (I 1.0))
(assert (forall ((x Real)) (=> (I x) (I (/ x 2)))))
(assert (forall ((x Real)) (=> (I x) (> x 0.1))))

(check-sat)
