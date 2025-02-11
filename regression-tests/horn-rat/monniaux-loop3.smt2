
(set-logic HORN)
(declare-fun inv (Real Real) Bool)
(assert (inv 0.0 0.0))
(assert (forall ((I Real) (J Real)) (or (> I 1000.0) (not (inv I J)) (inv (+
I 1.0) (+ J 2.0)))))
(assert (forall ((I Real) (J Real)) (=> (inv I J) (<= J 3000.0))))
(check-sat)
(get-model)
