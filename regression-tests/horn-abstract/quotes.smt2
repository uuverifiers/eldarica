
(set-logic HORN)
(declare-fun |inv:0| (Int Int) Bool)
(assert (|inv:0| 0 0))
(assert (forall ((I Int) (J Int)) (or (> I 1000) (not (|inv:0| I J)) (|inv:0| (+
I 1) (+ J 2)))))
(assert (forall ((I Int) (J Int)) (=> (|inv:0| I J) (<= J 3000))))
(check-sat)
(get-model)
