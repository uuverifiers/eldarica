

(declare-fun p (Bool) Bool)
(declare-fun q (Bool) Bool)

(assert (forall ((x Bool)) (p x)))
(assert (forall ((x Bool)) (=> (p x) (q (distinct x true)))))
(assert (forall ((x Bool)) (=> (q x) x)))

(check-sat)

