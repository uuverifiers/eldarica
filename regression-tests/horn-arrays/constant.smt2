(set-logic HORN)

(declare-fun inv ((Array Int Int)) Bool)

(assert (inv ((as const (Array Int Int)) 10)))
(assert (forall ((a (Array Int Int)))
         (=> (inv a) (inv (store a 1 5)))))
(assert (forall ((a (Array Int Int)) (i Int))
         (=> (inv a) (>= (select a i) 0))))

(check-sat)
