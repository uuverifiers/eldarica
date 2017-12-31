(set-logic HORN)

(declare-fun Inv (Bool Bool) Bool)

(assert (Inv true true))
(assert (forall ((x Bool) (y Bool)) (=> (Inv x y) (Inv (not x) (not y)))))
(assert (forall ((x Bool) (y Bool)) (=> (Inv x y) (= x y))))

(check-sat)


