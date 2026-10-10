; Linear problem solved via CEGAR even without hints
; Used to test that non-linear TEMPLATE hints do not break a simple solve
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (inv x) (= x1 (+ x 1))) (inv x1))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
