; Same linear problem, but hint uses initial-predicates with (* x x)
; EXPECTED: error "key not found: mul/3" — documents that non-linear
; predicates in initial-predicates form crash the solver pipeline
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x1 Int)) (=> (and (inv x) (= x1 (+ x 1))) (inv x1))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
