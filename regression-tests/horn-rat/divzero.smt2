; Example for which Eldarica previously produced the result unsat, since
; the division operator was not handled correctly

(set-logic HORN)

(declare-fun |invariant| ( Real  ) Bool)

(assert (invariant 1.0))
(assert (forall ((x Real)) (=> (invariant x) (< (/ x 2.0) 0))))

(check-sat)