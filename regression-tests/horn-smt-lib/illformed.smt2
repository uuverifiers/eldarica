; Input that should be rejected, no Horn clauses

(set-logic UFLIA)
(declare-fun n () Int)

(assert (and (> n 1) (not (= (- n 1) 1))))

(check-sat)
(get-model)