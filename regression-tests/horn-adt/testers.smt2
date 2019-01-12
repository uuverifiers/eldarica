
(set-logic HORN)

(declare-datatype XS ( (XS_empty)
                        (XS_cons (XS_head Int) (XS_tail XS)) ))

(declare-fun p1 (XS) Bool)

(assert (forall ((x XS)) (=> (is-XS_cons x) (p1 x))))
(assert (forall ((x XS)) (=> (and (p1 x) (= x XS_empty)) false)))

(check-sat)

