(set-logic HORN)

(declare-datatype Pair ( (P (left Int) (right Bool)) ))

(declare-fun I1 (Pair) Bool)
(declare-fun I2 (Pair) Bool)

(assert (I1 (P 0 true)))
(assert (forall ((p Pair))
           (=> (I1 p) (I2 (P (+ (left p) 1) (not (right p)))))))
(assert (forall ((p Pair))
           (=> (I2 p) (I1 (P (* (left p) 2) (not (right p)))))))

(assert (forall ((p Pair))
           (=> (I1 p) (and (>= (left p) 0) (right p)))))

(check-sat)
