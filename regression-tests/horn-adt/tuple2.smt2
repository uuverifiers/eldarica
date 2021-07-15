
(set-logic HORN)

(declare-datatype Pair ( (Pair (first Int) (second Int)) ))

(declare-fun p1 (Pair Int) Bool)

(assert (p1 (Pair 1 2) 5))
(assert (forall ((p Pair) (x Int))
     (=> (p1 p x) (p1 (Pair (+ (first p) 1) (- (second p) 1)) (- x 1)))))
(assert (forall ((p Pair) (x Int))
     (=> (p1 p x) (> x 0))))

(check-sat)
