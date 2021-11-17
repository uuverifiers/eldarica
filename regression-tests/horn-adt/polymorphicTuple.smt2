
(set-logic HORN)

(declare-datatypes ( ( Pair 2 ) ) (
  (par (S T) ( ( Pair ( first S ) ( second T ) )))))

(declare-fun p1 ((Pair Int Int) Int) Bool)

(assert (p1 (Pair 1 2) 42))
(assert (forall ((p (Pair Int Int)) (x Int))
     (=> (p1 p x) (p1 (Pair (+ (first p) 1) (- (second p) 1)) (+ x 1)))))
(assert (forall ((p (Pair Int Int)) (x Int))
     (=> (p1 p x) (> x 0))))

(check-sat)
