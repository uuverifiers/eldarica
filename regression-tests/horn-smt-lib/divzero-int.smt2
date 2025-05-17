
(set-logic HORN)

(declare-fun |invariant| ( Int Int ) Bool)

(assert (invariant 1 2))
(assert (forall ((x Int) (y Int)) (=> (invariant x y) (< (div x y) 0))))

(check-sat)
