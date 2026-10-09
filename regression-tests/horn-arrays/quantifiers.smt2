(set-logic HORN)
(define-fun arrayEq ((ar1 (Array Int Int)) (ar2 (Array Int Int))) Bool (forall ((i Int)) (= (select ar1 i) (select ar2 i))))

(assert (forall (
         (j (Array Int Int))
         (o (Array Int Int))
        )
    (=> (and (arrayEq j o) (= 1 (select o 1)) (= j (store (store o 0 0) 0 0))) false)))

(check-sat)

