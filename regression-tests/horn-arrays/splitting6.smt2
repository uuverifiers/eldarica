; Example in which Eldarica previously incorrectly cloned arrays; cloning
; and nested arrays do not mix well

(set-logic HORN)

(declare-fun atom1 () Bool)
(declare-fun atom3 () Bool)
(declare-fun pred ((Array Int (Array Int Int))) Bool)

(assert (forall ((arr (Array Int (Array Int Int)))) (pred arr)))
(assert (forall ((arr (Array Int (Array Int Int)))) (pred arr)))
(assert (forall ((arr (Array Int (Array Int Int))))
    (=> (and (pred arr) (= (select (select arr 0) 0) 0)) atom1)))
(assert (forall ((arr1 (Array Int (Array Int Int))) (arr2 (Array Int (Array Int Int))))
    (=>  (and (= (select (select arr1 0) 8) 0) 
              (= (store arr2 0 (store (select arr2 0) 8 4)) arr1)) atom3)))
(assert (=> (and atom1 atom3) false))

(check-sat)