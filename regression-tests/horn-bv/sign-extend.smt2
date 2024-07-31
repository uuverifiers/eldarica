; Problem that is sat; due to incorrect handling of sign_extend,
; Eldarica reported unsat in earlier versions.

(set-logic HORN)
(declare-fun foo ((_ BitVec 1)) Bool)
(declare-fun bar ((_ BitVec 2)) Bool)
(assert (foo (_ bv1 1)))
(assert
  (forall
    ((x (_ BitVec 1)))
    (=> (foo x) (bar ((_ sign_extend 1) x)))))
(assert
  (forall
    ((x (_ BitVec 2)))
    (=> (bar x) (= x (_ bv3 2)))))
(check-sat)
(get-model)
