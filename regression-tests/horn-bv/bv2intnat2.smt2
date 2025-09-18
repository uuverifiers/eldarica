(set-logic HORN)
(declare-fun foo ((_ BitVec 1)) Bool)
(declare-fun bar (Int Int) Bool)
(assert (foo (_ bv1 1)))

; sbt_to_int: cast from signed bit-vectors to ints
; ubv_to_int: cast from unsigned bit-vectors to ints
(assert
  (forall
    ((x (_ BitVec 1)))
    (=> (foo x) (bar (sbv_to_int x) (ubv_to_int x)))))

(assert
  (forall
    ((x Int) (y Int))
    (=> (bar x y) (and (= ((_ int_to_bv 1) x) (_ bv1 1))
                       (= ((_ int_to_bv 1) y) (_ bv1 1))))))
(assert
  (forall
    ((x Int) (y Int))
    (=> (bar x y) (distinct x y))))
(check-sat)
(get-model)
