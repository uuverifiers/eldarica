(set-logic HORN)
(declare-fun foo ((_ BitVec 1)) Bool)
(declare-fun bar (Int Int) Bool)
(assert (foo (_ bv1 1)))

; bv2int: cast from signed bit-vectors to ints
; bv2nat: cast from unsigned bit-vectors to ints
(assert
  (forall
    ((x (_ BitVec 1)))
    (=> (foo x) (bar (bv2int x) (bv2nat x)))))

; int2bv and nat2bv have the same semantics
(assert
  (forall
    ((x Int) (y Int))
    (=> (bar x y) (= ((_ int2bv 1) x) (_ bv1 1))
                  (= ((_ nat2bv 1) y) (_ bv1 1)))))
(assert
  (forall
    ((x Int) (y Int))
    (=> (bar x y) (distinct x y))))
(check-sat)
(get-model)
