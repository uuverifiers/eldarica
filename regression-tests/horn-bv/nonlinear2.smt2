(set-logic HORN)

(declare-fun Inv ((_ BitVec 32) (_ BitVec 32)) Bool)

(assert (forall ((x (_ BitVec 32))) (=> (and (bvsge x (_ bv2 32)) (bvsle x (_ bv5 32))) (Inv x (_ bv1 32)))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) (=> (Inv x y) (Inv x (bvmul x y)))))

(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32))) (=> (Inv x y) (bvsgt y (_ bv0 32)))))

(check-sat)
