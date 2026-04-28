(set-logic HORN)

(declare-fun I1 ((_ BitVec 32)) Bool)
(declare-fun I2 ((_ BitVec 32)) Bool)
(declare-fun I3 ((_ BitVec 32)) Bool)
(declare-fun I4 ((_ BitVec 32)) Bool)

(assert (I1 (_ bv10 32)))

(assert (forall ((x (_ BitVec 32))) (=> (I1 x) (I2 x))))
(assert (forall ((x (_ BitVec 32))) (=> (I1 x) (I3 x))))
(assert (forall ((x (_ BitVec 32))) (=> (I2 x) (I4 x))))
(assert (forall ((x (_ BitVec 32))) (=> (I3 x) (I4 x))))

(assert (forall ((x (_ BitVec 32))) (=> (I4 x) (= x (_ bv10 32)))))

(check-sat)

