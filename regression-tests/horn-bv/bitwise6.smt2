

(declare-fun p ((_ BitVec 32)) Bool)
(declare-fun q ((_ BitVec 32)) Bool)

(assert (forall ((x (_ BitVec 32))) (p x)))
(assert (forall ((x (_ BitVec 32))) (=> (p x) (q (bvand x (bvadd (_ bv4 32) (_ bv10 32)))))))
(assert (forall ((x (_ BitVec 32))) (=> (q x) (= x (_ bv0 32)))))

(check-sat)

