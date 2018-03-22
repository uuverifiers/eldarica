(set-logic HORN)

(declare-fun Inv ((_ BitVec 32) (_ BitVec 32)) Bool)

(assert (forall ((x (_ BitVec 32)))
   (=> (bvult x (_ bv100000 32)) (Inv x (_ bv0 32)))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
   (=> (and (Inv x y) (bvult y x)) (Inv x (bvadd (_ bv1 32) y)))))
(assert (forall ((x (_ BitVec 32)))
   (=> (Inv x (_ bv200000 32)) false)))

(check-sat)
