
(set-logic HORN)

(declare-fun Inv ((_ BitVec 8) (_ BitVec 8)) Bool)

(assert (Inv (_ bv5 8) (_ bv5 8)))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
     (=> (Inv x y)
         (Inv y (concat (bvadd ((_ extract 7 4) y) (_ bv3 4))
                        (bvadd ((_ extract 3 0) y) (_ bv3 4)))))))

(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
     (=> (Inv x y) (bvuge y x))))

(check-sat)
