(set-logic HORN)

(declare-fun Inv (Bool Bool (Array Int Int) (Array Int Bool) (_ BitVec 32)) Bool)

(check-sat)