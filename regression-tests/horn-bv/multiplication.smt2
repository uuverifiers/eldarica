(set-logic HORN)

(declare-fun R1 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) Int) Bool)
(declare-fun R2 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) Int) Bool)
(declare-fun R3 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) Int) Bool)
(declare-fun R4 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) Int) Bool)

(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (c Int))
   (=> (= c 32) (R1 x y z c))))
   
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (c Int))
   (=> (and (not (= c 32)) (R1 x y z c)) (R2 x y z c))))

(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (c Int))
   (=> (and (= (bvand x (_ bv1 32)) (_ bv1 32)) (R2 x y z c)) (R3 x y z c))))

(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (zp (_ BitVec 32)) (c Int))
   (=> (and (= zp (bvadd z y)) (R3 x y z c)) (R4 x y zp c))))
   
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (c Int))
   (=> (and (not (= (bvand x (_ bv1 32)) (_ bv1 32))) (R2 x y z c)) (R4 x y z c))))
   
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (c Int) (cp Int))
   (=> (and (= cp (- cp 1)) (R4 x y z c)) (R1 x y z cp))))

(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) (z (_ BitVec 32)) (c Int))
   (=> (and (= c 0) (not (= z (bvmul x y))) (R1 x y z c)) false)))

(check-sat)
