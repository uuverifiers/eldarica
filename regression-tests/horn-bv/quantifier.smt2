(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
; (set-info :status unknown)
(declare-fun inv_main4 ((_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun inv_main5 ((_ BitVec 32) (_ BitVec 32)) Bool)
(assert (forall ((var0 (_ BitVec 32))) (inv_main4 (_ bv0 32) var0 ) ) )
(assert (forall ((var0 (_ BitVec 32))) (forall ((var1 (_ BitVec 32))) (or (not (and (inv_main4 var1 var0 ) (not (bvsle (_ bv0 32) (bvadd (bvadd var0 (bvmul (bvneg (_ bv1 32)) var1 ) ) (bvneg (_ bv1 32)) ) ) ) ) ) (inv_main5 var1 var0 ) ) ) ) )
(assert (forall ((var0 (_ BitVec 32))) (forall ((var1 (_ BitVec 32))) (or (not (and (inv_main4 var1 var0 ) (bvsle (_ bv0 32) (bvadd (bvadd var0 (bvmul (bvneg (_ bv1 32)) var1 ) ) (bvneg (_ bv1 32)) ) ) ) ) (inv_main4 (bvadd var1 (_ bv2 32) ) var0 ) ) ) ) )
(assert (forall ((var0 (_ BitVec 32))) (forall ((var1 (_ BitVec 32))) (not (and (inv_main5 var1 var0 ) (forall ((var2 (_ BitVec 32))) (or (not (and (and (and (and (bvsle (_ bv0 32) (bvadd (bvadd (_ bv2 32) (bvmul (bvneg (_ bv1 32)) var2 ) ) (bvneg (_ bv1 32)) ) ) (bvsle (_ bv0 32) (bvadd (bvadd (_ bv2 32) (bvmul (_ bv1 32) var2 ) ) (bvneg (_ bv1 32)) ) ) ) (or (not (bvsle (_ bv0 32) (bvadd var2 (bvneg (_ bv1 32)) ) ) ) (bvsle (_ bv0 32) (bvadd var1 (bvneg (_ bv1 32)) ) ) ) ) (or (not (bvsle (_ bv0 32) (bvadd (bvmul (bvneg (_ bv1 32)) var2 ) (bvneg (_ bv1 32)) ) ) ) (bvsle (_ bv0 32) (bvadd (bvmul (bvneg (_ bv1 32)) var1 ) (bvneg (_ bv1 32)) ) ) ) ) (exists ((var3 (_ BitVec 32))) (= var1 (bvadd (bvmul (_ bv2 32) var3 ) var2 ) ) ) ) ) (= var2 (_ bv0 32) ) ) ) ) ) ) ) )
(check-sat)
