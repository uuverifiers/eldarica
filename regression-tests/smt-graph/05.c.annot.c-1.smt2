(set-logic HORN)
(set-info :source |
    Benchmark: C_VC
    Output by Princess (http://www.philipp.ruemmer.org/princess.shtml)
|)
(set-info :status unknown)
(declare-fun inv_main19 (Int Int Int Int Int) Bool)
(declare-fun inv_main6 (Int Int Int Int Int) Bool)
(assert (forall ((var0 Int)) (inv_main6 var0 0 0 0 0)))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int)) (or (not (and (inv_main6 var2 var4 var1 var0 var3) (and (not (= var2 0)) (not (= var5 0))))) (inv_main6 var2 (+ var4 1) (+ var1 1) (+ (+ var0 (+ var1 1)) 1) (+ var3 (+ var4 1))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int)) (or (not (and (inv_main6 var2 var4 var1 var0 var3) (and (= var2 0) (not (= var5 0))))) (inv_main6 var2 (+ var4 1) (+ var1 1) (+ var0 (+ var1 1)) (+ var3 (+ var4 1))))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int) (var5 Int)) (or (not (and (inv_main6 var2 var4 var1 var0 var3) (and (not (<= 0 (+ var0 (* (- 1) var3)))) (= var5 0)))) (inv_main19 var2 var4 var1 var0 var3))))
(assert (forall ((var0 Int) (var1 Int) (var2 Int) (var3 Int) (var4 Int)) (not (inv_main19 var2 var4 var1 var0 var3))))
(check-sat)
