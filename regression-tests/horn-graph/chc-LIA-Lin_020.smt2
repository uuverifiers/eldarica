; vmt-chc-benchmarks/./lustre/durationThm_3_e1_36_e7_432_000.smt2
(set-logic HORN)

(declare-fun |state| ( Int Int Bool Bool Int Int Int Int Bool Int Int Int Int Bool Int Int Bool Bool Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Int) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Int) (U Int) ) 
    (=>
      (and
        (let ((a!1 (or (not M) (<= (+ N (* (- 1) T) (* (- 1) S)) 0)))
      (a!2 (and (or Q (not (<= S R))) (<= U T) (<= 1 S) (<= 1 T))))
  (and (= F S)
       (= K 0)
       (= K N)
       (= H T)
       (= H G)
       (= I 0)
       (= I R)
       (= J 0)
       (= J U)
       (= a!1 L)
       (= E a!2)
       (= E O)
       (= O M)
       (= F A)))
      )
      (state K N E O J U I R M H T F S L G A Q P B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Bool) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Bool) (P Bool) (Q Int) (R Bool) (S Int) (T Int) (U Int) (V Bool) (W Int) (X Int) (Y Int) (Z Int) (A1 Bool) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Bool) (G1 Int) (H1 Bool) (I1 Bool) (J1 Int) (K1 Bool) (L1 Bool) (M1 Int) (N1 Int) (O1 Int) (P1 Int) ) 
    (=>
      (and
        (state N Q H R M P1 L M1 P K O1 I N1 O J A L1 V B C D)
        (let ((a!1 (or (not P) (<= (+ Q (* (- 1) O1) (* (- 1) N1)) 0)))
      (a!2 (or (not I1) (<= (+ J1 (* (- 1) D1) (* (- 1) C1)) 0)))
      (a!3 (and (or A1 (not (<= C1 B1))) (<= E1 D1) (<= 1 D1) (<= 1 C1)))
      (a!4 (or (not L1) (= (+ P1 (* (- 1) X)) (- 2))))
      (a!5 (or (not V) (= (+ M1 (* (- 1) U)) (- 2))))
      (a!6 (or (not V) (= (+ Q (* (- 1) W)) (- 2)))))
  (and (= N1 S)
       (= Y U)
       (= Z X)
       (= B1 Y)
       (= C1 S)
       (= D1 T)
       (= E1 Z)
       (= G1 W)
       (= N Q)
       (= M P1)
       (= L M1)
       (= K O1)
       (= I N1)
       (= J1 G1)
       (= a!1 O)
       (= a!2 H1)
       (= F1 (or R a!3))
       (= R P)
       (= H R)
       (= K1 F1)
       (= K1 I1)
       a!4
       (or L1 (= X 0))
       a!5
       a!6
       (or V (= U 0))
       (or V (= W 0))
       (= O1 T)))
      )
      (state G1 J1 F1 K1 Z E1 Y B1 I1 T D1 S C1 H1 G F A1 E U X W)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Int) (O Bool) (P Bool) (Q Bool) (R Int) (S Int) (T Int) (U Int) ) 
    (=>
      (and
        (state K N E O J U I R M H T F S L G A Q P B C D)
        (not L)
      )
      false
    )
  )
)

(check-sat)
(exit)
