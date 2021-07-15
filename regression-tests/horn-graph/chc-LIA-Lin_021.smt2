; vmt-chc-benchmarks/./lustre/durationThm_2_e7_145_000.smt2
(set-logic HORN)

(declare-fun |state| ( Int Int Bool Bool Int Int Int Int Bool Int Int Bool Bool Bool Int Bool Bool Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Bool) (L Int) (M Bool) (N Bool) (O Bool) (P Int) (Q Int) (R Bool) (S Int) (T Bool) ) 
    (=>
      (and
        (let ((a!1 (= (or (not K) (and R T) (not (<= Q L))) J))
      (a!2 (and (or R (not (<= Q P))) (or T (not (<= Q S))) (<= 1 Q))))
  (and (= I L)
       (= G Q)
       (= G F)
       (= A 0)
       (= A S)
       (= H 0)
       (= H P)
       a!1
       (= E a!2)
       (= E M)
       (= M K)
       (= I 0)))
      )
      (state I L E M H P A S K G Q R T J F O N B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Bool) (H Bool) (I Int) (J Int) (K Int) (L Int) (M Bool) (N Bool) (O Int) (P Bool) (Q Int) (R Bool) (S Int) (T Bool) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Bool) (B1 Int) (C1 Bool) (D1 Bool) (E1 Int) (F1 Bool) (G1 Bool) (H1 Int) (I1 Bool) (J1 Int) (K1 Int) (L1 Bool) (M1 Int) (N1 Bool) ) 
    (=>
      (and
        (state L O H P K J1 A M1 N J K1 L1 N1 M I T R B C D)
        (let ((a!1 (= (or (not N) (and L1 N1) (not (<= K1 O))) M))
      (a!2 (= (or (not G1) (and C1 A1) (not (<= Z H1))) F1))
      (a!3 (and (or C1 (not (<= Z B1))) (or A1 (not (<= Z Y))) (<= 1 Z)))
      (a!4 (or (not R) (not T) (= (+ O (* (- 1) S)) (- 1))))
      (a!5 (or (not T) (= (+ J1 (* (- 1) V)) (- 1))))
      (a!6 (or (not R) (= (+ M1 (* (- 1) Q)) (- 1)))))
  (and (= W Q)
       (= X V)
       (= Y X)
       (= Z U)
       (= B1 W)
       (= E1 S)
       (= L O)
       (= K J1)
       (= J K1)
       (= H1 E1)
       (= A M1)
       a!1
       a!2
       (= D1 (or P a!3))
       (= P N)
       (= H P)
       (= I1 D1)
       (= I1 G1)
       a!4
       (or (and R T) (= S 0))
       a!5
       (or T (= V 0))
       a!6
       (or R (= Q 0))
       (= K1 U)))
      )
      (state E1 H1 D1 I1 X Y W B1 G1 U Z A1 C1 F1 F E G Q V S)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Bool) (K Bool) (L Int) (M Bool) (N Bool) (O Bool) (P Int) (Q Int) (R Bool) (S Int) (T Bool) ) 
    (=>
      (and
        (state I L E M H P A S K G Q R T J F O N B C D)
        (not J)
      )
      false
    )
  )
)

(check-sat)
(exit)
