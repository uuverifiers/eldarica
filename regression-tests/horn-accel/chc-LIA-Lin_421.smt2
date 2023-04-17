; ./sv-comp/./2015-05-26/LIA/Eldarica/linear-tree-like/amotsa.smt2-0001_000.smt2
(set-logic HORN)

(declare-fun |predh11_1| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (v_38 Int) (v_39 Int) (v_40 Int) (v_41 Int) (v_42 Int) (v_43 Int) (v_44 Int) (v_45 Int) (v_46 Int) (v_47 Int) (v_48 Int) (v_49 Int) (v_50 Int) (v_51 Int) (v_52 Int) (v_53 Int) (v_54 Int) (v_55 Int) (v_56 Int) (v_57 Int) (v_58 Int) (v_59 Int) ) 
    (=>
      (and
        (and (= B (+ (- 1) J))
     (= D (+ O (* (- 1) N)))
     (= E (+ (- 1) J))
     (= F (+ O (* (- 1) N)))
     (= G (+ (- 1) J))
     (= C (+ (- 1) J))
     (<= 1 Q)
     (<= 0 (+ (* (- 1) Q) J))
     (= A (+ (- 1) J))
     (= v_38 Y)
     (= v_39 X)
     (= v_40 W)
     (= v_41 V)
     (= v_42 U)
     (= v_43 T)
     (= v_44 S)
     (= v_45 R)
     (= v_46 Q)
     (= v_47 P)
     (= 1 v_48)
     (= v_49 M)
     (= v_50 L)
     (= v_51 K)
     (= 1 v_52)
     (= 1 v_53)
     (= 1 v_54)
     (= 1 v_55)
     (= 1 v_56)
     (= v_57 J)
     (= v_58 I)
     (= v_59 H))
      )
      (predh11_1 Y
           X
           W
           V
           U
           G
           T
           S
           R
           Q
           P
           F
           L1
           K1
           J1
           M
           L
           K
           I1
           H1
           G1
           F1
           E1
           D1
           C1
           B1
           A1
           Z
           I
           H
           v_38
           v_39
           v_40
           v_41
           v_42
           E
           v_43
           v_44
           v_45
           v_46
           v_47
           D
           v_48
           O
           N
           v_49
           v_50
           v_51
           v_52
           C
           v_53
           B
           v_54
           J
           v_55
           A
           v_56
           v_57
           v_58
           v_59)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) ) 
    (=>
      (and
        (predh11_1 H2
           G2
           F2
           E2
           D2
           C2
           B2
           A2
           Z1
           Y1
           X1
           W1
           V1
           U1
           T1
           S1
           R1
           Q1
           P1
           O1
           N1
           M1
           L1
           K1
           J1
           I1
           H1
           G1
           F1
           E1
           D1
           C1
           B1
           A1
           Z
           Y
           X
           W
           V
           U
           T
           S
           R
           Q
           P
           O
           N
           M
           L
           K
           J
           I
           H
           G
           F
           E
           D
           C
           B
           A)
        (and (<= 0 (+ U (* (- 1) H))) (<= 0 (+ Y (* (- 1) R))) (<= 1 (+ U (* (- 1) G))))
      )
      false
    )
  )
)

(check-sat)
(exit)
