; vmt-chc-benchmarks/./lustre/fast_1_e8_747_e7_692_000.smt2
(set-logic HORN)

(declare-fun |state| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Bool) (R1 Int) (S1 Bool) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Bool) (D2 Bool) (E2 Bool) (F2 Bool) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) ) 
    (=>
      (and
        (let ((a!1 (= (or (and (not C1) (not A2) B2)
                  (and (not C1) A2 (not B2))
                  (and C1 (not A2) (not B2)))
              C2)))
  (and (= (and (not T1) S1 (not P1) O1 N1 M1 S Q1 (<= R1 200) (<= 35 R1)) F1)
       (= K2 J1)
       (= J2 U)
       (= H2 (not G2))
       (= H2 V)
       (= D2 W1)
       (= C2 V1)
       (= B L1)
       (= C Q1)
       (= F D2)
       (= G I1)
       (= I Y)
       (= J Z)
       (= M X)
       (= O W)
       (= Q P)
       (= S I2)
       (= S R)
       (= U T)
       (= F1 F2)
       (= H1 B1)
       (= E S1)
       (= A K1)
       (= U1 E1)
       (or (not E1) D1 (not F2))
       (or (not W1) (not V1) (= U1 A1))
       (or (and E1 F2) (= D1 E2))
       (or (not E2) F2)
       (or (not W) (= (or Z Y X) Q))
       (or W Q)
       (or (not C1) (= B1 A1))
       (or C1 A1)
       (or (not I1) (= H1 G1))
       (or I1 (= H1 H))
       (or (not U1) (and W1 V1))
       (not K2)
       (not J2)
       (not I2)
       (not B)
       (not C)
       (not D)
       (= F true)
       (not G)
       (not I)
       (not J)
       (not M)
       (not O)
       (= H true)
       (not E)
       (not A)
       a!1))
      )
      (state J
       Z
       I
       Y
       M
       X
       O
       W
       H1
       B1
       G
       I1
       H
       B2
       A2
       C1
       C2
       F
       D2
       W1
       V1
       U1
       A1
       E1
       E
       S1
       C
       Q1
       T1
       R1
       P1
       S
       O1
       N1
       M1
       F1
       B
       L1
       A
       K1
       K2
       J1
       G1
       F2
       D1
       E2
       J2
       U
       I2
       Q
       H2
       V
       T
       R
       P
       D
       G2
       Z1
       Y1
       X1
       K
       L
       N)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Bool) (R1 Int) (S1 Bool) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Bool) (D2 Bool) (E2 Bool) (F2 Bool) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Bool) (W2 Bool) (X2 Bool) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Bool) (C3 Bool) (D3 Bool) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Bool) (N3 Bool) (O3 Bool) (P3 Bool) (Q3 Bool) (R3 Bool) (S3 Bool) (T3 Bool) (U3 Bool) (V3 Bool) (W3 Bool) (X3 Bool) (Y3 Bool) (Z3 Bool) (A4 Bool) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Bool) (L4 Bool) (M4 Bool) (N4 Bool) (O4 Bool) (P4 Bool) (Q4 Bool) (R4 Bool) (S4 Bool) (T4 Bool) (U4 Bool) (V4 Bool) ) 
    (=>
      (and
        (state J
       Z
       I
       Y
       M
       X
       O
       W
       H1
       B1
       G
       I1
       H
       M4
       L4
       C1
       N4
       F
       O4
       W1
       V1
       U1
       A1
       E1
       E
       S1
       C
       Q1
       T1
       R1
       P1
       S
       O1
       N1
       M1
       F1
       B
       L1
       A
       K1
       V4
       J1
       G1
       Q4
       D1
       P4
       U4
       U
       T4
       Q
       S4
       V
       T
       R
       P
       D
       R4
       S2
       P2
       L2
       K
       L
       N)
        (let ((a!1 (= (or (and (not C1) (not L4) M4)
                  (and (not C1) L4 (not M4))
                  (and C1 (not L4) (not M4)))
              N4))
      (a!2 (or (not K4) (and (not Y1) (not X1) (or (not S) (not Z1)))))
      (a!3 (= (or (and (not F3) (not D3) B3)
                  (and (not F3) D3 (not B3))
                  (and F3 (not D3) (not B3)))
              H4)))
  (and a!1
       (= (and (not D4) C4 A4 (not Z3) Y3 X3 W3 W2 (<= B4 200) (<= 35 B4)) T3)
       (= (and S M1 N1 O1 (not P1) Q1 S1 (not T1) (<= R1 200) (<= 35 R1)) F1)
       (= (and S2 T2) R2)
       (= V4 J1)
       (= U4 U)
       (= S4 V)
       (= O4 W1)
       (= N4 V1)
       (= Y1 J2)
       (= Z1 M2)
       (= B2 N2)
       (= E2 K4)
       (= H2 G2)
       (= M2 (or (not L2) K2))
       (= N2 (or (not L2) K2))
       (= Q2 (and P2 O2))
       (= U2 (and D T2))
       (= V2 (and (not C1) (not L4) (not M4)))
       (= W2 E2)
       (= W2 J3)
       (= X2 (or (not S) W2))
       (= Y2 (or B1 F2))
       (= A3 (or (not T) Z2))
       (= C3 (or B3 (not L4)))
       (= E3 (or D3 (not M4)))
       (= G3 (or (not C1) F3))
       (= I3 H3)
       (= K3 G2)
       (= K3 Z2)
       (= L3 A2)
       (= M3 A3)
       (= N3 C3)
       (= O3 E3)
       (= P3 G3)
       (= R3 U3)
       (= T3 D2)
       (= V3 X2)
       (= A4 Q2)
       (= C4 U2)
       (= E4 S3)
       (= H4 F4)
       (= I4 V2)
       (= I4 G4)
       (= U1 E1)
       (= H1 B1)
       (= F1 Q4)
       (= U F2)
       (= U T)
       (= S T4)
       (= S R)
       (= Q P)
       (= O W)
       (= M X)
       (= J Z)
       (= I Y)
       (= G I1)
       (= F O4)
       (= E S1)
       (= C Q1)
       (= B L1)
       (= A K1)
       (or Y1 X1 (and S Z1) (= K4 J4))
       (or (not S3) H2 (not D2))
       (or (not G4) (not F4) (= Q3 E4))
       (or (not V1) (not W1) (= U1 A1))
       (or D1 (not E1) (not Q4))
       (or S J4 (not B2))
       (or (and S3 D2) (= H2 C2))
       (or (and E1 Q4) (= D1 P4))
       (or (and (not S) B2) (= S J4))
       (or (not D2) (= U C2))
       (or D2 (not C2))
       (or (not F3) (= R3 Q3))
       (or (not M3) (= (or P3 O3 N3) I3))
       (or M3 I3)
       (or Q3 F3)
       (or (not V3) (= U3 F2))
       (or V3 (= U3 Y2))
       (or (not E4) (and G4 F4))
       a!2
       (or (not U1) (and V1 W1))
       (or (not I1) (= H1 G1))
       (or I1 (= H1 H))
       (or (not C1) (= B1 A1))
       (or A1 C1)
       (or (not W) (= (or X Y Z) Q))
       (or Q W)
       (= A2 true)
       (not J2)
       a!3))
      )
      (state G3
       P3
       E3
       O3
       C3
       N3
       A3
       M3
       U3
       R3
       X2
       V3
       Y2
       D3
       B3
       F3
       H4
       V2
       I4
       G4
       F4
       E4
       Q3
       S3
       U2
       C4
       Q2
       A4
       D4
       B4
       Z3
       W2
       Y3
       X3
       W3
       T3
       N2
       B2
       M2
       Z1
       J2
       Y1
       F2
       D2
       H2
       C2
       G2
       K3
       E2
       I3
       A2
       L3
       Z2
       J3
       H3
       R2
       I2
       T2
       O2
       K2
       X1
       J4
       K4)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Bool) (R1 Int) (S1 Bool) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Bool) (D2 Bool) (E2 Bool) (F2 Bool) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) ) 
    (=>
      (and
        (state J
       Z
       I
       Y
       M
       X
       O
       W
       H1
       B1
       G
       I1
       H
       B2
       A2
       C1
       C2
       F
       D2
       W1
       V1
       U1
       A1
       E1
       E
       S1
       C
       Q1
       T1
       R1
       P1
       S
       O1
       N1
       M1
       F1
       B
       L1
       A
       K1
       K2
       J1
       G1
       F2
       D1
       E2
       J2
       U
       I2
       Q
       H2
       V
       T
       R
       P
       D
       G2
       Z1
       Y1
       X1
       K
       L
       N)
        (not P)
      )
      false
    )
  )
)

(check-sat)
(exit)
