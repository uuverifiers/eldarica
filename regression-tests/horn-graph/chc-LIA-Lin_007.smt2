; vmt-chc-benchmarks/./lustre/fast_2_e8_460_e7_43_000.smt2
(set-logic HORN)

(declare-fun |state| ( Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Bool) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Int) (D2 Bool) (E2 Bool) (F2 Bool) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Bool) (W2 Bool) (X2 Bool) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Bool) (C3 Bool) (D3 Bool) (E3 Bool) (F3 Bool) ) 
    (=>
      (and
        (let ((a!1 (or (not Q1) (= (and T1 (not S1) (not R1)) D1)))
      (a!2 (= (or (and (not W2) (not V2) W1)
                  (and (not W2) V2 (not W1))
                  (and W2 (not V2) (not W1)))
              T2)))
  (and (= (and (not E2) D2 B2 A2 Z1 Y1 (not X1) F1 (<= C2 200) (<= 35 C2)) J1)
       (= (and P2 O2 (not E2) A2 Z1 Y1 (not X1) G1 (<= C2 200) (<= 35 C2)) H2)
       (= (and Y W V U) T)
       (= F3 I1)
       (= E3 T1)
       (= B3 K1)
       (= A M1)
       (= C (not B))
       (= C L1)
       (= D N1)
       (= E O1)
       (= F P1)
       (= I D2)
       (= K R1)
       (= L L2)
       (= M M2)
       (= N N2)
       (= P P2)
       (= Q U2)
       (= A1 O2)
       (= B1 U)
       (= C1 Y)
       (= D1 V)
       (= E1 W)
       (= G1 A3)
       (= G1 F1)
       (= K1 H1)
       (= R K2)
       (= H2 D3)
       (= J Q1)
       (= J2 V1)
       (= G B2)
       (= Q2 G2)
       (= T2 R2)
       (= U2 S2)
       (or (not G2) F2 (not D3))
       (or (not S2) (not R2) (= Q2 U1))
       (or (and G2 D3) (= F2 C3))
       (or (not C3) D3)
       (or (not I1) (= E1 (not H1)))
       (or I1 E1)
       (or J1 (= C1 (not H1)))
       (or (not J1) C1)
       (or (not M1) (= (or P1 O1 N1) B1))
       (or M1 B1)
       a!1
       (or Q1 D1)
       (or (not W1) (= V1 U1))
       (or W1 U1)
       (or K2 (= J2 S))
       (or (not K2) (= J2 I2))
       (or (not Q2) (and S2 R2))
       (not F3)
       (not E3)
       (not B3)
       (not A3)
       (not A)
       (not D)
       (not E)
       (not F)
       (not H)
       (not I)
       (not K)
       (not L)
       (not M)
       (not N)
       (not O)
       (not P)
       (= Q true)
       (= S true)
       (not A1)
       (not R)
       (not J)
       (not G)
       a!2))
      )
      (state J2
       V1
       R
       K2
       S
       W2
       V2
       W1
       T2
       Q
       U2
       S2
       R2
       Q2
       U1
       G2
       P
       P2
       A1
       O2
       X1
       G1
       Y1
       Z1
       A2
       C2
       E2
       H2
       N
       N2
       M
       M2
       L
       L2
       I2
       D3
       F2
       C3
       B3
       K1
       A3
       F3
       I1
       E3
       T1
       K
       R1
       J
       Q1
       I
       D2
       G
       B2
       F1
       J1
       F
       P1
       E
       O1
       D
       N1
       A
       M1
       E1
       S1
       D1
       C1
       B1
       C
       L1
       H1
       W
       V
       Y
       U
       T
       O
       H
       B
       Y2
       X2
       Z2
       X
       Z)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Bool) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Int) (D2 Bool) (E2 Bool) (F2 Bool) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Bool) (W2 Bool) (X2 Bool) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Bool) (C3 Bool) (D3 Bool) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Bool) (N3 Bool) (O3 Bool) (P3 Bool) (Q3 Bool) (R3 Bool) (S3 Bool) (T3 Bool) (U3 Bool) (V3 Bool) (W3 Bool) (X3 Bool) (Y3 Bool) (Z3 Bool) (A4 Bool) (B4 Bool) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Bool) (L4 Bool) (M4 Bool) (N4 Bool) (O4 Bool) (P4 Bool) (Q4 Bool) (R4 Bool) (S4 Bool) (T4 Bool) (U4 Bool) (V4 Bool) (W4 Bool) (X4 Bool) (Y4 Bool) (Z4 Bool) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Bool) (J5 Bool) (K5 Bool) (L5 Bool) (M5 Bool) (N5 Bool) (O5 Bool) (P5 Bool) (Q5 Bool) (R5 Bool) (S5 Int) (T5 Bool) (U5 Bool) (V5 Bool) (W5 Bool) (X5 Bool) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Bool) (H6 Bool) (I6 Bool) (J6 Bool) (K6 Bool) (L6 Bool) ) 
    (=>
      (and
        (state J2
       V1
       R
       K2
       S
       W2
       V2
       W1
       T2
       Q
       U2
       S2
       R2
       Q2
       U1
       G2
       P
       P2
       A1
       O2
       X1
       G1
       Y1
       Z1
       A2
       C2
       E2
       H2
       N
       N2
       M
       M2
       L
       L2
       I2
       J6
       F2
       I6
       H6
       K1
       G6
       L6
       I1
       K6
       T1
       K
       R1
       J
       Q1
       I
       D2
       G
       B2
       F1
       J1
       F
       P1
       E
       O1
       D
       N1
       A
       M1
       E1
       S1
       D1
       C1
       B1
       C
       L1
       H1
       W
       V
       Y
       U
       T
       O
       H
       B
       P3
       M3
       X3
       X
       Z)
        (let ((a!1 (= (or (and (not W1) (not V2) W2)
                  (and (not W1) V2 (not W2))
                  (and W1 (not V2) (not W2)))
              T2))
      (a!2 (or (not Y2) (and (not A3) (not Z2) (or (not G1) (not B3)))))
      (a!3 (or (not I5) (= (and K5 (not J5) (not Z2)) Y4)))
      (a!4 (or (not Q1) (= (and (not R1) (not S1) T1) D1)))
      (a!5 (= (or (and (not J3) (not H3) F3)
                  (and (not J3) H3 (not F3))
                  (and J3 (not H3) (not F3)))
              E6)))
  (and a!1
       (= (and (not U5) T5 R5 Q5 P5 O5 (not N5) S3 (<= S5 200) (<= 35 S5)) B5)
       (= (and A6 Z5 (not U5) Q5 P5 O5 (not N5) O4 (<= S5 200) (<= 35 S5)) W5)
       (= (and G1 (not X1) Y1 Z1 A2 (not E2) O2 P2 (<= C2 200) (<= 35 C2)) H2)
       (= (and F1 (not X1) Y1 Z1 A2 B2 D2 (not E2) (<= C2 200) (<= 35 C2)) J1)
       (= (and V4 U4 T4 S4) R4)
       (= (and U V W Y) T)
       (= (and P3 Q3) O3)
       (= (and P3 Q3) L4)
       (= L6 I1)
       (= K6 T1)
       (= H6 K1)
       (= A3 H4)
       (= B3 I4)
       (= E3 (or (not H1) D3))
       (= G3 (or (not V2) F3))
       (= I3 (or (not W2) H3))
       (= K3 (or (not W1) J3))
       (= N3 (and M3 L3))
       (= R3 (and H Q3))
       (= T3 (or (not F1) S3))
       (= Y3 (or (not X3) W3))
       (= A4 J4)
       (= D4 Y2)
       (= G4 F4)
       (= I4 (or (not X3) W3))
       (= J4 (or (not X3) W3))
       (= K4 (and M3 L3))
       (= M4 (and O Q3))
       (= N4 (and (not W1) (not V2) (not W2)))
       (= O4 S3)
       (= O4 D4)
       (= P4 (or (not G1) O4))
       (= Q4 (or V1 E4))
       (= W4 S4)
       (= X4 T4)
       (= Y4 U4)
       (= Z4 V4)
       (= A5 Z3)
       (= C5 D3)
       (= C5 F4)
       (= D5 C3)
       (= E5 E3)
       (= F5 G3)
       (= G5 I3)
       (= H5 K3)
       (= I5 T3)
       (= J5 V3)
       (= K5 Y3)
       (= M5 X5)
       (= R5 N3)
       (= T5 R3)
       (= W5 C4)
       (= Y5 P4)
       (= Z5 K4)
       (= A6 M4)
       (= B6 V5)
       (= E6 C6)
       (= F6 N4)
       (= F6 D6)
       (= U2 S2)
       (= T2 R2)
       (= Q2 G2)
       (= J2 V1)
       (= H2 J6)
       (= K1 E4)
       (= K1 H1)
       (= G1 G6)
       (= G1 F1)
       (= E1 W)
       (= D1 V)
       (= C1 Y)
       (= B1 U)
       (= A1 O2)
       (= R K2)
       (= Q U2)
       (= P P2)
       (= N N2)
       (= M M2)
       (= L L2)
       (= K R1)
       (= J Q1)
       (= I D2)
       (= G B2)
       (= F P1)
       (= E O1)
       (= D N1)
       (= C L1)
       (= A M1)
       (or A3 Z2 (and G1 B3) (= Y2 X2))
       (or (not V5) G4 (not C4))
       (or (not D6) (not C6) (= L5 B6))
       (or (not R2) (not S2) (= Q2 U1))
       (or F2 (not G2) (not J6))
       (or G1 (not A4) X2)
       (or (and V5 C4) (= G4 B4))
       (or (and G2 J6) (= F2 I6))
       (or (and (not G1) A4) (= G1 X2))
       a!2
       (or (not J3) (= M5 L5))
       (or (not C4) (= K1 B4))
       (or C4 (not B4))
       (or (not A5) (= Z4 (not D3)))
       (or A5 Z4)
       (or B5 (= X4 (not D3)))
       (or (not B5) X4)
       (or (not E5) (= (or H5 G5 F5) W4))
       (or E5 W4)
       a!3
       (or I5 Y4)
       (or L5 J3)
       (or (not Y5) (= X5 E4))
       (or Y5 (= X5 Q4))
       (or (not B6) (and D6 C6))
       (or (not Q2) (and R2 S2))
       (or (not K2) (= J2 I2))
       (or K2 (= J2 S))
       (or (not W1) (= V1 U1))
       (or U1 W1)
       a!4
       (or (not M1) (= (or N1 O1 P1) B1))
       (or J1 (= C1 (not H1)))
       (or (not I1) (= E1 (not H1)))
       (or E1 I1)
       (or D1 Q1)
       (or C1 (not J1))
       (or B1 M1)
       (= C3 true)
       (not V3)
       (not Z3)
       (not H4)
       a!5))
      )
      (state X5
       M5
       P4
       Y5
       Q4
       H3
       F3
       J3
       E6
       N4
       F6
       D6
       C6
       B6
       L5
       V5
       M4
       A6
       K4
       Z5
       N5
       O4
       O5
       P5
       Q5
       S5
       U5
       W5
       J4
       A4
       I4
       B3
       H4
       A3
       E4
       C4
       G4
       B4
       F4
       C5
       D4
       Z3
       A5
       Y3
       K5
       V3
       J5
       T3
       I5
       R3
       T5
       N3
       R5
       S3
       B5
       K3
       H5
       I3
       G5
       G3
       F5
       E3
       E5
       Z4
       Z2
       Y4
       X4
       W4
       C3
       D5
       D3
       V4
       U4
       T4
       S4
       R4
       L4
       O3
       U3
       Q3
       L3
       W3
       X2
       Y2)
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Bool) (F Bool) (G Bool) (H Bool) (I Bool) (J Bool) (K Bool) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) (V Bool) (W Bool) (X Bool) (Y Bool) (Z Bool) (A1 Bool) (B1 Bool) (C1 Bool) (D1 Bool) (E1 Bool) (F1 Bool) (G1 Bool) (H1 Bool) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Bool) (R1 Bool) (S1 Bool) (T1 Bool) (U1 Bool) (V1 Bool) (W1 Bool) (X1 Bool) (Y1 Bool) (Z1 Bool) (A2 Bool) (B2 Bool) (C2 Int) (D2 Bool) (E2 Bool) (F2 Bool) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Bool) (P2 Bool) (Q2 Bool) (R2 Bool) (S2 Bool) (T2 Bool) (U2 Bool) (V2 Bool) (W2 Bool) (X2 Bool) (Y2 Bool) (Z2 Bool) (A3 Bool) (B3 Bool) (C3 Bool) (D3 Bool) (E3 Bool) (F3 Bool) ) 
    (=>
      (and
        (state J2
       V1
       R
       K2
       S
       W2
       V2
       W1
       T2
       Q
       U2
       S2
       R2
       Q2
       U1
       G2
       P
       P2
       A1
       O2
       X1
       G1
       Y1
       Z1
       A2
       C2
       E2
       H2
       N
       N2
       M
       M2
       L
       L2
       I2
       D3
       F2
       C3
       B3
       K1
       A3
       F3
       I1
       E3
       T1
       K
       R1
       J
       Q1
       I
       D2
       G
       B2
       F1
       J1
       F
       P1
       E
       O1
       D
       N1
       A
       M1
       E1
       S1
       D1
       C1
       B1
       C
       L1
       H1
       W
       V
       Y
       U
       T
       O
       H
       B
       Y2
       X2
       Z2
       X
       Z)
        (not T)
      )
      false
    )
  )
)

(check-sat)
(exit)
