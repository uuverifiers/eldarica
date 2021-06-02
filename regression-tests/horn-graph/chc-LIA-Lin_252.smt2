; sv-comp/./LIA/SLayerCF/chaining/very_simple_unsafe_garbage_less_easy.c_000.smt2
(set-logic HORN)

(declare-fun |transition-3| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |transition-4| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |transition-0| ( Int Int Int Int Int Int Int Int Int Int Int Bool ) Bool)
(declare-fun |transition-8| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |transition-5| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |transition-1| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |transition-2| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |transition-6| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)
(declare-fun |transition-7| ( Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Bool Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (v_11 Int) (v_12 Bool) (v_13 Int) (v_14 Int) (v_15 Bool) ) 
    (=>
      (and
        (transition-0 v_11 K I H G F E D C B A v_12)
        (and (= 4 v_11) (= v_12 false) (= 1025 v_13) (= 2 v_14) (= v_15 false))
      )
      (transition-0 v_13 J I H G F E D v_14 B A v_15)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (v_34 Int) (v_35 Bool) (v_36 Int) (v_37 Int) (v_38 Bool) ) 
    (=>
      (and
        (transition-1 v_34
              H1
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
              K
              J
              I
              v_35
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 4 v_34) (= v_35 false) (= 1025 v_36) (= 2 v_37) (= v_38 false))
      )
      (transition-1 v_36
              G1
              F1
              E1
              D1
              C1
              B1
              A1
              v_37
              Y
              X
              W
              V
              U
              T
              S
              K
              J
              I
              v_38
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (v_58 Int) (v_59 Bool) (v_60 Int) (v_61 Int) (v_62 Bool) ) 
    (=>
      (and
        (transition-2 v_58
              F2
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
              v_59
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 4 v_58) (= v_59 false) (= 1025 v_60) (= 2 v_61) (= v_62 false))
      )
      (transition-2 v_60
              E2
              D2
              C2
              B2
              A2
              Z1
              Y1
              v_61
              W1
              V1
              U1
              T1
              S1
              R1
              Q1
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
              v_62
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (v_82 Int) (v_83 Bool) (v_84 Int) (v_85 Int) (v_86 Bool) ) 
    (=>
      (and
        (transition-3 v_82
              D3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_83
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 4 v_82) (= v_83 false) (= 1025 v_84) (= 2 v_85) (= v_86 false))
      )
      (transition-3 v_84
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              v_85
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_86
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (v_106 Int) (v_107 Bool) (v_108 Int) (v_109 Int) (v_110 Bool) ) 
    (=>
      (and
        (transition-4 v_106
              B4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_107
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 4 v_106) (= v_107 false) (= 1025 v_108) (= 2 v_109) (= v_110 false))
      )
      (transition-4 v_108
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              v_109
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_110
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (v_130 Int) (v_131 Bool) (v_132 Int) (v_133 Int) (v_134 Bool) ) 
    (=>
      (and
        (transition-5 v_130
              Z4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_131
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 4 v_130) (= v_131 false) (= 1025 v_132) (= 2 v_133) (= v_134 false))
      )
      (transition-5 v_132
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              v_133
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_134
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (v_154 Int) (v_155 Bool) (v_156 Int) (v_157 Int) (v_158 Bool) ) 
    (=>
      (and
        (transition-6 v_154
              X5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_155
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 4 v_154) (= v_155 false) (= 1025 v_156) (= 2 v_157) (= v_158 false))
      )
      (transition-6 v_156
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              v_157
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_158
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (v_178 Int) (v_179 Bool) (v_180 Int) (v_181 Int) (v_182 Bool) ) 
    (=>
      (and
        (transition-7 v_178
              V6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_179
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 4 v_178) (= v_179 false) (= 1025 v_180) (= 2 v_181) (= v_182 false))
      )
      (transition-7 v_180
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              v_181
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_182
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (v_202 Int) (v_203 Bool) (v_204 Int) (v_205 Int) (v_206 Bool) ) 
    (=>
      (and
        (transition-8 v_202
              T7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_203
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 4 v_202) (= v_203 false) (= 1025 v_204) (= 2 v_205) (= v_206 false))
      )
      (transition-8 v_204
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              v_205
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_206
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (v_12 Int) (v_13 Bool) (v_14 Int) (v_15 Bool) ) 
    (=>
      (and
        (transition-0 v_12 K I H G F E D C B A v_13)
        (and (= 1025 v_12) (= v_13 false) (= L (* 4 C)) (= 1026 v_14) (= v_15 false))
      )
      (transition-0 v_14 J I H L F E D C B A v_15)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (v_35 Int) (v_36 Bool) (v_37 Int) (v_38 Bool) ) 
    (=>
      (and
        (transition-1 v_35
              H1
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
              K
              J
              I
              v_36
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 1025 v_35) (= v_36 false) (= I1 (* 4 Z)) (= 1026 v_37) (= v_38 false))
      )
      (transition-1 v_37
              G1
              F1
              E1
              I1
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
              K
              J
              I
              v_38
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (v_59 Int) (v_60 Bool) (v_61 Int) (v_62 Bool) ) 
    (=>
      (and
        (transition-2 v_59
              F2
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
              v_60
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 1025 v_59) (= v_60 false) (= G2 (* 4 X1)) (= 1026 v_61) (= v_62 false))
      )
      (transition-2 v_61
              E2
              D2
              C2
              G2
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
              v_62
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Int) (v_83 Int) (v_84 Bool) (v_85 Int) (v_86 Bool) ) 
    (=>
      (and
        (transition-3 v_83
              D3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_84
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1025 v_83) (= v_84 false) (= E3 (* 4 V2)) (= 1026 v_85) (= v_86 false))
      )
      (transition-3 v_85
              C3
              B3
              A3
              E3
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_86
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Int) (v_107 Int) (v_108 Bool) (v_109 Int) (v_110 Bool) ) 
    (=>
      (and
        (transition-4 v_107
              B4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_108
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 1025 v_107)
     (= v_108 false)
     (= C4 (* 4 T3))
     (= 1026 v_109)
     (= v_110 false))
      )
      (transition-4 v_109
              A4
              Z3
              Y3
              C4
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_110
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Int) (v_131 Int) (v_132 Bool) (v_133 Int) (v_134 Bool) ) 
    (=>
      (and
        (transition-5 v_131
              Z4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_132
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1025 v_131)
     (= v_132 false)
     (= A5 (* 4 R4))
     (= 1026 v_133)
     (= v_134 false))
      )
      (transition-5 v_133
              Y4
              X4
              W4
              A5
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_134
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Int) (v_155 Int) (v_156 Bool) (v_157 Int) (v_158 Bool) ) 
    (=>
      (and
        (transition-6 v_155
              X5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_156
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1025 v_155)
     (= v_156 false)
     (= Y5 (* 4 P5))
     (= 1026 v_157)
     (= v_158 false))
      )
      (transition-6 v_157
              W5
              V5
              U5
              Y5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_158
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Int) (v_179 Int) (v_180 Bool) (v_181 Int) (v_182 Bool) ) 
    (=>
      (and
        (transition-7 v_179
              V6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_180
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1025 v_179)
     (= v_180 false)
     (= W6 (* 4 N6))
     (= 1026 v_181)
     (= v_182 false))
      )
      (transition-7 v_181
              U6
              T6
              S6
              W6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_182
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (U7 Int) (v_203 Int) (v_204 Bool) (v_205 Int) (v_206 Bool) ) 
    (=>
      (and
        (transition-8 v_203
              T7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_204
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1025 v_203)
     (= v_204 false)
     (= U7 (* 4 L7))
     (= 1026 v_205)
     (= v_206 false))
      )
      (transition-8 v_205
              S7
              R7
              Q7
              U7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_206
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (v_50 Int) (v_51 Bool) (v_52 Int) (v_53 Bool) ) 
    (=>
      (and
        (transition-0 v_50 W1 U1 T1 S1 R1 Q1 P1 H1 G1 F1 v_51)
        (let ((a!1 (not (<= (+ U1 (div S1 4)) 1)))
      (a!2 (not (<= (+ U1 (div S1 4)) 3)))
      (a!3 (not (<= (+ U1 (div S1 4)) 5)))
      (a!4 (not (<= (+ U1 (div S1 4)) 6)))
      (a!5 (not (<= (+ U1 (div S1 4)) 7)))
      (a!6 (not (<= (+ U1 (div S1 4)) 4)))
      (a!7 (not (<= (+ U1 (div S1 4)) 2)))
      (a!8 (or (not (<= U1 0)) (<= (+ U1 (div S1 4)) 0)))
      (a!9 (not (<= (+ U1 (div S1 4)) 0))))
  (and (= 1026 v_50)
       (= v_51 false)
       (ite (and (<= U1 1) a!1) (= G (div S1 4)) (= G V))
       (ite (and (<= U1 1) a!1) R (= R O1))
       (ite (and (<= U1 3) a!2) (= E (div S1 4)) (= E T))
       (ite (and (<= U1 3) a!2) P (= P M1))
       (ite (and (<= U1 5) a!3) (= C (div S1 4)) (= C K))
       (ite (and (<= U1 5) a!3) N (= N K1))
       (ite (and (<= U1 6) a!4) (= B (div S1 4)) (= B J))
       (ite (and (<= U1 6) a!4) M (= M J1))
       (ite (and (<= U1 7) a!5) (= A (div S1 4)) (= A I))
       (ite (and (<= U1 7) a!5) L (= L I1))
       (ite (and (<= U1 4) a!6) (= D (div S1 4)) (= D S))
       (ite (and (<= U1 4) a!6) O (= O L1))
       (ite (and (<= U1 2) a!7) (= F (div S1 4)) (= F U))
       (ite (and (<= U1 2) a!7) Q (= Q N1))
       (= X1 (+ U1 (div S1 4)))
       (<= (+ U1 (div S1 4)) 64)
       a!8
       (ite (and (<= U1 0) a!9) (= H (div S1 4)) (= H W))
       (= 1027 v_52)
       (= v_53 false)))
      )
      (transition-1 v_52
              V1
              X1
              T1
              S1
              U1
              Q1
              P1
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
              v_53
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Int) (v_113 Int) (v_114 Bool) (v_115 Int) (v_116 Bool) ) 
    (=>
      (and
        (transition-1 v_113
              B4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_114
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              C2
              B2
              A2
              Z1
              Y1
              X1
              W1
              V1)
        (let ((a!1 (not (<= (+ Z3 (div X3 4)) 8)))
      (a!2 (not (<= (+ Z3 (div X3 4)) 9)))
      (a!3 (not (<= (+ Z3 (div X3 4)) 10)))
      (a!4 (not (<= (+ Z3 (div X3 4)) 11)))
      (a!5 (not (<= (+ Z3 (div X3 4)) 12)))
      (a!6 (not (<= (+ Z3 (div X3 4)) 13)))
      (a!7 (not (<= (+ Z3 (div X3 4)) 14)))
      (a!8 (not (<= (+ Z3 (div X3 4)) 15)))
      (a!9 (not (<= (+ Z3 (div X3 4)) 0)))
      (a!10 (not (<= (+ Z3 (div X3 4)) 1)))
      (a!11 (not (<= (+ Z3 (div X3 4)) 3)))
      (a!12 (not (<= (+ Z3 (div X3 4)) 5)))
      (a!13 (not (<= (+ Z3 (div X3 4)) 6)))
      (a!14 (not (<= (+ Z3 (div X3 4)) 7)))
      (a!15 (not (<= (+ Z3 (div X3 4)) 4)))
      (a!16 (not (<= (+ Z3 (div X3 4)) 2)))
      (a!17 (or (not (<= Z3 0)) (<= (+ Z3 (div X3 4)) 0))))
  (and (= 1026 v_113)
       (= v_114 false)
       (ite (and (<= Z3 8) a!1) I1 (= I1 N2))
       (ite (and (<= Z3 9) a!2) (= G (div X3 4)) (= G D1))
       (ite (and (<= Z3 9) a!2) R (= R M2))
       (ite (and (<= Z3 10) a!3) (= F (div X3 4)) (= F C1))
       (ite (and (<= Z3 10) a!3) Q (= Q L2))
       (ite (and (<= Z3 11) a!4) (= E (div X3 4)) (= E B1))
       (ite (and (<= Z3 11) a!4) P (= P K2))
       (ite (and (<= Z3 12) a!5) (= D (div X3 4)) (= D A1))
       (ite (and (<= Z3 12) a!5) O (= O J2))
       (ite (and (<= Z3 13) a!6) (= C (div X3 4)) (= C Z))
       (ite (and (<= Z3 13) a!6) N (= N I2))
       (ite (and (<= Z3 14) a!7) (= B (div X3 4)) (= B Y))
       (ite (and (<= Z3 14) a!7) M (= M H2))
       (ite (and (<= Z3 15) a!8) (= A (div X3 4)) (= A X))
       (ite (and (<= Z3 15) a!8) L (= L G2))
       (ite (and (<= Z3 0) a!9) (= W (div X3 4)) (= W U1))
       (ite (and (<= Z3 1) a!10) (= V (div X3 4)) (= V T1))
       (ite (and (<= Z3 1) a!10) P1 (= P1 K3))
       (ite (and (<= Z3 3) a!11) (= T (div X3 4)) (= T R1))
       (ite (and (<= Z3 3) a!11) N1 (= N1 I3))
       (ite (and (<= Z3 5) a!12) (= K (div X3 4)) (= K H1))
       (ite (and (<= Z3 5) a!12) L1 (= L1 G3))
       (ite (and (<= Z3 6) a!13) (= J (div X3 4)) (= J G1))
       (ite (and (<= Z3 6) a!13) K1 (= K1 F3))
       (ite (and (<= Z3 7) a!14) (= I (div X3 4)) (= I F1))
       (ite (and (<= Z3 7) a!14) J1 (= J1 E3))
       (ite (and (<= Z3 4) a!15) (= S (div X3 4)) (= S Q1))
       (ite (and (<= Z3 4) a!15) M1 (= M1 H3))
       (ite (and (<= Z3 2) a!16) (= U (div X3 4)) (= U S1))
       (ite (and (<= Z3 2) a!16) O1 (= O1 J3))
       (= H4 K3)
       (= G4 J3)
       (= F4 I3)
       (= E4 H3)
       (= D4 G3)
       (= C4 F3)
       (= L3 E3)
       (= V1 F1)
       (= Q3 A3)
       (= P3 Z2)
       (= O3 Y2)
       (= N3 X2)
       (= M3 W2)
       (= W1 G1)
       (= C2 U1)
       (= B2 T1)
       (= A2 S1)
       (= Z1 R1)
       (= Y1 Q1)
       (= X1 H1)
       (= D3 V2)
       (= C3 U2)
       (= B3 T2)
       (= I4 (+ Z3 (div X3 4)))
       (<= (+ Z3 (div X3 4)) 64)
       a!17
       (ite (and (<= Z3 8) a!1) (= H (div X3 4)) (= H E1))
       (= 1027 v_115)
       (= v_116 false)))
      )
      (transition-2 v_115
              A4
              I4
              Y3
              X3
              Z3
              V3
              U3
              T3
              S3
              R3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_116
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Bool) (Q6 Bool) (R6 Bool) (S6 Bool) (T6 Bool) (U6 Bool) (v_177 Int) (v_178 Bool) (v_179 Int) (v_180 Bool) ) 
    (=>
      (and
        (transition-2 v_177
              N6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              v_178
              U6
              T6
              S6
              R6
              Q6
              P6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2)
        (let ((a!1 (not (<= (+ L6 (div J6 4)) 16)))
      (a!2 (not (<= (+ L6 (div J6 4)) 17)))
      (a!3 (not (<= (+ L6 (div J6 4)) 18)))
      (a!4 (not (<= (+ L6 (div J6 4)) 19)))
      (a!5 (not (<= (+ L6 (div J6 4)) 20)))
      (a!6 (not (<= (+ L6 (div J6 4)) 21)))
      (a!7 (not (<= (+ L6 (div J6 4)) 22)))
      (a!8 (not (<= (+ L6 (div J6 4)) 23)))
      (a!9 (not (<= (+ L6 (div J6 4)) 8)))
      (a!10 (not (<= (+ L6 (div J6 4)) 9)))
      (a!11 (not (<= (+ L6 (div J6 4)) 10)))
      (a!12 (not (<= (+ L6 (div J6 4)) 11)))
      (a!13 (not (<= (+ L6 (div J6 4)) 12)))
      (a!14 (not (<= (+ L6 (div J6 4)) 13)))
      (a!15 (not (<= (+ L6 (div J6 4)) 14)))
      (a!16 (not (<= (+ L6 (div J6 4)) 15)))
      (a!17 (not (<= (+ L6 (div J6 4)) 0)))
      (a!18 (not (<= (+ L6 (div J6 4)) 1)))
      (a!19 (not (<= (+ L6 (div J6 4)) 3)))
      (a!20 (not (<= (+ L6 (div J6 4)) 5)))
      (a!21 (not (<= (+ L6 (div J6 4)) 6)))
      (a!22 (not (<= (+ L6 (div J6 4)) 7)))
      (a!23 (not (<= (+ L6 (div J6 4)) 4)))
      (a!24 (not (<= (+ L6 (div J6 4)) 2)))
      (a!25 (or (not (<= L6 0)) (<= (+ L6 (div J6 4)) 0))))
  (and (= 1026 v_177)
       (= v_178 false)
       (ite (and (<= L6 16) a!1) I1 (= I1 L3))
       (ite (and (<= L6 17) a!2) (= G (div J6 4)) (= G T1))
       (ite (and (<= L6 17) a!2) R (= R K3))
       (ite (and (<= L6 18) a!3) (= F (div J6 4)) (= F S1))
       (ite (and (<= L6 18) a!3) Q (= Q J3))
       (ite (and (<= L6 19) a!4) (= E (div J6 4)) (= E R1))
       (ite (and (<= L6 19) a!4) P (= P I3))
       (ite (and (<= L6 20) a!5) (= D (div J6 4)) (= D Q1))
       (ite (and (<= L6 20) a!5) O (= O H3))
       (ite (and (<= L6 21) a!6) (= C (div J6 4)) (= C H1))
       (ite (and (<= L6 21) a!6) N (= N G3))
       (ite (and (<= L6 22) a!7) (= B (div J6 4)) (= B G1))
       (ite (and (<= L6 22) a!7) M (= M F3))
       (ite (and (<= L6 23) a!8) (= A (div J6 4)) (= A F1))
       (ite (and (<= L6 23) a!8) L (= L E3))
       (ite (and (<= L6 8) a!9) (= W (div J6 4)) (= W C2))
       (ite (and (<= L6 8) a!9) G2 (= G2 J4))
       (ite (and (<= L6 9) a!10) (= V (div J6 4)) (= V B2))
       (ite (and (<= L6 9) a!10) P1 (= P1 I4))
       (ite (and (<= L6 10) a!11) (= U (div J6 4)) (= U A2))
       (ite (and (<= L6 10) a!11) O1 (= O1 H4))
       (ite (and (<= L6 11) a!12) (= T (div J6 4)) (= T Z1))
       (ite (and (<= L6 11) a!12) N1 (= N1 G4))
       (ite (and (<= L6 12) a!13) (= S (div J6 4)) (= S Y1))
       (ite (and (<= L6 12) a!13) M1 (= M1 F4))
       (ite (and (<= L6 13) a!14) (= K (div J6 4)) (= K X1))
       (ite (and (<= L6 13) a!14) L1 (= L1 E4))
       (ite (and (<= L6 14) a!15) (= J (div J6 4)) (= J W1))
       (ite (and (<= L6 14) a!15) K1 (= K1 D4))
       (ite (and (<= L6 15) a!16) (= I (div J6 4)) (= I V1))
       (ite (and (<= L6 15) a!16) J1 (= J1 C4))
       (ite (and (<= L6 0) a!17) (= E1 (div J6 4)) (= E1 S2))
       (ite (and (<= L6 1) a!18) (= D1 (div J6 4)) (= D1 R2))
       (ite (and (<= L6 1) a!18) N2 (= N2 G5))
       (ite (and (<= L6 3) a!19) (= B1 (div J6 4)) (= B1 P2))
       (ite (and (<= L6 3) a!19) L2 (= L2 E5))
       (ite (and (<= L6 5) a!20) (= Z (div J6 4)) (= Z F2))
       (ite (and (<= L6 5) a!20) J2 (= J2 C5))
       (ite (and (<= L6 6) a!21) (= Y (div J6 4)) (= Y E2))
       (ite (and (<= L6 6) a!21) I2 (= I2 B5))
       (ite (and (<= L6 7) a!22) (= X (div J6 4)) (= X D2))
       (ite (and (<= L6 7) a!22) H2 (= H2 A5))
       (ite (and (<= L6 4) a!23) (= A1 (div J6 4)) (= A1 O2))
       (ite (and (<= L6 4) a!23) K2 (= K2 D5))
       (ite (and (<= L6 2) a!24) (= C1 (div J6 4)) (= C1 Q2))
       (ite (and (<= L6 2) a!24) M2 (= M2 F5))
       (= U6 G5)
       (= H5 C4)
       (= T6 F5)
       (= S6 E5)
       (= R6 D5)
       (= Q6 C5)
       (= P6 B5)
       (= F6 A5)
       (= E6 J4)
       (= D6 I4)
       (= C6 H4)
       (= B6 G4)
       (= A6 F4)
       (= Z5 E4)
       (= Y5 D4)
       (= Q3 S2)
       (= P3 R2)
       (= O3 Q2)
       (= N3 P2)
       (= M3 O2)
       (= D3 F2)
       (= C3 E2)
       (= B3 D2)
       (= A3 C2)
       (= Z2 B2)
       (= Y2 A2)
       (= X2 Z1)
       (= W2 Y1)
       (= V2 X1)
       (= U2 W1)
       (= T2 V1)
       (= M5 O4)
       (= L5 N4)
       (= K5 M4)
       (= J5 L4)
       (= I5 K4)
       (= Z4 B4)
       (= Y4 A4)
       (= X4 Z3)
       (= U5 W4)
       (= T5 V4)
       (= S5 U4)
       (= R5 T4)
       (= Q5 S4)
       (= P5 R4)
       (= O5 Q4)
       (= N5 P4)
       (= O6 (+ L6 (div J6 4)))
       (<= (+ L6 (div J6 4)) 64)
       a!25
       (ite (and (<= L6 16) a!1) (= H (div J6 4)) (= H U1))
       (= 1027 v_179)
       (= v_180 false)))
      )
      (transition-3 v_179
              M6
              O6
              K6
              J6
              L6
              H6
              G6
              X5
              W5
              V5
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_180
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (U7 Int) (V7 Bool) (W7 Bool) (X7 Bool) (Y7 Bool) (Z7 Bool) (A8 Bool) (B8 Bool) (C8 Bool) (D8 Bool) (E8 Bool) (F8 Bool) (G8 Bool) (H8 Bool) (I8 Bool) (J8 Bool) (K8 Bool) (L8 Bool) (M8 Bool) (N8 Bool) (O8 Bool) (P8 Bool) (Q8 Bool) (R8 Int) (S8 Int) (T8 Int) (U8 Int) (V8 Int) (W8 Int) (X8 Int) (Y8 Int) (Z8 Int) (A9 Int) (B9 Int) (C9 Int) (D9 Int) (E9 Int) (F9 Int) (G9 Int) (v_241 Int) (v_242 Bool) (v_243 Int) (v_244 Bool) ) 
    (=>
      (and
        (transition-3 v_241
              F9
              D9
              C9
              B9
              A9
              Z8
              Y8
              X8
              W8
              V8
              U8
              T8
              S8
              R8
              U7
              T7
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              v_242
              Q8
              P8
              O8
              N8
              M8
              L8
              K8
              J8
              I8
              H8
              G8
              F8
              E8
              D8
              C8
              B8
              A8
              Z7
              Y7
              X7
              W7
              V7
              D7
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3)
        (let ((a!1 (not (<= (+ D9 (div B9 4)) 24)))
      (a!2 (not (<= (+ D9 (div B9 4)) 25)))
      (a!3 (not (<= (+ D9 (div B9 4)) 26)))
      (a!4 (not (<= (+ D9 (div B9 4)) 27)))
      (a!5 (not (<= (+ D9 (div B9 4)) 28)))
      (a!6 (not (<= (+ D9 (div B9 4)) 29)))
      (a!7 (not (<= (+ D9 (div B9 4)) 30)))
      (a!8 (not (<= (+ D9 (div B9 4)) 31)))
      (a!9 (not (<= (+ D9 (div B9 4)) 16)))
      (a!10 (not (<= (+ D9 (div B9 4)) 17)))
      (a!11 (not (<= (+ D9 (div B9 4)) 18)))
      (a!12 (not (<= (+ D9 (div B9 4)) 19)))
      (a!13 (not (<= (+ D9 (div B9 4)) 20)))
      (a!14 (not (<= (+ D9 (div B9 4)) 21)))
      (a!15 (not (<= (+ D9 (div B9 4)) 22)))
      (a!16 (not (<= (+ D9 (div B9 4)) 23)))
      (a!17 (not (<= (+ D9 (div B9 4)) 8)))
      (a!18 (not (<= (+ D9 (div B9 4)) 9)))
      (a!19 (not (<= (+ D9 (div B9 4)) 10)))
      (a!20 (not (<= (+ D9 (div B9 4)) 11)))
      (a!21 (not (<= (+ D9 (div B9 4)) 12)))
      (a!22 (not (<= (+ D9 (div B9 4)) 13)))
      (a!23 (not (<= (+ D9 (div B9 4)) 14)))
      (a!24 (not (<= (+ D9 (div B9 4)) 15)))
      (a!25 (not (<= (+ D9 (div B9 4)) 0)))
      (a!26 (not (<= (+ D9 (div B9 4)) 1)))
      (a!27 (not (<= (+ D9 (div B9 4)) 3)))
      (a!28 (not (<= (+ D9 (div B9 4)) 5)))
      (a!29 (not (<= (+ D9 (div B9 4)) 6)))
      (a!30 (not (<= (+ D9 (div B9 4)) 7)))
      (a!31 (not (<= (+ D9 (div B9 4)) 4)))
      (a!32 (not (<= (+ D9 (div B9 4)) 2)))
      (a!33 (or (not (<= D9 0)) (<= (+ D9 (div B9 4)) 0))))
  (and (= 1026 v_241)
       (= v_242 false)
       (ite (and (<= D9 24) a!1) I1 (= I1 J4))
       (ite (and (<= D9 25) a!2) (= G (div B9 4)) (= G B2))
       (ite (and (<= D9 25) a!2) R (= R I4))
       (ite (and (<= D9 26) a!3) (= F (div B9 4)) (= F A2))
       (ite (and (<= D9 26) a!3) Q (= Q H4))
       (ite (and (<= D9 27) a!4) (= E (div B9 4)) (= E Z1))
       (ite (and (<= D9 27) a!4) P (= P G4))
       (ite (and (<= D9 28) a!5) (= D (div B9 4)) (= D Y1))
       (ite (and (<= D9 28) a!5) O (= O F4))
       (ite (and (<= D9 29) a!6) (= C (div B9 4)) (= C X1))
       (ite (and (<= D9 29) a!6) N (= N E4))
       (ite (and (<= D9 30) a!7) (= B (div B9 4)) (= B W1))
       (ite (and (<= D9 30) a!7) M (= M D4))
       (ite (and (<= D9 31) a!8) (= A (div B9 4)) (= A V1))
       (ite (and (<= D9 31) a!8) L (= L C4))
       (ite (and (<= D9 16) a!9) (= W (div B9 4)) (= W S2))
       (ite (and (<= D9 16) a!9) G2 (= G2 H5))
       (ite (and (<= D9 17) a!10) (= V (div B9 4)) (= V R2))
       (ite (and (<= D9 17) a!10) P1 (= P1 G5))
       (ite (and (<= D9 18) a!11) (= U (div B9 4)) (= U Q2))
       (ite (and (<= D9 18) a!11) O1 (= O1 F5))
       (ite (and (<= D9 19) a!12) (= T (div B9 4)) (= T P2))
       (ite (and (<= D9 19) a!12) N1 (= N1 E5))
       (ite (and (<= D9 20) a!13) (= S (div B9 4)) (= S O2))
       (ite (and (<= D9 20) a!13) M1 (= M1 D5))
       (ite (and (<= D9 21) a!14) (= K (div B9 4)) (= K F2))
       (ite (and (<= D9 21) a!14) L1 (= L1 C5))
       (ite (and (<= D9 22) a!15) (= J (div B9 4)) (= J E2))
       (ite (and (<= D9 22) a!15) K1 (= K1 B5))
       (ite (and (<= D9 23) a!16) (= I (div B9 4)) (= I D2))
       (ite (and (<= D9 23) a!16) J1 (= J1 A5))
       (ite (and (<= D9 8) a!17) (= E1 (div B9 4)) (= E1 A3))
       (ite (and (<= D9 8) a!17) E3 (= E3 F6))
       (ite (and (<= D9 9) a!18) (= D1 (div B9 4)) (= D1 Z2))
       (ite (and (<= D9 9) a!18) N2 (= N2 E6))
       (ite (and (<= D9 10) a!19) (= C1 (div B9 4)) (= C1 Y2))
       (ite (and (<= D9 10) a!19) M2 (= M2 D6))
       (ite (and (<= D9 11) a!20) (= B1 (div B9 4)) (= B1 X2))
       (ite (and (<= D9 11) a!20) L2 (= L2 C6))
       (ite (and (<= D9 12) a!21) (= A1 (div B9 4)) (= A1 W2))
       (ite (and (<= D9 12) a!21) K2 (= K2 B6))
       (ite (and (<= D9 13) a!22) (= Z (div B9 4)) (= Z V2))
       (ite (and (<= D9 13) a!22) J2 (= J2 A6))
       (ite (and (<= D9 14) a!23) (= Y (div B9 4)) (= Y U2))
       (ite (and (<= D9 14) a!23) I2 (= I2 Z5))
       (ite (and (<= D9 15) a!24) (= X (div B9 4)) (= X T2))
       (ite (and (<= D9 15) a!24) H2 (= H2 Y5))
       (ite (and (<= D9 0) a!25) (= U1 (div B9 4)) (= U1 Q3))
       (ite (and (<= D9 1) a!26) (= T1 (div B9 4)) (= T1 P3))
       (ite (and (<= D9 1) a!26) L3 (= L3 C7))
       (ite (and (<= D9 3) a!27) (= R1 (div B9 4)) (= R1 N3))
       (ite (and (<= D9 3) a!27) J3 (= J3 A7))
       (ite (and (<= D9 5) a!28) (= H1 (div B9 4)) (= H1 D3))
       (ite (and (<= D9 5) a!28) H3 (= H3 Y6))
       (ite (and (<= D9 6) a!29) (= G1 (div B9 4)) (= G1 C3))
       (ite (and (<= D9 6) a!29) G3 (= G3 X6))
       (ite (and (<= D9 7) a!30) (= F1 (div B9 4)) (= F1 B3))
       (ite (and (<= D9 7) a!30) F3 (= F3 W6))
       (ite (and (<= D9 4) a!31) (= Q1 (div B9 4)) (= Q1 M3))
       (ite (and (<= D9 4) a!31) I3 (= I3 Z6))
       (ite (and (<= D9 2) a!32) (= S1 (div B9 4)) (= S1 O3))
       (ite (and (<= D9 2) a!32) K3 (= K3 B7))
       (= B8 H5)
       (= D7 A5)
       (= H8 D6)
       (= G8 C6)
       (= F8 B6)
       (= E8 A6)
       (= D8 Z5)
       (= C8 Y5)
       (= A8 G5)
       (= Z7 F5)
       (= Y7 E5)
       (= X7 D5)
       (= W7 C5)
       (= V7 B5)
       (= I8 E6)
       (= J8 F6)
       (= Q8 C7)
       (= P8 B7)
       (= O8 A7)
       (= N8 Z6)
       (= M8 Y6)
       (= L8 X6)
       (= K8 W6)
       (= W4 Q3)
       (= V4 P3)
       (= U4 O3)
       (= T4 N3)
       (= S4 M3)
       (= Z3 T2)
       (= Y3 S2)
       (= X3 R2)
       (= W3 Q2)
       (= V3 P2)
       (= U3 O2)
       (= T6 N5)
       (= R7 L6)
       (= Q7 K6)
       (= P7 J6)
       (= O7 I6)
       (= N7 H6)
       (= M7 G6)
       (= A4 U2)
       (= U6 O5)
       (= S7 M6)
       (= B4 V2)
       (= T3 F2)
       (= S3 E2)
       (= R3 D2)
       (= R4 D3)
       (= Q4 C3)
       (= P4 B3)
       (= O4 A3)
       (= N4 Z2)
       (= M4 Y2)
       (= L4 X2)
       (= K4 W2)
       (= V6 P5)
       (= U7 O6)
       (= T7 N6)
       (= L7 X5)
       (= K7 W5)
       (= J7 V5)
       (= I7 U5)
       (= H7 T5)
       (= G7 S5)
       (= F7 R5)
       (= E7 Q5)
       (= U8 S6)
       (= T8 R6)
       (= S8 Q6)
       (= R8 P6)
       (= G9 (+ D9 (div B9 4)))
       (<= (+ D9 (div B9 4)) 64)
       a!33
       (ite (and (<= D9 24) a!1) (= H (div B9 4)) (= H C2))
       (= 1027 v_243)
       (= v_244 false)))
      )
      (transition-4 v_243
              E9
              G9
              C9
              B9
              D9
              Z8
              Y8
              X8
              W8
              V8
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              v_244
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (U7 Int) (V7 Bool) (W7 Bool) (X7 Bool) (Y7 Bool) (Z7 Bool) (A8 Bool) (B8 Bool) (C8 Bool) (D8 Bool) (E8 Bool) (F8 Bool) (G8 Bool) (H8 Bool) (I8 Bool) (J8 Bool) (K8 Bool) (L8 Bool) (M8 Bool) (N8 Bool) (O8 Bool) (P8 Bool) (Q8 Bool) (R8 Int) (S8 Int) (T8 Int) (U8 Int) (V8 Int) (W8 Int) (X8 Int) (Y8 Int) (Z8 Int) (A9 Int) (B9 Int) (C9 Int) (D9 Int) (E9 Int) (F9 Int) (G9 Int) (H9 Bool) (I9 Bool) (J9 Bool) (K9 Bool) (L9 Bool) (M9 Bool) (N9 Bool) (O9 Bool) (P9 Bool) (Q9 Bool) (R9 Bool) (S9 Bool) (T9 Bool) (U9 Bool) (V9 Bool) (W9 Bool) (X9 Bool) (Y9 Bool) (Z9 Bool) (A10 Bool) (B10 Bool) (C10 Bool) (D10 Bool) (E10 Bool) (F10 Int) (G10 Int) (H10 Int) (I10 Int) (J10 Int) (K10 Int) (L10 Int) (M10 Int) (N10 Int) (O10 Int) (P10 Int) (Q10 Int) (R10 Int) (S10 Int) (T10 Int) (U10 Int) (V10 Int) (W10 Int) (X10 Int) (Y10 Int) (Z10 Int) (A11 Int) (B11 Int) (C11 Int) (D11 Int) (E11 Int) (F11 Int) (G11 Int) (H11 Int) (I11 Int) (J11 Int) (K11 Int) (L11 Int) (M11 Int) (N11 Int) (O11 Int) (P11 Int) (Q11 Int) (R11 Int) (S11 Int) (v_305 Int) (v_306 Bool) (v_307 Int) (v_308 Bool) ) 
    (=>
      (and
        (transition-4 v_305
              R11
              P11
              O11
              N11
              M11
              L11
              K11
              J11
              I11
              H11
              G11
              F11
              E11
              D11
              C11
              B11
              A11
              Z10
              Y10
              X10
              W10
              V10
              U10
              T10
              S10
              R10
              Q10
              P10
              O10
              N10
              M10
              L10
              K10
              J10
              I10
              H10
              G10
              F10
              G9
              F9
              E9
              D9
              v_306
              E10
              D10
              C10
              B10
              A10
              Z9
              Y9
              X9
              W9
              V9
              U9
              T9
              S9
              R9
              Q9
              P9
              O9
              N9
              M9
              L9
              K9
              J9
              I9
              H9
              Q8
              P8
              O8
              N8
              M8
              L8
              K8
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4)
        (let ((a!1 (not (<= (+ P11 (div N11 4)) 32)))
      (a!2 (not (<= (+ P11 (div N11 4)) 33)))
      (a!3 (not (<= (+ P11 (div N11 4)) 34)))
      (a!4 (not (<= (+ P11 (div N11 4)) 35)))
      (a!5 (not (<= (+ P11 (div N11 4)) 36)))
      (a!6 (not (<= (+ P11 (div N11 4)) 37)))
      (a!7 (not (<= (+ P11 (div N11 4)) 38)))
      (a!8 (not (<= (+ P11 (div N11 4)) 39)))
      (a!9 (not (<= (+ P11 (div N11 4)) 24)))
      (a!10 (not (<= (+ P11 (div N11 4)) 25)))
      (a!11 (not (<= (+ P11 (div N11 4)) 26)))
      (a!12 (not (<= (+ P11 (div N11 4)) 27)))
      (a!13 (not (<= (+ P11 (div N11 4)) 28)))
      (a!14 (not (<= (+ P11 (div N11 4)) 29)))
      (a!15 (not (<= (+ P11 (div N11 4)) 30)))
      (a!16 (not (<= (+ P11 (div N11 4)) 31)))
      (a!17 (not (<= (+ P11 (div N11 4)) 16)))
      (a!18 (not (<= (+ P11 (div N11 4)) 17)))
      (a!19 (not (<= (+ P11 (div N11 4)) 18)))
      (a!20 (not (<= (+ P11 (div N11 4)) 19)))
      (a!21 (not (<= (+ P11 (div N11 4)) 20)))
      (a!22 (not (<= (+ P11 (div N11 4)) 21)))
      (a!23 (not (<= (+ P11 (div N11 4)) 22)))
      (a!24 (not (<= (+ P11 (div N11 4)) 23)))
      (a!25 (not (<= (+ P11 (div N11 4)) 8)))
      (a!26 (not (<= (+ P11 (div N11 4)) 9)))
      (a!27 (not (<= (+ P11 (div N11 4)) 10)))
      (a!28 (not (<= (+ P11 (div N11 4)) 11)))
      (a!29 (not (<= (+ P11 (div N11 4)) 12)))
      (a!30 (not (<= (+ P11 (div N11 4)) 13)))
      (a!31 (not (<= (+ P11 (div N11 4)) 14)))
      (a!32 (not (<= (+ P11 (div N11 4)) 15)))
      (a!33 (not (<= (+ P11 (div N11 4)) 0)))
      (a!34 (not (<= (+ P11 (div N11 4)) 1)))
      (a!35 (not (<= (+ P11 (div N11 4)) 3)))
      (a!36 (not (<= (+ P11 (div N11 4)) 5)))
      (a!37 (not (<= (+ P11 (div N11 4)) 6)))
      (a!38 (not (<= (+ P11 (div N11 4)) 7)))
      (a!39 (not (<= (+ P11 (div N11 4)) 4)))
      (a!40 (not (<= (+ P11 (div N11 4)) 2)))
      (a!41 (or (not (<= P11 0)) (<= (+ P11 (div N11 4)) 0))))
  (and (= 1026 v_305)
       (= v_306 false)
       (ite (and (<= P11 32) a!1) I1 (= I1 H5))
       (ite (and (<= P11 33) a!2) (= G (div N11 4)) (= G R2))
       (ite (and (<= P11 33) a!2) R (= R G5))
       (ite (and (<= P11 34) a!3) (= F (div N11 4)) (= F Q2))
       (ite (and (<= P11 34) a!3) Q (= Q F5))
       (ite (and (<= P11 35) a!4) (= E (div N11 4)) (= E P2))
       (ite (and (<= P11 35) a!4) P (= P E5))
       (ite (and (<= P11 36) a!5) (= D (div N11 4)) (= D O2))
       (ite (and (<= P11 36) a!5) O (= O D5))
       (ite (and (<= P11 37) a!6) (= C (div N11 4)) (= C F2))
       (ite (and (<= P11 37) a!6) N (= N C5))
       (ite (and (<= P11 38) a!7) (= B (div N11 4)) (= B E2))
       (ite (and (<= P11 38) a!7) M (= M B5))
       (ite (and (<= P11 39) a!8) (= A (div N11 4)) (= A D2))
       (ite (and (<= P11 39) a!8) L (= L A5))
       (ite (and (<= P11 24) a!9) (= W (div N11 4)) (= W A3))
       (ite (and (<= P11 24) a!9) G2 (= G2 F6))
       (ite (and (<= P11 25) a!10) (= V (div N11 4)) (= V Z2))
       (ite (and (<= P11 25) a!10) P1 (= P1 E6))
       (ite (and (<= P11 26) a!11) (= U (div N11 4)) (= U Y2))
       (ite (and (<= P11 26) a!11) O1 (= O1 D6))
       (ite (and (<= P11 27) a!12) (= T (div N11 4)) (= T X2))
       (ite (and (<= P11 27) a!12) N1 (= N1 C6))
       (ite (and (<= P11 28) a!13) (= S (div N11 4)) (= S W2))
       (ite (and (<= P11 28) a!13) M1 (= M1 B6))
       (ite (and (<= P11 29) a!14) (= K (div N11 4)) (= K V2))
       (ite (and (<= P11 29) a!14) L1 (= L1 A6))
       (ite (and (<= P11 30) a!15) (= J (div N11 4)) (= J U2))
       (ite (and (<= P11 30) a!15) K1 (= K1 Z5))
       (ite (and (<= P11 31) a!16) (= I (div N11 4)) (= I T2))
       (ite (and (<= P11 31) a!16) J1 (= J1 Y5))
       (ite (and (<= P11 16) a!17) (= E1 (div N11 4)) (= E1 Q3))
       (ite (and (<= P11 16) a!17) E3 (= E3 D7))
       (ite (and (<= P11 17) a!18) (= D1 (div N11 4)) (= D1 P3))
       (ite (and (<= P11 17) a!18) N2 (= N2 C7))
       (ite (and (<= P11 18) a!19) (= C1 (div N11 4)) (= C1 O3))
       (ite (and (<= P11 18) a!19) M2 (= M2 B7))
       (ite (and (<= P11 19) a!20) (= B1 (div N11 4)) (= B1 N3))
       (ite (and (<= P11 19) a!20) L2 (= L2 A7))
       (ite (and (<= P11 20) a!21) (= A1 (div N11 4)) (= A1 M3))
       (ite (and (<= P11 20) a!21) K2 (= K2 Z6))
       (ite (and (<= P11 21) a!22) (= Z (div N11 4)) (= Z D3))
       (ite (and (<= P11 21) a!22) J2 (= J2 Y6))
       (ite (and (<= P11 22) a!23) (= Y (div N11 4)) (= Y C3))
       (ite (and (<= P11 22) a!23) I2 (= I2 X6))
       (ite (and (<= P11 23) a!24) (= X (div N11 4)) (= X B3))
       (ite (and (<= P11 23) a!24) H2 (= H2 W6))
       (ite (and (<= P11 8) a!25) (= U1 (div N11 4)) (= U1 Y3))
       (ite (and (<= P11 8) a!25) C4 (= C4 C8))
       (ite (and (<= P11 9) a!26) (= T1 (div N11 4)) (= T1 X3))
       (ite (and (<= P11 9) a!26) L3 (= L3 B8))
       (ite (and (<= P11 10) a!27) (= S1 (div N11 4)) (= S1 W3))
       (ite (and (<= P11 10) a!27) K3 (= K3 A8))
       (ite (and (<= P11 11) a!28) (= R1 (div N11 4)) (= R1 V3))
       (ite (and (<= P11 11) a!28) J3 (= J3 Z7))
       (ite (and (<= P11 12) a!29) (= Q1 (div N11 4)) (= Q1 U3))
       (ite (and (<= P11 12) a!29) I3 (= I3 Y7))
       (ite (and (<= P11 13) a!30) (= H1 (div N11 4)) (= H1 T3))
       (ite (and (<= P11 13) a!30) H3 (= H3 X7))
       (ite (and (<= P11 14) a!31) (= G1 (div N11 4)) (= G1 S3))
       (ite (and (<= P11 14) a!31) G3 (= G3 W7))
       (ite (and (<= P11 15) a!32) (= F1 (div N11 4)) (= F1 R3))
       (ite (and (<= P11 15) a!32) F3 (= F3 V7))
       (ite (and (<= P11 0) a!33) (= C2 (div N11 4)) (= C2 O4))
       (ite (and (<= P11 1) a!34) (= B2 (div N11 4)) (= B2 N4))
       (ite (and (<= P11 1) a!34) J4 (= J4 J8))
       (ite (and (<= P11 3) a!35) (= Z1 (div N11 4)) (= Z1 L4))
       (ite (and (<= P11 3) a!35) H4 (= H4 H8))
       (ite (and (<= P11 5) a!36) (= X1 (div N11 4)) (= X1 B4))
       (ite (and (<= P11 5) a!36) F4 (= F4 F8))
       (ite (and (<= P11 6) a!37) (= W1 (div N11 4)) (= W1 A4))
       (ite (and (<= P11 6) a!37) E4 (= E4 E8))
       (ite (and (<= P11 7) a!38) (= V1 (div N11 4)) (= V1 Z3))
       (ite (and (<= P11 7) a!38) D4 (= D4 D8))
       (ite (and (<= P11 4) a!39) (= Y1 (div N11 4)) (= Y1 K4))
       (ite (and (<= P11 4) a!39) G4 (= G4 G8))
       (ite (and (<= P11 2) a!40) (= A2 (div N11 4)) (= A2 M4))
       (ite (and (<= P11 2) a!40) I4 (= I4 I8))
       (= P9 D7)
       (= O9 C7)
       (= N9 B7)
       (= M9 A7)
       (= L9 Z6)
       (= K9 Y6)
       (= J9 X6)
       (= I9 W6)
       (= Q8 E6)
       (= P8 D6)
       (= O8 C6)
       (= N8 B6)
       (= M8 A6)
       (= L8 Z5)
       (= K8 Y5)
       (= H9 F6)
       (= V9 A8)
       (= U9 Z7)
       (= T9 Y7)
       (= S9 X7)
       (= R9 W7)
       (= Q9 V7)
       (= W9 B8)
       (= X9 C8)
       (= E10 J8)
       (= D10 I8)
       (= C10 H8)
       (= B10 G8)
       (= A10 F8)
       (= Z9 E8)
       (= Y9 D8)
       (= K6 O4)
       (= J6 N4)
       (= I6 M4)
       (= H6 L4)
       (= G6 K4)
       (= N5 R3)
       (= M5 Q3)
       (= L5 P3)
       (= K5 O3)
       (= J5 N3)
       (= P4 T2)
       (= I5 M3)
       (= F9 V6)
       (= E9 U6)
       (= D9 T6)
       (= B11 X8)
       (= A11 W8)
       (= Z10 V8)
       (= Y10 U8)
       (= X10 T8)
       (= W10 S8)
       (= Q4 U2)
       (= O5 S3)
       (= G9 E7)
       (= C11 Y8)
       (= W4 A3)
       (= V4 Z2)
       (= U4 Y2)
       (= T4 X2)
       (= S4 W2)
       (= R4 V2)
       (= U5 Y3)
       (= T5 X3)
       (= S5 W3)
       (= R5 V3)
       (= Q5 U3)
       (= P5 T3)
       (= Z4 D3)
       (= Y4 C3)
       (= X4 B3)
       (= X5 B4)
       (= W5 A4)
       (= V5 Z3)
       (= K10 K7)
       (= J10 J7)
       (= I10 I7)
       (= H10 H7)
       (= G10 G7)
       (= F10 F7)
       (= G11 C9)
       (= F11 B9)
       (= E11 A9)
       (= D11 Z8)
       (= V10 R8)
       (= U10 U7)
       (= T10 T7)
       (= S10 S7)
       (= R10 R7)
       (= Q10 Q7)
       (= P10 P7)
       (= O10 O7)
       (= N10 N7)
       (= M10 M7)
       (= L10 L7)
       (= S11 (+ P11 (div N11 4)))
       (<= (+ P11 (div N11 4)) 64)
       a!41
       (ite (and (<= P11 32) a!1) (= H (div N11 4)) (= H S2))
       (= 1027 v_307)
       (= v_308 false)))
      )
      (transition-5 v_307
              Q11
              S11
              O11
              N11
              P11
              L11
              K11
              J11
              I11
              H11
              C9
              B9
              A9
              Z8
              Y8
              X8
              W8
              V8
              U8
              T8
              S8
              R8
              U7
              T7
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              v_308
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (U7 Int) (V7 Bool) (W7 Bool) (X7 Bool) (Y7 Bool) (Z7 Bool) (A8 Bool) (B8 Bool) (C8 Bool) (D8 Bool) (E8 Bool) (F8 Bool) (G8 Bool) (H8 Bool) (I8 Bool) (J8 Bool) (K8 Bool) (L8 Bool) (M8 Bool) (N8 Bool) (O8 Bool) (P8 Bool) (Q8 Bool) (R8 Int) (S8 Int) (T8 Int) (U8 Int) (V8 Int) (W8 Int) (X8 Int) (Y8 Int) (Z8 Int) (A9 Int) (B9 Int) (C9 Int) (D9 Int) (E9 Int) (F9 Int) (G9 Int) (H9 Bool) (I9 Bool) (J9 Bool) (K9 Bool) (L9 Bool) (M9 Bool) (N9 Bool) (O9 Bool) (P9 Bool) (Q9 Bool) (R9 Bool) (S9 Bool) (T9 Bool) (U9 Bool) (V9 Bool) (W9 Bool) (X9 Bool) (Y9 Bool) (Z9 Bool) (A10 Bool) (B10 Bool) (C10 Bool) (D10 Bool) (E10 Bool) (F10 Int) (G10 Int) (H10 Int) (I10 Int) (J10 Int) (K10 Int) (L10 Int) (M10 Int) (N10 Int) (O10 Int) (P10 Int) (Q10 Int) (R10 Int) (S10 Int) (T10 Int) (U10 Int) (V10 Int) (W10 Int) (X10 Int) (Y10 Int) (Z10 Int) (A11 Int) (B11 Int) (C11 Int) (D11 Int) (E11 Int) (F11 Int) (G11 Int) (H11 Int) (I11 Int) (J11 Int) (K11 Int) (L11 Int) (M11 Int) (N11 Int) (O11 Int) (P11 Int) (Q11 Int) (R11 Int) (S11 Int) (T11 Bool) (U11 Bool) (V11 Bool) (W11 Bool) (X11 Bool) (Y11 Bool) (Z11 Bool) (A12 Bool) (B12 Bool) (C12 Bool) (D12 Bool) (E12 Bool) (F12 Bool) (G12 Bool) (H12 Bool) (I12 Bool) (J12 Bool) (K12 Bool) (L12 Bool) (M12 Bool) (N12 Bool) (O12 Bool) (P12 Bool) (Q12 Bool) (R12 Int) (S12 Int) (T12 Int) (U12 Int) (V12 Int) (W12 Int) (X12 Int) (Y12 Int) (Z12 Int) (A13 Int) (B13 Int) (C13 Int) (D13 Int) (E13 Int) (F13 Int) (G13 Int) (H13 Int) (I13 Int) (J13 Int) (K13 Int) (L13 Int) (M13 Int) (N13 Int) (O13 Int) (P13 Int) (Q13 Int) (R13 Int) (S13 Int) (T13 Int) (U13 Int) (V13 Int) (W13 Int) (X13 Int) (Y13 Int) (Z13 Int) (A14 Int) (B14 Int) (C14 Int) (D14 Int) (E14 Int) (v_369 Int) (v_370 Bool) (v_371 Int) (v_372 Bool) ) 
    (=>
      (and
        (transition-5 v_369
              D14
              B14
              A14
              Z13
              Y13
              X13
              W13
              V13
              U13
              T13
              S13
              R13
              Q13
              P13
              O13
              N13
              M13
              L13
              K13
              J13
              I13
              H13
              G13
              F13
              E13
              D13
              C13
              B13
              A13
              Z12
              Y12
              X12
              W12
              V12
              U12
              T12
              S12
              R12
              S11
              R11
              Q11
              P11
              O11
              N11
              M11
              L11
              K11
              J11
              I11
              H11
              v_370
              Q12
              P12
              O12
              N12
              M12
              L12
              K12
              J12
              I12
              H12
              G12
              F12
              E12
              D12
              C12
              B12
              A12
              Z11
              Y11
              X11
              W11
              V11
              U11
              T11
              E10
              D10
              C10
              B10
              A10
              Z9
              Y9
              X9
              W9
              V9
              U9
              T9
              S9
              R9
              Q9
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5)
        (let ((a!1 (not (<= (+ B14 (div Z13 4)) 40)))
      (a!2 (not (<= (+ B14 (div Z13 4)) 41)))
      (a!3 (not (<= (+ B14 (div Z13 4)) 42)))
      (a!4 (not (<= (+ B14 (div Z13 4)) 43)))
      (a!5 (not (<= (+ B14 (div Z13 4)) 44)))
      (a!6 (not (<= (+ B14 (div Z13 4)) 45)))
      (a!7 (not (<= (+ B14 (div Z13 4)) 46)))
      (a!8 (not (<= (+ B14 (div Z13 4)) 47)))
      (a!9 (not (<= (+ B14 (div Z13 4)) 32)))
      (a!10 (not (<= (+ B14 (div Z13 4)) 33)))
      (a!11 (not (<= (+ B14 (div Z13 4)) 34)))
      (a!12 (not (<= (+ B14 (div Z13 4)) 35)))
      (a!13 (not (<= (+ B14 (div Z13 4)) 36)))
      (a!14 (not (<= (+ B14 (div Z13 4)) 37)))
      (a!15 (not (<= (+ B14 (div Z13 4)) 38)))
      (a!16 (not (<= (+ B14 (div Z13 4)) 39)))
      (a!17 (not (<= (+ B14 (div Z13 4)) 24)))
      (a!18 (not (<= (+ B14 (div Z13 4)) 25)))
      (a!19 (not (<= (+ B14 (div Z13 4)) 26)))
      (a!20 (not (<= (+ B14 (div Z13 4)) 27)))
      (a!21 (not (<= (+ B14 (div Z13 4)) 28)))
      (a!22 (not (<= (+ B14 (div Z13 4)) 29)))
      (a!23 (not (<= (+ B14 (div Z13 4)) 30)))
      (a!24 (not (<= (+ B14 (div Z13 4)) 31)))
      (a!25 (not (<= (+ B14 (div Z13 4)) 16)))
      (a!26 (not (<= (+ B14 (div Z13 4)) 17)))
      (a!27 (not (<= (+ B14 (div Z13 4)) 18)))
      (a!28 (not (<= (+ B14 (div Z13 4)) 19)))
      (a!29 (not (<= (+ B14 (div Z13 4)) 20)))
      (a!30 (not (<= (+ B14 (div Z13 4)) 21)))
      (a!31 (not (<= (+ B14 (div Z13 4)) 22)))
      (a!32 (not (<= (+ B14 (div Z13 4)) 23)))
      (a!33 (not (<= (+ B14 (div Z13 4)) 8)))
      (a!34 (not (<= (+ B14 (div Z13 4)) 9)))
      (a!35 (not (<= (+ B14 (div Z13 4)) 10)))
      (a!36 (not (<= (+ B14 (div Z13 4)) 11)))
      (a!37 (not (<= (+ B14 (div Z13 4)) 12)))
      (a!38 (not (<= (+ B14 (div Z13 4)) 13)))
      (a!39 (not (<= (+ B14 (div Z13 4)) 14)))
      (a!40 (not (<= (+ B14 (div Z13 4)) 15)))
      (a!41 (not (<= (+ B14 (div Z13 4)) 0)))
      (a!42 (not (<= (+ B14 (div Z13 4)) 1)))
      (a!43 (not (<= (+ B14 (div Z13 4)) 3)))
      (a!44 (not (<= (+ B14 (div Z13 4)) 5)))
      (a!45 (not (<= (+ B14 (div Z13 4)) 6)))
      (a!46 (not (<= (+ B14 (div Z13 4)) 7)))
      (a!47 (not (<= (+ B14 (div Z13 4)) 4)))
      (a!48 (not (<= (+ B14 (div Z13 4)) 2)))
      (a!49 (or (not (<= B14 0)) (<= (+ B14 (div Z13 4)) 0))))
  (and (= 1026 v_369)
       (= v_370 false)
       (ite (and (<= B14 40) a!1) I1 (= I1 F6))
       (ite (and (<= B14 41) a!2) (= G (div Z13 4)) (= G Z2))
       (ite (and (<= B14 41) a!2) R (= R E6))
       (ite (and (<= B14 42) a!3) (= F (div Z13 4)) (= F Y2))
       (ite (and (<= B14 42) a!3) Q (= Q D6))
       (ite (and (<= B14 43) a!4) (= E (div Z13 4)) (= E X2))
       (ite (and (<= B14 43) a!4) P (= P C6))
       (ite (and (<= B14 44) a!5) (= D (div Z13 4)) (= D W2))
       (ite (and (<= B14 44) a!5) O (= O B6))
       (ite (and (<= B14 45) a!6) (= C (div Z13 4)) (= C V2))
       (ite (and (<= B14 45) a!6) N (= N A6))
       (ite (and (<= B14 46) a!7) (= B (div Z13 4)) (= B U2))
       (ite (and (<= B14 46) a!7) M (= M Z5))
       (ite (and (<= B14 47) a!8) (= A (div Z13 4)) (= A T2))
       (ite (and (<= B14 47) a!8) L (= L Y5))
       (ite (and (<= B14 32) a!9) (= W (div Z13 4)) (= W Q3))
       (ite (and (<= B14 32) a!9) G2 (= G2 D7))
       (ite (and (<= B14 33) a!10) (= V (div Z13 4)) (= V P3))
       (ite (and (<= B14 33) a!10) P1 (= P1 C7))
       (ite (and (<= B14 34) a!11) (= U (div Z13 4)) (= U O3))
       (ite (and (<= B14 34) a!11) O1 (= O1 B7))
       (ite (and (<= B14 35) a!12) (= T (div Z13 4)) (= T N3))
       (ite (and (<= B14 35) a!12) N1 (= N1 A7))
       (ite (and (<= B14 36) a!13) (= S (div Z13 4)) (= S M3))
       (ite (and (<= B14 36) a!13) M1 (= M1 Z6))
       (ite (and (<= B14 37) a!14) (= K (div Z13 4)) (= K D3))
       (ite (and (<= B14 37) a!14) L1 (= L1 Y6))
       (ite (and (<= B14 38) a!15) (= J (div Z13 4)) (= J C3))
       (ite (and (<= B14 38) a!15) K1 (= K1 X6))
       (ite (and (<= B14 39) a!16) (= I (div Z13 4)) (= I B3))
       (ite (and (<= B14 39) a!16) J1 (= J1 W6))
       (ite (and (<= B14 24) a!17) (= E1 (div Z13 4)) (= E1 Y3))
       (ite (and (<= B14 24) a!17) E3 (= E3 C8))
       (ite (and (<= B14 25) a!18) (= D1 (div Z13 4)) (= D1 X3))
       (ite (and (<= B14 25) a!18) N2 (= N2 B8))
       (ite (and (<= B14 26) a!19) (= C1 (div Z13 4)) (= C1 W3))
       (ite (and (<= B14 26) a!19) M2 (= M2 A8))
       (ite (and (<= B14 27) a!20) (= B1 (div Z13 4)) (= B1 V3))
       (ite (and (<= B14 27) a!20) L2 (= L2 Z7))
       (ite (and (<= B14 28) a!21) (= A1 (div Z13 4)) (= A1 U3))
       (ite (and (<= B14 28) a!21) K2 (= K2 Y7))
       (ite (and (<= B14 29) a!22) (= Z (div Z13 4)) (= Z T3))
       (ite (and (<= B14 29) a!22) J2 (= J2 X7))
       (ite (and (<= B14 30) a!23) (= Y (div Z13 4)) (= Y S3))
       (ite (and (<= B14 30) a!23) I2 (= I2 W7))
       (ite (and (<= B14 31) a!24) (= X (div Z13 4)) (= X R3))
       (ite (and (<= B14 31) a!24) H2 (= H2 V7))
       (ite (and (<= B14 16) a!25) (= U1 (div Z13 4)) (= U1 O4))
       (ite (and (<= B14 16) a!25) C4 (= C4 K8))
       (ite (and (<= B14 17) a!26) (= T1 (div Z13 4)) (= T1 N4))
       (ite (and (<= B14 17) a!26) L3 (= L3 J8))
       (ite (and (<= B14 18) a!27) (= S1 (div Z13 4)) (= S1 M4))
       (ite (and (<= B14 18) a!27) K3 (= K3 I8))
       (ite (and (<= B14 19) a!28) (= R1 (div Z13 4)) (= R1 L4))
       (ite (and (<= B14 19) a!28) J3 (= J3 H8))
       (ite (and (<= B14 20) a!29) (= Q1 (div Z13 4)) (= Q1 K4))
       (ite (and (<= B14 20) a!29) I3 (= I3 G8))
       (ite (and (<= B14 21) a!30) (= H1 (div Z13 4)) (= H1 B4))
       (ite (and (<= B14 21) a!30) H3 (= H3 F8))
       (ite (and (<= B14 22) a!31) (= G1 (div Z13 4)) (= G1 A4))
       (ite (and (<= B14 22) a!31) G3 (= G3 E8))
       (ite (and (<= B14 23) a!32) (= F1 (div Z13 4)) (= F1 Z3))
       (ite (and (<= B14 23) a!32) F3 (= F3 D8))
       (ite (and (<= B14 8) a!33) (= C2 (div Z13 4)) (= C2 W4))
       (ite (and (<= B14 8) a!33) A5 (= A5 I9))
       (ite (and (<= B14 9) a!34) (= B2 (div Z13 4)) (= B2 V4))
       (ite (and (<= B14 9) a!34) J4 (= J4 H9))
       (ite (and (<= B14 10) a!35) (= A2 (div Z13 4)) (= A2 U4))
       (ite (and (<= B14 10) a!35) I4 (= I4 Q8))
       (ite (and (<= B14 11) a!36) (= Z1 (div Z13 4)) (= Z1 T4))
       (ite (and (<= B14 11) a!36) H4 (= H4 P8))
       (ite (and (<= B14 12) a!37) (= Y1 (div Z13 4)) (= Y1 S4))
       (ite (and (<= B14 12) a!37) G4 (= G4 O8))
       (ite (and (<= B14 13) a!38) (= X1 (div Z13 4)) (= X1 R4))
       (ite (and (<= B14 13) a!38) F4 (= F4 N8))
       (ite (and (<= B14 14) a!39) (= W1 (div Z13 4)) (= W1 Q4))
       (ite (and (<= B14 14) a!39) E4 (= E4 M8))
       (ite (and (<= B14 15) a!40) (= V1 (div Z13 4)) (= V1 P4))
       (ite (and (<= B14 15) a!40) D4 (= D4 L8))
       (ite (and (<= B14 0) a!41) (= S2 (div Z13 4)) (= S2 M5))
       (ite (and (<= B14 1) a!42) (= R2 (div Z13 4)) (= R2 L5))
       (ite (and (<= B14 1) a!42) H5 (= H5 P9))
       (ite (and (<= B14 3) a!43) (= P2 (div Z13 4)) (= P2 J5))
       (ite (and (<= B14 3) a!43) F5 (= F5 N9))
       (ite (and (<= B14 5) a!44) (= F2 (div Z13 4)) (= F2 Z4))
       (ite (and (<= B14 5) a!44) D5 (= D5 L9))
       (ite (and (<= B14 6) a!45) (= E2 (div Z13 4)) (= E2 Y4))
       (ite (and (<= B14 6) a!45) C5 (= C5 K9))
       (ite (and (<= B14 7) a!46) (= D2 (div Z13 4)) (= D2 X4))
       (ite (and (<= B14 7) a!46) B5 (= B5 J9))
       (ite (and (<= B14 4) a!47) (= O2 (div Z13 4)) (= O2 I5))
       (ite (and (<= B14 4) a!47) E5 (= E5 M9))
       (ite (and (<= B14 2) a!48) (= Q2 (div Z13 4)) (= Q2 K5))
       (ite (and (<= B14 2) a!48) G5 (= G5 O9))
       (= B12 K8)
       (= A12 J8)
       (= Z11 I8)
       (= Y11 H8)
       (= X11 G8)
       (= W11 F8)
       (= V11 E8)
       (= U11 D8)
       (= E10 B8)
       (= D10 A8)
       (= C10 Z7)
       (= B10 Y7)
       (= A10 X7)
       (= Z9 W7)
       (= Y9 V7)
       (= T11 C8)
       (= X9 D7)
       (= H12 Q8)
       (= G12 P8)
       (= F12 O8)
       (= E12 N8)
       (= D12 M8)
       (= C12 L8)
       (= I12 H9)
       (= W9 C7)
       (= V9 B7)
       (= U9 A7)
       (= T9 Z6)
       (= S9 Y6)
       (= R9 X6)
       (= Q9 W6)
       (= J12 I9)
       (= Q12 P9)
       (= P12 O9)
       (= O12 N9)
       (= N12 M9)
       (= M12 L9)
       (= L12 K9)
       (= K12 J9)
       (= J6 X3)
       (= I6 W3)
       (= H6 V3)
       (= G6 U3)
       (= P5 D3)
       (= O5 C3)
       (= N5 B3)
       (= X5 T3)
       (= W5 S3)
       (= V5 R3)
       (= U5 Q3)
       (= T5 P3)
       (= S5 O3)
       (= R5 N3)
       (= Q5 M3)
       (= R11 F9)
       (= Q11 E9)
       (= P11 D9)
       (= O11 C9)
       (= N11 B9)
       (= M11 A9)
       (= N13 B11)
       (= M13 A11)
       (= L13 Z10)
       (= K13 Y10)
       (= J13 X10)
       (= I13 W10)
       (= K6 Y3)
       (= S11 G9)
       (= O13 C11)
       (= I7 W4)
       (= H7 V4)
       (= G7 U4)
       (= F7 T4)
       (= E7 S4)
       (= V6 R4)
       (= U6 Q4)
       (= T6 P4)
       (= S6 O4)
       (= R6 N4)
       (= Q6 M4)
       (= P6 L4)
       (= O6 K4)
       (= N6 B4)
       (= M6 A4)
       (= L6 Z3)
       (= Q7 M5)
       (= P7 L5)
       (= O7 K5)
       (= N7 J5)
       (= M7 I5)
       (= L7 Z4)
       (= K7 Y4)
       (= J7 X4)
       (= L11 Z8)
       (= K11 Y8)
       (= J11 X8)
       (= I11 W8)
       (= H11 V8)
       (= W12 K10)
       (= V12 J10)
       (= U12 I10)
       (= T12 H10)
       (= S12 G10)
       (= R12 F10)
       (= S13 G11)
       (= R13 F11)
       (= Q13 E11)
       (= P13 D11)
       (= H13 V10)
       (= G13 U10)
       (= F13 T10)
       (= E13 S10)
       (= D13 R10)
       (= C13 Q10)
       (= B13 P10)
       (= A13 O10)
       (= Z12 N10)
       (= Y12 M10)
       (= X12 L10)
       (= E14 (+ B14 (div Z13 4)))
       (<= (+ B14 (div Z13 4)) 64)
       a!49
       (ite (and (<= B14 40) a!1) (= H (div Z13 4)) (= H A3))
       (= 1027 v_371)
       (= v_372 false)))
      )
      (transition-6 v_371
              C14
              E14
              A14
              Z13
              B14
              X13
              W13
              V13
              U13
              T13
              G11
              F11
              E11
              D11
              C11
              B11
              A11
              Z10
              Y10
              X10
              W10
              V10
              U10
              T10
              S10
              R10
              Q10
              P10
              O10
              N10
              M10
              L10
              K10
              J10
              I10
              H10
              G10
              F10
              G9
              F9
              E9
              D9
              C9
              B9
              A9
              Z8
              Y8
              X8
              W8
              V8
              U8
              T8
              S8
              R8
              U7
              T7
              S7
              R7
              v_372
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (U7 Int) (V7 Bool) (W7 Bool) (X7 Bool) (Y7 Bool) (Z7 Bool) (A8 Bool) (B8 Bool) (C8 Bool) (D8 Bool) (E8 Bool) (F8 Bool) (G8 Bool) (H8 Bool) (I8 Bool) (J8 Bool) (K8 Bool) (L8 Bool) (M8 Bool) (N8 Bool) (O8 Bool) (P8 Bool) (Q8 Bool) (R8 Int) (S8 Int) (T8 Int) (U8 Int) (V8 Int) (W8 Int) (X8 Int) (Y8 Int) (Z8 Int) (A9 Int) (B9 Int) (C9 Int) (D9 Int) (E9 Int) (F9 Int) (G9 Int) (H9 Bool) (I9 Bool) (J9 Bool) (K9 Bool) (L9 Bool) (M9 Bool) (N9 Bool) (O9 Bool) (P9 Bool) (Q9 Bool) (R9 Bool) (S9 Bool) (T9 Bool) (U9 Bool) (V9 Bool) (W9 Bool) (X9 Bool) (Y9 Bool) (Z9 Bool) (A10 Bool) (B10 Bool) (C10 Bool) (D10 Bool) (E10 Bool) (F10 Int) (G10 Int) (H10 Int) (I10 Int) (J10 Int) (K10 Int) (L10 Int) (M10 Int) (N10 Int) (O10 Int) (P10 Int) (Q10 Int) (R10 Int) (S10 Int) (T10 Int) (U10 Int) (V10 Int) (W10 Int) (X10 Int) (Y10 Int) (Z10 Int) (A11 Int) (B11 Int) (C11 Int) (D11 Int) (E11 Int) (F11 Int) (G11 Int) (H11 Int) (I11 Int) (J11 Int) (K11 Int) (L11 Int) (M11 Int) (N11 Int) (O11 Int) (P11 Int) (Q11 Int) (R11 Int) (S11 Int) (T11 Bool) (U11 Bool) (V11 Bool) (W11 Bool) (X11 Bool) (Y11 Bool) (Z11 Bool) (A12 Bool) (B12 Bool) (C12 Bool) (D12 Bool) (E12 Bool) (F12 Bool) (G12 Bool) (H12 Bool) (I12 Bool) (J12 Bool) (K12 Bool) (L12 Bool) (M12 Bool) (N12 Bool) (O12 Bool) (P12 Bool) (Q12 Bool) (R12 Int) (S12 Int) (T12 Int) (U12 Int) (V12 Int) (W12 Int) (X12 Int) (Y12 Int) (Z12 Int) (A13 Int) (B13 Int) (C13 Int) (D13 Int) (E13 Int) (F13 Int) (G13 Int) (H13 Int) (I13 Int) (J13 Int) (K13 Int) (L13 Int) (M13 Int) (N13 Int) (O13 Int) (P13 Int) (Q13 Int) (R13 Int) (S13 Int) (T13 Int) (U13 Int) (V13 Int) (W13 Int) (X13 Int) (Y13 Int) (Z13 Int) (A14 Int) (B14 Int) (C14 Int) (D14 Int) (E14 Int) (F14 Bool) (G14 Bool) (H14 Bool) (I14 Bool) (J14 Bool) (K14 Bool) (L14 Bool) (M14 Bool) (N14 Bool) (O14 Bool) (P14 Bool) (Q14 Bool) (R14 Bool) (S14 Bool) (T14 Bool) (U14 Bool) (V14 Bool) (W14 Bool) (X14 Bool) (Y14 Bool) (Z14 Bool) (A15 Bool) (B15 Bool) (C15 Bool) (D15 Int) (E15 Int) (F15 Int) (G15 Int) (H15 Int) (I15 Int) (J15 Int) (K15 Int) (L15 Int) (M15 Int) (N15 Int) (O15 Int) (P15 Int) (Q15 Int) (R15 Int) (S15 Int) (T15 Int) (U15 Int) (V15 Int) (W15 Int) (X15 Int) (Y15 Int) (Z15 Int) (A16 Int) (B16 Int) (C16 Int) (D16 Int) (E16 Int) (F16 Int) (G16 Int) (H16 Int) (I16 Int) (J16 Int) (K16 Int) (L16 Int) (M16 Int) (N16 Int) (O16 Int) (P16 Int) (Q16 Int) (v_433 Int) (v_434 Bool) (v_435 Int) (v_436 Bool) ) 
    (=>
      (and
        (transition-6 v_433
              P16
              N16
              M16
              L16
              K16
              J16
              I16
              H16
              G16
              F16
              E16
              D16
              C16
              B16
              A16
              Z15
              Y15
              X15
              W15
              V15
              U15
              T15
              S15
              R15
              Q15
              P15
              O15
              N15
              M15
              L15
              K15
              J15
              I15
              H15
              G15
              F15
              E15
              D15
              E14
              D14
              C14
              B14
              A14
              Z13
              Y13
              X13
              W13
              V13
              U13
              T13
              S13
              R13
              Q13
              P13
              O13
              N13
              M13
              L13
              v_434
              C15
              B15
              A15
              Z14
              Y14
              X14
              W14
              V14
              U14
              T14
              S14
              R14
              Q14
              P14
              O14
              N14
              M14
              L14
              K14
              J14
              I14
              H14
              G14
              F14
              Q12
              P12
              O12
              N12
              M12
              L12
              K12
              J12
              I12
              H12
              G12
              F12
              E12
              D12
              C12
              B12
              A12
              Z11
              Y11
              X11
              W11
              V11
              U11
              I10
              H10
              G10
              F10
              G9
              F9
              E9
              D9
              C9
              B9
              A9
              Z8
              Y8
              X8
              W8
              V8
              U8
              T8
              S8
              R8
              U7
              T7
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6)
        (let ((a!1 (not (<= (+ N16 (div L16 4)) 48)))
      (a!2 (not (<= (+ N16 (div L16 4)) 49)))
      (a!3 (not (<= (+ N16 (div L16 4)) 50)))
      (a!4 (not (<= (+ N16 (div L16 4)) 51)))
      (a!5 (not (<= (+ N16 (div L16 4)) 52)))
      (a!6 (not (<= (+ N16 (div L16 4)) 53)))
      (a!7 (not (<= (+ N16 (div L16 4)) 54)))
      (a!8 (not (<= (+ N16 (div L16 4)) 55)))
      (a!9 (not (<= (+ N16 (div L16 4)) 40)))
      (a!10 (not (<= (+ N16 (div L16 4)) 41)))
      (a!11 (not (<= (+ N16 (div L16 4)) 42)))
      (a!12 (not (<= (+ N16 (div L16 4)) 43)))
      (a!13 (not (<= (+ N16 (div L16 4)) 44)))
      (a!14 (not (<= (+ N16 (div L16 4)) 45)))
      (a!15 (not (<= (+ N16 (div L16 4)) 46)))
      (a!16 (not (<= (+ N16 (div L16 4)) 47)))
      (a!17 (not (<= (+ N16 (div L16 4)) 32)))
      (a!18 (not (<= (+ N16 (div L16 4)) 33)))
      (a!19 (not (<= (+ N16 (div L16 4)) 34)))
      (a!20 (not (<= (+ N16 (div L16 4)) 35)))
      (a!21 (not (<= (+ N16 (div L16 4)) 36)))
      (a!22 (not (<= (+ N16 (div L16 4)) 37)))
      (a!23 (not (<= (+ N16 (div L16 4)) 38)))
      (a!24 (not (<= (+ N16 (div L16 4)) 39)))
      (a!25 (not (<= (+ N16 (div L16 4)) 24)))
      (a!26 (not (<= (+ N16 (div L16 4)) 25)))
      (a!27 (not (<= (+ N16 (div L16 4)) 26)))
      (a!28 (not (<= (+ N16 (div L16 4)) 27)))
      (a!29 (not (<= (+ N16 (div L16 4)) 28)))
      (a!30 (not (<= (+ N16 (div L16 4)) 29)))
      (a!31 (not (<= (+ N16 (div L16 4)) 30)))
      (a!32 (not (<= (+ N16 (div L16 4)) 31)))
      (a!33 (not (<= (+ N16 (div L16 4)) 16)))
      (a!34 (not (<= (+ N16 (div L16 4)) 17)))
      (a!35 (not (<= (+ N16 (div L16 4)) 18)))
      (a!36 (not (<= (+ N16 (div L16 4)) 19)))
      (a!37 (not (<= (+ N16 (div L16 4)) 20)))
      (a!38 (not (<= (+ N16 (div L16 4)) 21)))
      (a!39 (not (<= (+ N16 (div L16 4)) 22)))
      (a!40 (not (<= (+ N16 (div L16 4)) 23)))
      (a!41 (not (<= (+ N16 (div L16 4)) 8)))
      (a!42 (not (<= (+ N16 (div L16 4)) 9)))
      (a!43 (not (<= (+ N16 (div L16 4)) 10)))
      (a!44 (not (<= (+ N16 (div L16 4)) 11)))
      (a!45 (not (<= (+ N16 (div L16 4)) 12)))
      (a!46 (not (<= (+ N16 (div L16 4)) 13)))
      (a!47 (not (<= (+ N16 (div L16 4)) 14)))
      (a!48 (not (<= (+ N16 (div L16 4)) 15)))
      (a!49 (not (<= (+ N16 (div L16 4)) 0)))
      (a!50 (not (<= (+ N16 (div L16 4)) 1)))
      (a!51 (not (<= (+ N16 (div L16 4)) 3)))
      (a!52 (not (<= (+ N16 (div L16 4)) 5)))
      (a!53 (not (<= (+ N16 (div L16 4)) 6)))
      (a!54 (not (<= (+ N16 (div L16 4)) 7)))
      (a!55 (not (<= (+ N16 (div L16 4)) 4)))
      (a!56 (not (<= (+ N16 (div L16 4)) 2)))
      (a!57 (or (not (<= N16 0)) (<= (+ N16 (div L16 4)) 0))))
  (and (= 1026 v_433)
       (= v_434 false)
       (ite (and (<= N16 48) a!1) I1 (= I1 D7))
       (ite (and (<= N16 49) a!2) (= G (div L16 4)) (= G P3))
       (ite (and (<= N16 49) a!2) R (= R C7))
       (ite (and (<= N16 50) a!3) (= F (div L16 4)) (= F O3))
       (ite (and (<= N16 50) a!3) Q (= Q B7))
       (ite (and (<= N16 51) a!4) (= E (div L16 4)) (= E N3))
       (ite (and (<= N16 51) a!4) P (= P A7))
       (ite (and (<= N16 52) a!5) (= D (div L16 4)) (= D M3))
       (ite (and (<= N16 52) a!5) O (= O Z6))
       (ite (and (<= N16 53) a!6) (= C (div L16 4)) (= C D3))
       (ite (and (<= N16 53) a!6) N (= N Y6))
       (ite (and (<= N16 54) a!7) (= B (div L16 4)) (= B C3))
       (ite (and (<= N16 54) a!7) M (= M X6))
       (ite (and (<= N16 55) a!8) (= A (div L16 4)) (= A B3))
       (ite (and (<= N16 55) a!8) L (= L W6))
       (ite (and (<= N16 40) a!9) (= W (div L16 4)) (= W Y3))
       (ite (and (<= N16 40) a!9) G2 (= G2 C8))
       (ite (and (<= N16 41) a!10) (= V (div L16 4)) (= V X3))
       (ite (and (<= N16 41) a!10) P1 (= P1 B8))
       (ite (and (<= N16 42) a!11) (= U (div L16 4)) (= U W3))
       (ite (and (<= N16 42) a!11) O1 (= O1 A8))
       (ite (and (<= N16 43) a!12) (= T (div L16 4)) (= T V3))
       (ite (and (<= N16 43) a!12) N1 (= N1 Z7))
       (ite (and (<= N16 44) a!13) (= S (div L16 4)) (= S U3))
       (ite (and (<= N16 44) a!13) M1 (= M1 Y7))
       (ite (and (<= N16 45) a!14) (= K (div L16 4)) (= K T3))
       (ite (and (<= N16 45) a!14) L1 (= L1 X7))
       (ite (and (<= N16 46) a!15) (= J (div L16 4)) (= J S3))
       (ite (and (<= N16 46) a!15) K1 (= K1 W7))
       (ite (and (<= N16 47) a!16) (= I (div L16 4)) (= I R3))
       (ite (and (<= N16 47) a!16) J1 (= J1 V7))
       (ite (and (<= N16 32) a!17) (= E1 (div L16 4)) (= E1 O4))
       (ite (and (<= N16 32) a!17) E3 (= E3 K8))
       (ite (and (<= N16 33) a!18) (= D1 (div L16 4)) (= D1 N4))
       (ite (and (<= N16 33) a!18) N2 (= N2 J8))
       (ite (and (<= N16 34) a!19) (= C1 (div L16 4)) (= C1 M4))
       (ite (and (<= N16 34) a!19) M2 (= M2 I8))
       (ite (and (<= N16 35) a!20) (= B1 (div L16 4)) (= B1 L4))
       (ite (and (<= N16 35) a!20) L2 (= L2 H8))
       (ite (and (<= N16 36) a!21) (= A1 (div L16 4)) (= A1 K4))
       (ite (and (<= N16 36) a!21) K2 (= K2 G8))
       (ite (and (<= N16 37) a!22) (= Z (div L16 4)) (= Z B4))
       (ite (and (<= N16 37) a!22) J2 (= J2 F8))
       (ite (and (<= N16 38) a!23) (= Y (div L16 4)) (= Y A4))
       (ite (and (<= N16 38) a!23) I2 (= I2 E8))
       (ite (and (<= N16 39) a!24) (= X (div L16 4)) (= X Z3))
       (ite (and (<= N16 39) a!24) H2 (= H2 D8))
       (ite (and (<= N16 24) a!25) (= U1 (div L16 4)) (= U1 W4))
       (ite (and (<= N16 24) a!25) C4 (= C4 I9))
       (ite (and (<= N16 25) a!26) (= T1 (div L16 4)) (= T1 V4))
       (ite (and (<= N16 25) a!26) L3 (= L3 H9))
       (ite (and (<= N16 26) a!27) (= S1 (div L16 4)) (= S1 U4))
       (ite (and (<= N16 26) a!27) K3 (= K3 Q8))
       (ite (and (<= N16 27) a!28) (= R1 (div L16 4)) (= R1 T4))
       (ite (and (<= N16 27) a!28) J3 (= J3 P8))
       (ite (and (<= N16 28) a!29) (= Q1 (div L16 4)) (= Q1 S4))
       (ite (and (<= N16 28) a!29) I3 (= I3 O8))
       (ite (and (<= N16 29) a!30) (= H1 (div L16 4)) (= H1 R4))
       (ite (and (<= N16 29) a!30) H3 (= H3 N8))
       (ite (and (<= N16 30) a!31) (= G1 (div L16 4)) (= G1 Q4))
       (ite (and (<= N16 30) a!31) G3 (= G3 M8))
       (ite (and (<= N16 31) a!32) (= F1 (div L16 4)) (= F1 P4))
       (ite (and (<= N16 31) a!32) F3 (= F3 L8))
       (ite (and (<= N16 16) a!33) (= C2 (div L16 4)) (= C2 M5))
       (ite (and (<= N16 16) a!33) A5 (= A5 Q9))
       (ite (and (<= N16 17) a!34) (= B2 (div L16 4)) (= B2 L5))
       (ite (and (<= N16 17) a!34) J4 (= J4 P9))
       (ite (and (<= N16 18) a!35) (= A2 (div L16 4)) (= A2 K5))
       (ite (and (<= N16 18) a!35) I4 (= I4 O9))
       (ite (and (<= N16 19) a!36) (= Z1 (div L16 4)) (= Z1 J5))
       (ite (and (<= N16 19) a!36) H4 (= H4 N9))
       (ite (and (<= N16 20) a!37) (= Y1 (div L16 4)) (= Y1 I5))
       (ite (and (<= N16 20) a!37) G4 (= G4 M9))
       (ite (and (<= N16 21) a!38) (= X1 (div L16 4)) (= X1 Z4))
       (ite (and (<= N16 21) a!38) F4 (= F4 L9))
       (ite (and (<= N16 22) a!39) (= W1 (div L16 4)) (= W1 Y4))
       (ite (and (<= N16 22) a!39) E4 (= E4 K9))
       (ite (and (<= N16 23) a!40) (= V1 (div L16 4)) (= V1 X4))
       (ite (and (<= N16 23) a!40) D4 (= D4 J9))
       (ite (and (<= N16 8) a!41) (= S2 (div L16 4)) (= S2 U5))
       (ite (and (<= N16 8) a!41) Y5 (= Y5 Y9))
       (ite (and (<= N16 9) a!42) (= R2 (div L16 4)) (= R2 T5))
       (ite (and (<= N16 9) a!42) H5 (= H5 X9))
       (ite (and (<= N16 10) a!43) (= Q2 (div L16 4)) (= Q2 S5))
       (ite (and (<= N16 10) a!43) G5 (= G5 W9))
       (ite (and (<= N16 11) a!44) (= P2 (div L16 4)) (= P2 R5))
       (ite (and (<= N16 11) a!44) F5 (= F5 V9))
       (ite (and (<= N16 12) a!45) (= O2 (div L16 4)) (= O2 Q5))
       (ite (and (<= N16 12) a!45) E5 (= E5 U9))
       (ite (and (<= N16 13) a!46) (= F2 (div L16 4)) (= F2 P5))
       (ite (and (<= N16 13) a!46) D5 (= D5 T9))
       (ite (and (<= N16 14) a!47) (= E2 (div L16 4)) (= E2 O5))
       (ite (and (<= N16 14) a!47) C5 (= C5 S9))
       (ite (and (<= N16 15) a!48) (= D2 (div L16 4)) (= D2 N5))
       (ite (and (<= N16 15) a!48) B5 (= B5 R9))
       (ite (and (<= N16 0) a!49) (= A3 (div L16 4)) (= A3 K6))
       (ite (and (<= N16 1) a!50) (= Z2 (div L16 4)) (= Z2 J6))
       (ite (and (<= N16 1) a!50) F6 (= F6 T11))
       (ite (and (<= N16 3) a!51) (= X2 (div L16 4)) (= X2 H6))
       (ite (and (<= N16 3) a!51) D6 (= D6 D10))
       (ite (and (<= N16 5) a!52) (= V2 (div L16 4)) (= V2 X5))
       (ite (and (<= N16 5) a!52) B6 (= B6 B10))
       (ite (and (<= N16 6) a!53) (= U2 (div L16 4)) (= U2 W5))
       (ite (and (<= N16 6) a!53) A6 (= A6 A10))
       (ite (and (<= N16 7) a!54) (= T2 (div L16 4)) (= T2 V5))
       (ite (and (<= N16 7) a!54) Z5 (= Z5 Z9))
       (ite (and (<= N16 4) a!55) (= W2 (div L16 4)) (= W2 G6))
       (ite (and (<= N16 4) a!55) C6 (= C6 C10))
       (ite (and (<= N16 2) a!56) (= Y2 (div L16 4)) (= Y2 I6))
       (ite (and (<= N16 2) a!56) E6 (= E6 E10))
       (= Z11 A8)
       (= Y11 Z7)
       (= X11 Y7)
       (= W11 X7)
       (= V11 W7)
       (= U11 V7)
       (= N14 Q9)
       (= M14 P9)
       (= L14 O9)
       (= K14 N9)
       (= J14 M9)
       (= I14 L9)
       (= H14 K9)
       (= G14 J9)
       (= Q12 H9)
       (= P12 Q8)
       (= O12 P8)
       (= N12 O8)
       (= M12 N8)
       (= L12 M8)
       (= K12 L8)
       (= F14 I9)
       (= J12 K8)
       (= T14 W9)
       (= S14 V9)
       (= R14 U9)
       (= Q14 T9)
       (= P14 S9)
       (= O14 R9)
       (= A12 B8)
       (= U14 X9)
       (= B12 C8)
       (= I12 J8)
       (= H12 I8)
       (= G12 H8)
       (= F12 G8)
       (= E12 F8)
       (= D12 E8)
       (= C12 D8)
       (= V14 Y9)
       (= C15 T11)
       (= B15 E10)
       (= A15 D10)
       (= Z14 C10)
       (= Y14 B10)
       (= X14 A10)
       (= W14 Z9)
       (= J7 P4)
       (= I7 O4)
       (= H7 N4)
       (= G7 M4)
       (= F7 L4)
       (= E7 K4)
       (= N6 T3)
       (= M6 S3)
       (= L6 R3)
       (= V8 N5)
       (= U8 M5)
       (= T8 L5)
       (= S8 K5)
       (= V6 B4)
       (= U6 A4)
       (= T6 Z3)
       (= S6 Y3)
       (= R6 X3)
       (= Q6 W3)
       (= P6 V3)
       (= O6 U3)
       (= I10 K6)
       (= H10 J6)
       (= R8 J5)
       (= U7 I5)
       (= T7 Z4)
       (= S7 Y4)
       (= R7 X4)
       (= Q7 W4)
       (= P7 V4)
       (= O7 U4)
       (= N7 T4)
       (= M7 S4)
       (= L7 R4)
       (= K7 Q4)
       (= G10 I6)
       (= D14 J11)
       (= C14 I11)
       (= B14 H11)
       (= A14 G11)
       (= Z13 F11)
       (= Y13 E11)
       (= Z15 F13)
       (= Y15 E13)
       (= X15 D13)
       (= W15 C13)
       (= V15 B13)
       (= U15 A13)
       (= W8 O5)
       (= E14 K11)
       (= A16 G13)
       (= G9 G6)
       (= F9 X5)
       (= E9 W5)
       (= D9 V5)
       (= C9 U5)
       (= B9 T5)
       (= A9 S5)
       (= Z8 R5)
       (= Y8 Q5)
       (= X8 P5)
       (= F10 H6)
       (= M13 S10)
       (= L13 R10)
       (= X13 D11)
       (= W13 C11)
       (= V13 B11)
       (= U13 A11)
       (= T13 Z10)
       (= S13 Y10)
       (= R13 X10)
       (= Q13 W10)
       (= P13 V10)
       (= O13 U10)
       (= N13 T10)
       (= I15 Q11)
       (= H15 P11)
       (= G15 O11)
       (= F15 N11)
       (= E15 M11)
       (= D15 L11)
       (= E16 K13)
       (= D16 J13)
       (= C16 I13)
       (= B16 H13)
       (= T15 Z12)
       (= S15 Y12)
       (= R15 X12)
       (= Q15 W12)
       (= P15 V12)
       (= O15 U12)
       (= N15 T12)
       (= M15 S12)
       (= L15 R12)
       (= K15 S11)
       (= J15 R11)
       (= Q16 (+ N16 (div L16 4)))
       (<= (+ N16 (div L16 4)) 64)
       a!57
       (ite (and (<= N16 48) a!1) (= H (div L16 4)) (= H Q3))
       (= 1027 v_435)
       (= v_436 false)))
      )
      (transition-7 v_435
              O16
              Q16
              M16
              L16
              N16
              J16
              I16
              H16
              G16
              F16
              K13
              J13
              I13
              H13
              G13
              F13
              E13
              D13
              C13
              B13
              A13
              Z12
              Y12
              X12
              W12
              V12
              U12
              T12
              S12
              R12
              S11
              R11
              Q11
              P11
              O11
              N11
              M11
              L11
              K11
              J11
              I11
              H11
              G11
              F11
              E11
              D11
              C11
              B11
              A11
              Z10
              Y10
              X10
              W10
              V10
              U10
              T10
              S10
              R10
              Q10
              P10
              O10
              N10
              M10
              L10
              K10
              J10
              v_436
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (U7 Int) (V7 Bool) (W7 Bool) (X7 Bool) (Y7 Bool) (Z7 Bool) (A8 Bool) (B8 Bool) (C8 Bool) (D8 Bool) (E8 Bool) (F8 Bool) (G8 Bool) (H8 Bool) (I8 Bool) (J8 Bool) (K8 Bool) (L8 Bool) (M8 Bool) (N8 Bool) (O8 Bool) (P8 Bool) (Q8 Bool) (R8 Int) (S8 Int) (T8 Int) (U8 Int) (V8 Int) (W8 Int) (X8 Int) (Y8 Int) (Z8 Int) (A9 Int) (B9 Int) (C9 Int) (D9 Int) (E9 Int) (F9 Int) (G9 Int) (H9 Bool) (I9 Bool) (J9 Bool) (K9 Bool) (L9 Bool) (M9 Bool) (N9 Bool) (O9 Bool) (P9 Bool) (Q9 Bool) (R9 Bool) (S9 Bool) (T9 Bool) (U9 Bool) (V9 Bool) (W9 Bool) (X9 Bool) (Y9 Bool) (Z9 Bool) (A10 Bool) (B10 Bool) (C10 Bool) (D10 Bool) (E10 Bool) (F10 Int) (G10 Int) (H10 Int) (I10 Int) (J10 Int) (K10 Int) (L10 Int) (M10 Int) (N10 Int) (O10 Int) (P10 Int) (Q10 Int) (R10 Int) (S10 Int) (T10 Int) (U10 Int) (V10 Int) (W10 Int) (X10 Int) (Y10 Int) (Z10 Int) (A11 Int) (B11 Int) (C11 Int) (D11 Int) (E11 Int) (F11 Int) (G11 Int) (H11 Int) (I11 Int) (J11 Int) (K11 Int) (L11 Int) (M11 Int) (N11 Int) (O11 Int) (P11 Int) (Q11 Int) (R11 Int) (S11 Int) (T11 Bool) (U11 Bool) (V11 Bool) (W11 Bool) (X11 Bool) (Y11 Bool) (Z11 Bool) (A12 Bool) (B12 Bool) (C12 Bool) (D12 Bool) (E12 Bool) (F12 Bool) (G12 Bool) (H12 Bool) (I12 Bool) (J12 Bool) (K12 Bool) (L12 Bool) (M12 Bool) (N12 Bool) (O12 Bool) (P12 Bool) (Q12 Bool) (R12 Int) (S12 Int) (T12 Int) (U12 Int) (V12 Int) (W12 Int) (X12 Int) (Y12 Int) (Z12 Int) (A13 Int) (B13 Int) (C13 Int) (D13 Int) (E13 Int) (F13 Int) (G13 Int) (H13 Int) (I13 Int) (J13 Int) (K13 Int) (L13 Int) (M13 Int) (N13 Int) (O13 Int) (P13 Int) (Q13 Int) (R13 Int) (S13 Int) (T13 Int) (U13 Int) (V13 Int) (W13 Int) (X13 Int) (Y13 Int) (Z13 Int) (A14 Int) (B14 Int) (C14 Int) (D14 Int) (E14 Int) (F14 Bool) (G14 Bool) (H14 Bool) (I14 Bool) (J14 Bool) (K14 Bool) (L14 Bool) (M14 Bool) (N14 Bool) (O14 Bool) (P14 Bool) (Q14 Bool) (R14 Bool) (S14 Bool) (T14 Bool) (U14 Bool) (V14 Bool) (W14 Bool) (X14 Bool) (Y14 Bool) (Z14 Bool) (A15 Bool) (B15 Bool) (C15 Bool) (D15 Int) (E15 Int) (F15 Int) (G15 Int) (H15 Int) (I15 Int) (J15 Int) (K15 Int) (L15 Int) (M15 Int) (N15 Int) (O15 Int) (P15 Int) (Q15 Int) (R15 Int) (S15 Int) (T15 Int) (U15 Int) (V15 Int) (W15 Int) (X15 Int) (Y15 Int) (Z15 Int) (A16 Int) (B16 Int) (C16 Int) (D16 Int) (E16 Int) (F16 Int) (G16 Int) (H16 Int) (I16 Int) (J16 Int) (K16 Int) (L16 Int) (M16 Int) (N16 Int) (O16 Int) (P16 Int) (Q16 Int) (R16 Bool) (S16 Bool) (T16 Bool) (U16 Bool) (V16 Bool) (W16 Bool) (X16 Bool) (Y16 Bool) (Z16 Bool) (A17 Bool) (B17 Bool) (C17 Bool) (D17 Bool) (E17 Bool) (F17 Bool) (G17 Bool) (H17 Bool) (I17 Bool) (J17 Bool) (K17 Bool) (L17 Bool) (M17 Bool) (N17 Bool) (O17 Bool) (P17 Int) (Q17 Int) (R17 Int) (S17 Int) (T17 Int) (U17 Int) (V17 Int) (W17 Int) (X17 Int) (Y17 Int) (Z17 Int) (A18 Int) (B18 Int) (C18 Int) (D18 Int) (E18 Int) (F18 Int) (G18 Int) (H18 Int) (I18 Int) (J18 Int) (K18 Int) (L18 Int) (M18 Int) (N18 Int) (O18 Int) (P18 Int) (Q18 Int) (R18 Int) (S18 Int) (T18 Int) (U18 Int) (V18 Int) (W18 Int) (X18 Int) (Y18 Int) (Z18 Int) (A19 Int) (B19 Int) (C19 Int) (v_497 Int) (v_498 Bool) (v_499 Int) (v_500 Bool) ) 
    (=>
      (and
        (transition-7 v_497
              B19
              Z18
              Y18
              X18
              W18
              V18
              U18
              T18
              S18
              R18
              Q18
              P18
              O18
              N18
              M18
              L18
              K18
              J18
              I18
              H18
              G18
              F18
              E18
              D18
              C18
              B18
              A18
              Z17
              Y17
              X17
              W17
              V17
              U17
              T17
              S17
              R17
              Q17
              P17
              Q16
              P16
              O16
              N16
              M16
              L16
              K16
              J16
              I16
              H16
              G16
              F16
              E16
              D16
              C16
              B16
              A16
              Z15
              Y15
              X15
              W15
              V15
              U15
              T15
              S15
              R15
              Q15
              P15
              v_498
              O17
              N17
              M17
              L17
              K17
              J17
              I17
              H17
              G17
              F17
              E17
              D17
              C17
              B17
              A17
              Z16
              Y16
              X16
              W16
              V16
              U16
              T16
              S16
              R16
              C15
              B15
              A15
              Z14
              Y14
              X14
              W14
              V14
              U14
              T14
              S14
              R14
              Q14
              P14
              O14
              N14
              M14
              L14
              K14
              J14
              I14
              H14
              G14
              F14
              Q12
              P12
              O12
              N12
              M12
              L12
              K12
              G11
              F11
              E11
              D11
              C11
              B11
              A11
              Z10
              Y10
              X10
              W10
              V10
              U10
              T10
              S10
              R10
              Q10
              P10
              O10
              N10
              M10
              L10
              K10
              J10
              I10
              H10
              G10
              F10
              G9
              F9
              E9
              D9
              C9
              B9
              A9
              Z8
              Y8
              X8
              W8
              V8
              U8
              T8
              S8
              R8
              U7
              T7
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7)
        (let ((a!1 (not (<= (+ Z18 (div X18 4)) 56)))
      (a!2 (not (<= (+ Z18 (div X18 4)) 57)))
      (a!3 (not (<= (+ Z18 (div X18 4)) 58)))
      (a!4 (not (<= (+ Z18 (div X18 4)) 59)))
      (a!5 (not (<= (+ Z18 (div X18 4)) 60)))
      (a!6 (not (<= (+ Z18 (div X18 4)) 61)))
      (a!7 (not (<= (+ Z18 (div X18 4)) 62)))
      (a!8 (not (<= (+ Z18 (div X18 4)) 63)))
      (a!9 (not (<= (+ Z18 (div X18 4)) 48)))
      (a!10 (not (<= (+ Z18 (div X18 4)) 49)))
      (a!11 (not (<= (+ Z18 (div X18 4)) 50)))
      (a!12 (not (<= (+ Z18 (div X18 4)) 51)))
      (a!13 (not (<= (+ Z18 (div X18 4)) 52)))
      (a!14 (not (<= (+ Z18 (div X18 4)) 53)))
      (a!15 (not (<= (+ Z18 (div X18 4)) 54)))
      (a!16 (not (<= (+ Z18 (div X18 4)) 55)))
      (a!17 (not (<= (+ Z18 (div X18 4)) 40)))
      (a!18 (not (<= (+ Z18 (div X18 4)) 41)))
      (a!19 (not (<= (+ Z18 (div X18 4)) 42)))
      (a!20 (not (<= (+ Z18 (div X18 4)) 43)))
      (a!21 (not (<= (+ Z18 (div X18 4)) 44)))
      (a!22 (not (<= (+ Z18 (div X18 4)) 45)))
      (a!23 (not (<= (+ Z18 (div X18 4)) 46)))
      (a!24 (not (<= (+ Z18 (div X18 4)) 47)))
      (a!25 (not (<= (+ Z18 (div X18 4)) 32)))
      (a!26 (not (<= (+ Z18 (div X18 4)) 33)))
      (a!27 (not (<= (+ Z18 (div X18 4)) 34)))
      (a!28 (not (<= (+ Z18 (div X18 4)) 35)))
      (a!29 (not (<= (+ Z18 (div X18 4)) 36)))
      (a!30 (not (<= (+ Z18 (div X18 4)) 37)))
      (a!31 (not (<= (+ Z18 (div X18 4)) 38)))
      (a!32 (not (<= (+ Z18 (div X18 4)) 39)))
      (a!33 (not (<= (+ Z18 (div X18 4)) 24)))
      (a!34 (not (<= (+ Z18 (div X18 4)) 25)))
      (a!35 (not (<= (+ Z18 (div X18 4)) 26)))
      (a!36 (not (<= (+ Z18 (div X18 4)) 27)))
      (a!37 (not (<= (+ Z18 (div X18 4)) 28)))
      (a!38 (not (<= (+ Z18 (div X18 4)) 29)))
      (a!39 (not (<= (+ Z18 (div X18 4)) 30)))
      (a!40 (not (<= (+ Z18 (div X18 4)) 31)))
      (a!41 (not (<= (+ Z18 (div X18 4)) 16)))
      (a!42 (not (<= (+ Z18 (div X18 4)) 17)))
      (a!43 (not (<= (+ Z18 (div X18 4)) 18)))
      (a!44 (not (<= (+ Z18 (div X18 4)) 19)))
      (a!45 (not (<= (+ Z18 (div X18 4)) 20)))
      (a!46 (not (<= (+ Z18 (div X18 4)) 21)))
      (a!47 (not (<= (+ Z18 (div X18 4)) 22)))
      (a!48 (not (<= (+ Z18 (div X18 4)) 23)))
      (a!49 (not (<= (+ Z18 (div X18 4)) 8)))
      (a!50 (not (<= (+ Z18 (div X18 4)) 9)))
      (a!51 (not (<= (+ Z18 (div X18 4)) 10)))
      (a!52 (not (<= (+ Z18 (div X18 4)) 11)))
      (a!53 (not (<= (+ Z18 (div X18 4)) 12)))
      (a!54 (not (<= (+ Z18 (div X18 4)) 13)))
      (a!55 (not (<= (+ Z18 (div X18 4)) 14)))
      (a!56 (not (<= (+ Z18 (div X18 4)) 15)))
      (a!57 (not (<= (+ Z18 (div X18 4)) 0)))
      (a!58 (not (<= (+ Z18 (div X18 4)) 1)))
      (a!59 (not (<= (+ Z18 (div X18 4)) 3)))
      (a!60 (not (<= (+ Z18 (div X18 4)) 5)))
      (a!61 (not (<= (+ Z18 (div X18 4)) 6)))
      (a!62 (not (<= (+ Z18 (div X18 4)) 7)))
      (a!63 (not (<= (+ Z18 (div X18 4)) 4)))
      (a!64 (not (<= (+ Z18 (div X18 4)) 2)))
      (a!65 (or (not (<= Z18 0)) (<= (+ Z18 (div X18 4)) 0))))
  (and (= 1026 v_497)
       (= v_498 false)
       (ite (and (<= Z18 56) a!1) I1 (= I1 C8))
       (ite (and (<= Z18 57) a!2) (= G (div X18 4)) (= G X3))
       (ite (and (<= Z18 57) a!2) R (= R B8))
       (ite (and (<= Z18 58) a!3) (= F (div X18 4)) (= F W3))
       (ite (and (<= Z18 58) a!3) Q (= Q A8))
       (ite (and (<= Z18 59) a!4) (= E (div X18 4)) (= E V3))
       (ite (and (<= Z18 59) a!4) P (= P Z7))
       (ite (and (<= Z18 60) a!5) (= D (div X18 4)) (= D U3))
       (ite (and (<= Z18 60) a!5) O (= O Y7))
       (ite (and (<= Z18 61) a!6) (= C (div X18 4)) (= C T3))
       (ite (and (<= Z18 61) a!6) N (= N X7))
       (ite (and (<= Z18 62) a!7) (= B (div X18 4)) (= B S3))
       (ite (and (<= Z18 62) a!7) M (= M W7))
       (ite (and (<= Z18 63) a!8) (= A (div X18 4)) (= A R3))
       (ite (and (<= Z18 63) a!8) L (= L V7))
       (ite (and (<= Z18 48) a!9) (= W (div X18 4)) (= W O4))
       (ite (and (<= Z18 48) a!9) G2 (= G2 K8))
       (ite (and (<= Z18 49) a!10) (= V (div X18 4)) (= V N4))
       (ite (and (<= Z18 49) a!10) P1 (= P1 J8))
       (ite (and (<= Z18 50) a!11) (= U (div X18 4)) (= U M4))
       (ite (and (<= Z18 50) a!11) O1 (= O1 I8))
       (ite (and (<= Z18 51) a!12) (= T (div X18 4)) (= T L4))
       (ite (and (<= Z18 51) a!12) N1 (= N1 H8))
       (ite (and (<= Z18 52) a!13) (= S (div X18 4)) (= S K4))
       (ite (and (<= Z18 52) a!13) M1 (= M1 G8))
       (ite (and (<= Z18 53) a!14) (= K (div X18 4)) (= K B4))
       (ite (and (<= Z18 53) a!14) L1 (= L1 F8))
       (ite (and (<= Z18 54) a!15) (= J (div X18 4)) (= J A4))
       (ite (and (<= Z18 54) a!15) K1 (= K1 E8))
       (ite (and (<= Z18 55) a!16) (= I (div X18 4)) (= I Z3))
       (ite (and (<= Z18 55) a!16) J1 (= J1 D8))
       (ite (and (<= Z18 40) a!17) (= E1 (div X18 4)) (= E1 W4))
       (ite (and (<= Z18 40) a!17) E3 (= E3 I9))
       (ite (and (<= Z18 41) a!18) (= D1 (div X18 4)) (= D1 V4))
       (ite (and (<= Z18 41) a!18) N2 (= N2 H9))
       (ite (and (<= Z18 42) a!19) (= C1 (div X18 4)) (= C1 U4))
       (ite (and (<= Z18 42) a!19) M2 (= M2 Q8))
       (ite (and (<= Z18 43) a!20) (= B1 (div X18 4)) (= B1 T4))
       (ite (and (<= Z18 43) a!20) L2 (= L2 P8))
       (ite (and (<= Z18 44) a!21) (= A1 (div X18 4)) (= A1 S4))
       (ite (and (<= Z18 44) a!21) K2 (= K2 O8))
       (ite (and (<= Z18 45) a!22) (= Z (div X18 4)) (= Z R4))
       (ite (and (<= Z18 45) a!22) J2 (= J2 N8))
       (ite (and (<= Z18 46) a!23) (= Y (div X18 4)) (= Y Q4))
       (ite (and (<= Z18 46) a!23) I2 (= I2 M8))
       (ite (and (<= Z18 47) a!24) (= X (div X18 4)) (= X P4))
       (ite (and (<= Z18 47) a!24) H2 (= H2 L8))
       (ite (and (<= Z18 32) a!25) (= U1 (div X18 4)) (= U1 M5))
       (ite (and (<= Z18 32) a!25) C4 (= C4 Q9))
       (ite (and (<= Z18 33) a!26) (= T1 (div X18 4)) (= T1 L5))
       (ite (and (<= Z18 33) a!26) L3 (= L3 P9))
       (ite (and (<= Z18 34) a!27) (= S1 (div X18 4)) (= S1 K5))
       (ite (and (<= Z18 34) a!27) K3 (= K3 O9))
       (ite (and (<= Z18 35) a!28) (= R1 (div X18 4)) (= R1 J5))
       (ite (and (<= Z18 35) a!28) J3 (= J3 N9))
       (ite (and (<= Z18 36) a!29) (= Q1 (div X18 4)) (= Q1 I5))
       (ite (and (<= Z18 36) a!29) I3 (= I3 M9))
       (ite (and (<= Z18 37) a!30) (= H1 (div X18 4)) (= H1 Z4))
       (ite (and (<= Z18 37) a!30) H3 (= H3 L9))
       (ite (and (<= Z18 38) a!31) (= G1 (div X18 4)) (= G1 Y4))
       (ite (and (<= Z18 38) a!31) G3 (= G3 K9))
       (ite (and (<= Z18 39) a!32) (= F1 (div X18 4)) (= F1 X4))
       (ite (and (<= Z18 39) a!32) F3 (= F3 J9))
       (ite (and (<= Z18 24) a!33) (= C2 (div X18 4)) (= C2 U5))
       (ite (and (<= Z18 24) a!33) A5 (= A5 Y9))
       (ite (and (<= Z18 25) a!34) (= B2 (div X18 4)) (= B2 T5))
       (ite (and (<= Z18 25) a!34) J4 (= J4 X9))
       (ite (and (<= Z18 26) a!35) (= A2 (div X18 4)) (= A2 S5))
       (ite (and (<= Z18 26) a!35) I4 (= I4 W9))
       (ite (and (<= Z18 27) a!36) (= Z1 (div X18 4)) (= Z1 R5))
       (ite (and (<= Z18 27) a!36) H4 (= H4 V9))
       (ite (and (<= Z18 28) a!37) (= Y1 (div X18 4)) (= Y1 Q5))
       (ite (and (<= Z18 28) a!37) G4 (= G4 U9))
       (ite (and (<= Z18 29) a!38) (= X1 (div X18 4)) (= X1 P5))
       (ite (and (<= Z18 29) a!38) F4 (= F4 T9))
       (ite (and (<= Z18 30) a!39) (= W1 (div X18 4)) (= W1 O5))
       (ite (and (<= Z18 30) a!39) E4 (= E4 S9))
       (ite (and (<= Z18 31) a!40) (= V1 (div X18 4)) (= V1 N5))
       (ite (and (<= Z18 31) a!40) D4 (= D4 R9))
       (ite (and (<= Z18 16) a!41) (= S2 (div X18 4)) (= S2 K6))
       (ite (and (<= Z18 16) a!41) Y5 (= Y5 U11))
       (ite (and (<= Z18 17) a!42) (= R2 (div X18 4)) (= R2 J6))
       (ite (and (<= Z18 17) a!42) H5 (= H5 T11))
       (ite (and (<= Z18 18) a!43) (= Q2 (div X18 4)) (= Q2 I6))
       (ite (and (<= Z18 18) a!43) G5 (= G5 E10))
       (ite (and (<= Z18 19) a!44) (= P2 (div X18 4)) (= P2 H6))
       (ite (and (<= Z18 19) a!44) F5 (= F5 D10))
       (ite (and (<= Z18 20) a!45) (= O2 (div X18 4)) (= O2 G6))
       (ite (and (<= Z18 20) a!45) E5 (= E5 C10))
       (ite (and (<= Z18 21) a!46) (= F2 (div X18 4)) (= F2 X5))
       (ite (and (<= Z18 21) a!46) D5 (= D5 B10))
       (ite (and (<= Z18 22) a!47) (= E2 (div X18 4)) (= E2 W5))
       (ite (and (<= Z18 22) a!47) C5 (= C5 A10))
       (ite (and (<= Z18 23) a!48) (= D2 (div X18 4)) (= D2 V5))
       (ite (and (<= Z18 23) a!48) B5 (= B5 Z9))
       (ite (and (<= Z18 8) a!49) (= A3 (div X18 4)) (= A3 S6))
       (ite (and (<= Z18 8) a!49) W6 (= W6 C12))
       (ite (and (<= Z18 9) a!50) (= Z2 (div X18 4)) (= Z2 R6))
       (ite (and (<= Z18 9) a!50) F6 (= F6 B12))
       (ite (and (<= Z18 10) a!51) (= Y2 (div X18 4)) (= Y2 Q6))
       (ite (and (<= Z18 10) a!51) E6 (= E6 A12))
       (ite (and (<= Z18 11) a!52) (= X2 (div X18 4)) (= X2 P6))
       (ite (and (<= Z18 11) a!52) D6 (= D6 Z11))
       (ite (and (<= Z18 12) a!53) (= W2 (div X18 4)) (= W2 O6))
       (ite (and (<= Z18 12) a!53) C6 (= C6 Y11))
       (ite (and (<= Z18 13) a!54) (= V2 (div X18 4)) (= V2 N6))
       (ite (and (<= Z18 13) a!54) B6 (= B6 X11))
       (ite (and (<= Z18 14) a!55) (= U2 (div X18 4)) (= U2 M6))
       (ite (and (<= Z18 14) a!55) A6 (= A6 W11))
       (ite (and (<= Z18 15) a!56) (= T2 (div X18 4)) (= T2 L6))
       (ite (and (<= Z18 15) a!56) Z5 (= Z5 V11))
       (ite (and (<= Z18 0) a!57) (= Q3 (div X18 4)) (= Q3 I7))
       (ite (and (<= Z18 1) a!58) (= P3 (div X18 4)) (= P3 H7))
       (ite (and (<= Z18 1) a!58) D7 (= D7 J12))
       (ite (and (<= Z18 3) a!59) (= N3 (div X18 4)) (= N3 F7))
       (ite (and (<= Z18 3) a!59) B7 (= B7 H12))
       (ite (and (<= Z18 5) a!60) (= D3 (div X18 4)) (= D3 V6))
       (ite (and (<= Z18 5) a!60) Z6 (= Z6 F12))
       (ite (and (<= Z18 6) a!61) (= C3 (div X18 4)) (= C3 U6))
       (ite (and (<= Z18 6) a!61) Y6 (= Y6 E12))
       (ite (and (<= Z18 7) a!62) (= B3 (div X18 4)) (= B3 T6))
       (ite (and (<= Z18 7) a!62) X6 (= X6 D12))
       (ite (and (<= Z18 4) a!63) (= M3 (div X18 4)) (= M3 E7))
       (ite (and (<= Z18 4) a!63) A7 (= A7 G12))
       (ite (and (<= Z18 2) a!64) (= O3 (div X18 4)) (= O3 G7))
       (ite (and (<= Z18 2) a!64) C7 (= C7 I12))
       (= L14 Q8)
       (= K14 P8)
       (= J14 O8)
       (= I14 N8)
       (= H14 M8)
       (= G14 L8)
       (= P12 I8)
       (= O12 H8)
       (= N12 G8)
       (= M12 F8)
       (= L12 E8)
       (= K12 D8)
       (= Z16 U11)
       (= Y16 T11)
       (= X16 E10)
       (= W16 D10)
       (= V16 C10)
       (= U16 B10)
       (= T16 A10)
       (= S16 Z9)
       (= C15 X9)
       (= B15 W9)
       (= A15 V9)
       (= Z14 U9)
       (= Y14 T9)
       (= X14 S9)
       (= W14 R9)
       (= F14 K8)
       (= R16 Y9)
       (= V14 Q9)
       (= F17 A12)
       (= E17 Z11)
       (= D17 Y11)
       (= C17 X11)
       (= B17 W11)
       (= A17 V11)
       (= Q12 J8)
       (= M14 H9)
       (= G17 B12)
       (= N14 I9)
       (= U14 P9)
       (= T14 O9)
       (= S14 N9)
       (= R14 M9)
       (= Q14 L9)
       (= P14 K9)
       (= O14 J9)
       (= H17 C12)
       (= O17 J12)
       (= N17 I12)
       (= M17 H12)
       (= L17 G12)
       (= K17 F12)
       (= J17 E12)
       (= I17 D12)
       (= J7 Z3)
       (= Z8 J5)
       (= Y8 I5)
       (= X8 Z4)
       (= W8 Y4)
       (= V8 X4)
       (= U8 W4)
       (= T8 V4)
       (= S8 U4)
       (= G11 I7)
       (= F11 H7)
       (= E11 G7)
       (= N10 H6)
       (= M10 G6)
       (= L10 X5)
       (= K10 W5)
       (= J10 V5)
       (= I10 U5)
       (= H10 T5)
       (= G9 Q5)
       (= F9 P5)
       (= E9 O5)
       (= D9 N5)
       (= C9 M5)
       (= B9 L5)
       (= A9 K5)
       (= R8 T4)
       (= U7 S4)
       (= T7 R4)
       (= S7 Q4)
       (= R7 P4)
       (= Q7 O4)
       (= P7 N4)
       (= O7 M4)
       (= N7 L4)
       (= M7 K4)
       (= L7 B4)
       (= K7 A4)
       (= D11 F7)
       (= C11 E7)
       (= B11 V6)
       (= A11 U6)
       (= Z10 T6)
       (= Y10 S6)
       (= X10 R6)
       (= W10 Q6)
       (= V10 P6)
       (= U10 O6)
       (= T10 N6)
       (= S10 M6)
       (= R10 L6)
       (= Q10 K6)
       (= P10 J6)
       (= O10 I6)
       (= G10 S5)
       (= F10 R5)
       (= P16 N13)
       (= O16 M13)
       (= N16 L13)
       (= M16 K13)
       (= L16 J13)
       (= K16 I13)
       (= R15 R11)
       (= Q15 Q11)
       (= P15 P11)
       (= L18 J15)
       (= K18 I15)
       (= J18 H15)
       (= I18 G15)
       (= H18 F15)
       (= G18 E15)
       (= S15 S11)
       (= Q16 O13)
       (= M18 K15)
       (= Y15 W12)
       (= X15 V12)
       (= W15 U12)
       (= V15 T12)
       (= U15 S12)
       (= T15 R12)
       (= J16 H13)
       (= I16 G13)
       (= H16 F13)
       (= G16 E13)
       (= F16 D13)
       (= E16 C13)
       (= D16 B13)
       (= C16 A13)
       (= B16 Z12)
       (= A16 Y12)
       (= Z15 X12)
       (= U17 U13)
       (= T17 T13)
       (= S17 S13)
       (= R17 R13)
       (= Q17 Q13)
       (= P17 P13)
       (= Q18 O15)
       (= P18 N15)
       (= O18 M15)
       (= N18 L15)
       (= F18 D15)
       (= E18 E14)
       (= D18 D14)
       (= C18 C14)
       (= B18 B14)
       (= A18 A14)
       (= Z17 Z13)
       (= Y17 Y13)
       (= X17 X13)
       (= W17 W13)
       (= V17 V13)
       (= C19 (+ Z18 (div X18 4)))
       (<= (+ Z18 (div X18 4)) 64)
       a!65
       (ite (and (<= Z18 56) a!1) (= H (div X18 4)) (= H Y3))
       (= 1027 v_499)
       (= v_500 false)))
      )
      (transition-8 v_499
              A19
              C19
              Y18
              X18
              Z18
              V18
              U18
              T18
              S18
              R18
              O15
              N15
              M15
              L15
              K15
              J15
              I15
              H15
              G15
              F15
              E15
              D15
              E14
              D14
              C14
              B14
              A14
              Z13
              Y13
              X13
              W13
              V13
              U13
              T13
              S13
              R13
              Q13
              P13
              O13
              N13
              M13
              L13
              K13
              J13
              I13
              H13
              G13
              F13
              E13
              D13
              C13
              B13
              A13
              Z12
              Y12
              X12
              W12
              V12
              U12
              T12
              S12
              R12
              S11
              R11
              Q11
              P11
              O11
              N11
              M11
              L11
              K11
              J11
              I11
              H11
              v_500
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (v_11 Int) (v_12 Bool) (v_13 Int) (v_14 Int) (v_15 Bool) ) 
    (=>
      (and
        (transition-0 v_11 K I H G F E D C B A v_12)
        (and (= 1027 v_11) (= v_12 false) (= 1028 v_13) (= v_14 F) (= v_15 false))
      )
      (transition-0 v_13 J I H G F E D C v_14 A v_15)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (v_34 Int) (v_35 Bool) (v_36 Int) (v_37 Int) (v_38 Bool) ) 
    (=>
      (and
        (transition-1 v_34
              H1
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
              K
              J
              I
              v_35
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 1027 v_34) (= v_35 false) (= 1028 v_36) (= v_37 C1) (= v_38 false))
      )
      (transition-1 v_36
              G1
              F1
              E1
              D1
              C1
              B1
              A1
              Z
              v_37
              X
              W
              V
              U
              T
              S
              K
              J
              I
              v_38
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (v_58 Int) (v_59 Bool) (v_60 Int) (v_61 Int) (v_62 Bool) ) 
    (=>
      (and
        (transition-2 v_58
              F2
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
              v_59
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 1027 v_58) (= v_59 false) (= 1028 v_60) (= v_61 A2) (= v_62 false))
      )
      (transition-2 v_60
              E2
              D2
              C2
              B2
              A2
              Z1
              Y1
              X1
              v_61
              V1
              U1
              T1
              S1
              R1
              Q1
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
              v_62
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (v_82 Int) (v_83 Bool) (v_84 Int) (v_85 Int) (v_86 Bool) ) 
    (=>
      (and
        (transition-3 v_82
              D3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_83
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1027 v_82) (= v_83 false) (= 1028 v_84) (= v_85 Y2) (= v_86 false))
      )
      (transition-3 v_84
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              v_85
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_86
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (v_106 Int) (v_107 Bool) (v_108 Int) (v_109 Int) (v_110 Bool) ) 
    (=>
      (and
        (transition-4 v_106
              B4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_107
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 1027 v_106) (= v_107 false) (= 1028 v_108) (= v_109 W3) (= v_110 false))
      )
      (transition-4 v_108
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              v_109
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_110
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (v_130 Int) (v_131 Bool) (v_132 Int) (v_133 Int) (v_134 Bool) ) 
    (=>
      (and
        (transition-5 v_130
              Z4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_131
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1027 v_130) (= v_131 false) (= 1028 v_132) (= v_133 U4) (= v_134 false))
      )
      (transition-5 v_132
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              v_133
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_134
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (v_154 Int) (v_155 Bool) (v_156 Int) (v_157 Int) (v_158 Bool) ) 
    (=>
      (and
        (transition-6 v_154
              X5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_155
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1027 v_154) (= v_155 false) (= 1028 v_156) (= v_157 S5) (= v_158 false))
      )
      (transition-6 v_156
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              v_157
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_158
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (v_178 Int) (v_179 Bool) (v_180 Int) (v_181 Int) (v_182 Bool) ) 
    (=>
      (and
        (transition-7 v_178
              V6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_179
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1027 v_178) (= v_179 false) (= 1028 v_180) (= v_181 Q6) (= v_182 false))
      )
      (transition-7 v_180
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              v_181
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_182
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (v_202 Int) (v_203 Bool) (v_204 Int) (v_205 Int) (v_206 Bool) ) 
    (=>
      (and
        (transition-8 v_202
              T7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_203
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1027 v_202) (= v_203 false) (= 1028 v_204) (= v_205 O7) (= v_206 false))
      )
      (transition-8 v_204
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              v_205
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_206
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (v_11 Int) (v_12 Bool) (v_13 Int) (v_14 Int) (v_15 Bool) ) 
    (=>
      (and
        (transition-0 v_11 K I H G F E D C B A v_12)
        (and (= 1028 v_11) (= v_12 false) (= 1029 v_13) (= v_14 B) (= v_15 false))
      )
      (transition-0 v_13 J I H G F E D C B v_14 v_15)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (v_34 Int) (v_35 Bool) (v_36 Int) (v_37 Int) (v_38 Bool) ) 
    (=>
      (and
        (transition-1 v_34
              H1
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
              K
              J
              I
              v_35
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 1028 v_34) (= v_35 false) (= 1029 v_36) (= v_37 Y) (= v_38 false))
      )
      (transition-1 v_36
              G1
              F1
              E1
              D1
              C1
              B1
              A1
              Z
              Y
              v_37
              W
              V
              U
              T
              S
              K
              J
              I
              v_38
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (v_58 Int) (v_59 Bool) (v_60 Int) (v_61 Int) (v_62 Bool) ) 
    (=>
      (and
        (transition-2 v_58
              F2
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
              v_59
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 1028 v_58) (= v_59 false) (= 1029 v_60) (= v_61 W1) (= v_62 false))
      )
      (transition-2 v_60
              E2
              D2
              C2
              B2
              A2
              Z1
              Y1
              X1
              W1
              v_61
              U1
              T1
              S1
              R1
              Q1
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
              v_62
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (v_82 Int) (v_83 Bool) (v_84 Int) (v_85 Int) (v_86 Bool) ) 
    (=>
      (and
        (transition-3 v_82
              D3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_83
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1028 v_82) (= v_83 false) (= 1029 v_84) (= v_85 U2) (= v_86 false))
      )
      (transition-3 v_84
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              v_85
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_86
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (v_106 Int) (v_107 Bool) (v_108 Int) (v_109 Int) (v_110 Bool) ) 
    (=>
      (and
        (transition-4 v_106
              B4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_107
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 1028 v_106) (= v_107 false) (= 1029 v_108) (= v_109 S3) (= v_110 false))
      )
      (transition-4 v_108
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              v_109
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_110
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (v_130 Int) (v_131 Bool) (v_132 Int) (v_133 Int) (v_134 Bool) ) 
    (=>
      (and
        (transition-5 v_130
              Z4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_131
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1028 v_130) (= v_131 false) (= 1029 v_132) (= v_133 Q4) (= v_134 false))
      )
      (transition-5 v_132
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              v_133
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_134
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (v_154 Int) (v_155 Bool) (v_156 Int) (v_157 Int) (v_158 Bool) ) 
    (=>
      (and
        (transition-6 v_154
              X5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_155
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1028 v_154) (= v_155 false) (= 1029 v_156) (= v_157 O5) (= v_158 false))
      )
      (transition-6 v_156
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              v_157
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_158
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (v_178 Int) (v_179 Bool) (v_180 Int) (v_181 Int) (v_182 Bool) ) 
    (=>
      (and
        (transition-7 v_178
              V6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_179
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1028 v_178) (= v_179 false) (= 1029 v_180) (= v_181 M6) (= v_182 false))
      )
      (transition-7 v_180
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              v_181
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_182
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (v_202 Int) (v_203 Bool) (v_204 Int) (v_205 Int) (v_206 Bool) ) 
    (=>
      (and
        (transition-8 v_202
              T7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_203
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1028 v_202) (= v_203 false) (= 1029 v_204) (= v_205 K7) (= v_206 false))
      )
      (transition-8 v_204
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              v_205
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_206
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (v_11 Int) (v_12 Bool) (v_13 Int) (v_14 Bool) ) 
    (=>
      (and
        (transition-0 v_11 K I H G F E D C B A v_12)
        (and (= 1029 v_11) (= v_12 false) (= 1030 v_13) (= v_14 false))
      )
      (transition-0 v_13 J I H G F E D C K A v_14)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (v_34 Int) (v_35 Bool) (v_36 Int) (v_37 Bool) ) 
    (=>
      (and
        (transition-1 v_34
              H1
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
              K
              J
              I
              v_35
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 1029 v_34) (= v_35 false) (= 1030 v_36) (= v_37 false))
      )
      (transition-1 v_36
              G1
              F1
              E1
              D1
              C1
              B1
              A1
              Z
              H1
              X
              W
              V
              U
              T
              S
              K
              J
              I
              v_37
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (v_58 Int) (v_59 Bool) (v_60 Int) (v_61 Bool) ) 
    (=>
      (and
        (transition-2 v_58
              F2
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
              v_59
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 1029 v_58) (= v_59 false) (= 1030 v_60) (= v_61 false))
      )
      (transition-2 v_60
              E2
              D2
              C2
              B2
              A2
              Z1
              Y1
              X1
              F2
              V1
              U1
              T1
              S1
              R1
              Q1
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
              v_61
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (v_82 Int) (v_83 Bool) (v_84 Int) (v_85 Bool) ) 
    (=>
      (and
        (transition-3 v_82
              D3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_83
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1029 v_82) (= v_83 false) (= 1030 v_84) (= v_85 false))
      )
      (transition-3 v_84
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              D3
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_85
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (v_106 Int) (v_107 Bool) (v_108 Int) (v_109 Bool) ) 
    (=>
      (and
        (transition-4 v_106
              B4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_107
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 1029 v_106) (= v_107 false) (= 1030 v_108) (= v_109 false))
      )
      (transition-4 v_108
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              B4
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_109
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (v_130 Int) (v_131 Bool) (v_132 Int) (v_133 Bool) ) 
    (=>
      (and
        (transition-5 v_130
              Z4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_131
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1029 v_130) (= v_131 false) (= 1030 v_132) (= v_133 false))
      )
      (transition-5 v_132
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Z4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_133
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (v_154 Int) (v_155 Bool) (v_156 Int) (v_157 Bool) ) 
    (=>
      (and
        (transition-6 v_154
              X5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_155
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1029 v_154) (= v_155 false) (= 1030 v_156) (= v_157 false))
      )
      (transition-6 v_156
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              X5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_157
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (v_178 Int) (v_179 Bool) (v_180 Int) (v_181 Bool) ) 
    (=>
      (and
        (transition-7 v_178
              V6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_179
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1029 v_178) (= v_179 false) (= 1030 v_180) (= v_181 false))
      )
      (transition-7 v_180
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              V6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_181
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (v_202 Int) (v_203 Bool) (v_204 Int) (v_205 Bool) ) 
    (=>
      (and
        (transition-8 v_202
              T7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_203
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1029 v_202) (= v_203 false) (= 1030 v_204) (= v_205 false))
      )
      (transition-8 v_204
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              T7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_205
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (v_11 Int) (v_12 Bool) (v_13 Int) (v_14 Bool) ) 
    (=>
      (and
        (transition-0 v_11 K I H G F E D C B A v_12)
        (and (= 1030 v_11) (= v_12 false) (= 1031 v_13) (= v_14 false))
      )
      (transition-0 v_13 J I K G F E D C B A v_14)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (v_34 Int) (v_35 Bool) (v_36 Int) (v_37 Bool) ) 
    (=>
      (and
        (transition-1 v_34
              H1
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
              K
              J
              I
              v_35
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 1030 v_34) (= v_35 false) (= 1031 v_36) (= v_37 false))
      )
      (transition-1 v_36
              G1
              F1
              H1
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
              K
              J
              I
              v_37
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (v_58 Int) (v_59 Bool) (v_60 Int) (v_61 Bool) ) 
    (=>
      (and
        (transition-2 v_58
              F2
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
              v_59
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 1030 v_58) (= v_59 false) (= 1031 v_60) (= v_61 false))
      )
      (transition-2 v_60
              E2
              D2
              F2
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
              v_61
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (v_82 Int) (v_83 Bool) (v_84 Int) (v_85 Bool) ) 
    (=>
      (and
        (transition-3 v_82
              D3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_83
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1030 v_82) (= v_83 false) (= 1031 v_84) (= v_85 false))
      )
      (transition-3 v_84
              C3
              B3
              D3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_85
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (v_106 Int) (v_107 Bool) (v_108 Int) (v_109 Bool) ) 
    (=>
      (and
        (transition-4 v_106
              B4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_107
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 1030 v_106) (= v_107 false) (= 1031 v_108) (= v_109 false))
      )
      (transition-4 v_108
              A4
              Z3
              B4
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_109
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (v_130 Int) (v_131 Bool) (v_132 Int) (v_133 Bool) ) 
    (=>
      (and
        (transition-5 v_130
              Z4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_131
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1030 v_130) (= v_131 false) (= 1031 v_132) (= v_133 false))
      )
      (transition-5 v_132
              Y4
              X4
              Z4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_133
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (v_154 Int) (v_155 Bool) (v_156 Int) (v_157 Bool) ) 
    (=>
      (and
        (transition-6 v_154
              X5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_155
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1030 v_154) (= v_155 false) (= 1031 v_156) (= v_157 false))
      )
      (transition-6 v_156
              W5
              V5
              X5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_157
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (v_178 Int) (v_179 Bool) (v_180 Int) (v_181 Bool) ) 
    (=>
      (and
        (transition-7 v_178
              V6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_179
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1030 v_178) (= v_179 false) (= 1031 v_180) (= v_181 false))
      )
      (transition-7 v_180
              U6
              T6
              V6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_181
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (v_202 Int) (v_203 Bool) (v_204 Int) (v_205 Bool) ) 
    (=>
      (and
        (transition-8 v_202
              T7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_203
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1030 v_202) (= v_203 false) (= 1031 v_204) (= v_205 false))
      )
      (transition-8 v_204
              S7
              R7
              T7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_205
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (v_11 Int) (v_12 Bool) (v_13 Int) (v_14 Int) (v_15 Bool) ) 
    (=>
      (and
        (transition-0 v_11 K I H G F E D C B A v_12)
        (and (= 1031 v_11) (= v_12 false) (= 1032 v_13) (= v_14 H) (= v_15 false))
      )
      (transition-0 v_13 J I H G F v_14 D C B A v_15)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (v_34 Int) (v_35 Bool) (v_36 Int) (v_37 Int) (v_38 Bool) ) 
    (=>
      (and
        (transition-1 v_34
              H1
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
              K
              J
              I
              v_35
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 1031 v_34) (= v_35 false) (= 1032 v_36) (= v_37 E1) (= v_38 false))
      )
      (transition-1 v_36
              G1
              F1
              E1
              D1
              C1
              v_37
              A1
              Z
              Y
              X
              W
              V
              U
              T
              S
              K
              J
              I
              v_38
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (v_58 Int) (v_59 Bool) (v_60 Int) (v_61 Int) (v_62 Bool) ) 
    (=>
      (and
        (transition-2 v_58
              F2
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
              v_59
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 1031 v_58) (= v_59 false) (= 1032 v_60) (= v_61 C2) (= v_62 false))
      )
      (transition-2 v_60
              E2
              D2
              C2
              B2
              A2
              v_61
              Y1
              X1
              W1
              V1
              U1
              T1
              S1
              R1
              Q1
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
              v_62
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (v_82 Int) (v_83 Bool) (v_84 Int) (v_85 Int) (v_86 Bool) ) 
    (=>
      (and
        (transition-3 v_82
              D3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_83
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1031 v_82) (= v_83 false) (= 1032 v_84) (= v_85 A3) (= v_86 false))
      )
      (transition-3 v_84
              C3
              B3
              A3
              Z2
              Y2
              v_85
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_86
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (v_106 Int) (v_107 Bool) (v_108 Int) (v_109 Int) (v_110 Bool) ) 
    (=>
      (and
        (transition-4 v_106
              B4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_107
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 1031 v_106) (= v_107 false) (= 1032 v_108) (= v_109 Y3) (= v_110 false))
      )
      (transition-4 v_108
              A4
              Z3
              Y3
              X3
              W3
              v_109
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_110
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (v_130 Int) (v_131 Bool) (v_132 Int) (v_133 Int) (v_134 Bool) ) 
    (=>
      (and
        (transition-5 v_130
              Z4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_131
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1031 v_130) (= v_131 false) (= 1032 v_132) (= v_133 W4) (= v_134 false))
      )
      (transition-5 v_132
              Y4
              X4
              W4
              V4
              U4
              v_133
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_134
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (v_154 Int) (v_155 Bool) (v_156 Int) (v_157 Int) (v_158 Bool) ) 
    (=>
      (and
        (transition-6 v_154
              X5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_155
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1031 v_154) (= v_155 false) (= 1032 v_156) (= v_157 U5) (= v_158 false))
      )
      (transition-6 v_156
              W5
              V5
              U5
              T5
              S5
              v_157
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_158
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (v_178 Int) (v_179 Bool) (v_180 Int) (v_181 Int) (v_182 Bool) ) 
    (=>
      (and
        (transition-7 v_178
              V6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_179
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1031 v_178) (= v_179 false) (= 1032 v_180) (= v_181 S6) (= v_182 false))
      )
      (transition-7 v_180
              U6
              T6
              S6
              R6
              Q6
              v_181
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_182
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (v_202 Int) (v_203 Bool) (v_204 Int) (v_205 Int) (v_206 Bool) ) 
    (=>
      (and
        (transition-8 v_202
              T7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_203
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1031 v_202) (= v_203 false) (= 1032 v_204) (= v_205 Q7) (= v_206 false))
      )
      (transition-8 v_204
              S7
              R7
              Q7
              P7
              O7
              v_205
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_206
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (v_11 Int) (v_12 Bool) (v_13 Int) (v_14 Bool) ) 
    (=>
      (and
        (transition-0 v_11 K I H G F E D C B A v_12)
        (and (= 1032 v_11) (= v_12 false) (= 3 v_13) (= v_14 false))
      )
      (transition-0 v_13 J I K G F E D C B A v_14)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (v_34 Int) (v_35 Bool) (v_36 Int) (v_37 Bool) ) 
    (=>
      (and
        (transition-1 v_34
              H1
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
              K
              J
              I
              v_35
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 1032 v_34) (= v_35 false) (= 3 v_36) (= v_37 false))
      )
      (transition-1 v_36
              G1
              F1
              H1
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
              K
              J
              I
              v_37
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (v_58 Int) (v_59 Bool) (v_60 Int) (v_61 Bool) ) 
    (=>
      (and
        (transition-2 v_58
              F2
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
              v_59
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 1032 v_58) (= v_59 false) (= 3 v_60) (= v_61 false))
      )
      (transition-2 v_60
              E2
              D2
              F2
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
              v_61
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (v_82 Int) (v_83 Bool) (v_84 Int) (v_85 Bool) ) 
    (=>
      (and
        (transition-3 v_82
              D3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_83
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1032 v_82) (= v_83 false) (= 3 v_84) (= v_85 false))
      )
      (transition-3 v_84
              C3
              B3
              D3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_85
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (v_106 Int) (v_107 Bool) (v_108 Int) (v_109 Bool) ) 
    (=>
      (and
        (transition-4 v_106
              B4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_107
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 1032 v_106) (= v_107 false) (= 3 v_108) (= v_109 false))
      )
      (transition-4 v_108
              A4
              Z3
              B4
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_109
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (v_130 Int) (v_131 Bool) (v_132 Int) (v_133 Bool) ) 
    (=>
      (and
        (transition-5 v_130
              Z4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_131
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1032 v_130) (= v_131 false) (= 3 v_132) (= v_133 false))
      )
      (transition-5 v_132
              Y4
              X4
              Z4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_133
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (v_154 Int) (v_155 Bool) (v_156 Int) (v_157 Bool) ) 
    (=>
      (and
        (transition-6 v_154
              X5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_155
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1032 v_154) (= v_155 false) (= 3 v_156) (= v_157 false))
      )
      (transition-6 v_156
              W5
              V5
              X5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_157
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (v_178 Int) (v_179 Bool) (v_180 Int) (v_181 Bool) ) 
    (=>
      (and
        (transition-7 v_178
              V6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_179
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1032 v_178) (= v_179 false) (= 3 v_180) (= v_181 false))
      )
      (transition-7 v_180
              U6
              T6
              V6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_181
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (v_202 Int) (v_203 Bool) (v_204 Int) (v_205 Bool) ) 
    (=>
      (and
        (transition-8 v_202
              T7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_203
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1032 v_202) (= v_203 false) (= 3 v_204) (= v_205 false))
      )
      (transition-8 v_204
              S7
              R7
              T7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_205
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (v_10 Int) (v_11 Bool) (v_12 Int) (v_13 Bool) ) 
    (=>
      (and
        (transition-0 v_10 J I H G F E D C B A v_11)
        (and (= 1 v_10) (= v_11 false) (= 1 v_12) (= v_13 false))
      )
      (transition-0 v_12 J I H G F E D C B A v_13)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (v_33 Int) (v_34 Bool) (v_35 Int) (v_36 Bool) ) 
    (=>
      (and
        (transition-1 v_33
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
              K
              J
              I
              v_34
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 1 v_33) (= v_34 false) (= 1 v_35) (= v_36 false))
      )
      (transition-1 v_35
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
              K
              J
              I
              v_36
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (v_57 Int) (v_58 Bool) (v_59 Int) (v_60 Bool) ) 
    (=>
      (and
        (transition-2 v_57
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
              v_58
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 1 v_57) (= v_58 false) (= 1 v_59) (= v_60 false))
      )
      (transition-2 v_59
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
              v_60
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (v_81 Int) (v_82 Bool) (v_83 Int) (v_84 Bool) ) 
    (=>
      (and
        (transition-3 v_81
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_82
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1 v_81) (= v_82 false) (= 1 v_83) (= v_84 false))
      )
      (transition-3 v_83
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_84
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (v_105 Int) (v_106 Bool) (v_107 Int) (v_108 Bool) ) 
    (=>
      (and
        (transition-4 v_105
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_106
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 1 v_105) (= v_106 false) (= 1 v_107) (= v_108 false))
      )
      (transition-4 v_107
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_108
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (v_129 Int) (v_130 Bool) (v_131 Int) (v_132 Bool) ) 
    (=>
      (and
        (transition-5 v_129
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_130
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1 v_129) (= v_130 false) (= 1 v_131) (= v_132 false))
      )
      (transition-5 v_131
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_132
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (v_153 Int) (v_154 Bool) (v_155 Int) (v_156 Bool) ) 
    (=>
      (and
        (transition-6 v_153
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_154
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1 v_153) (= v_154 false) (= 1 v_155) (= v_156 false))
      )
      (transition-6 v_155
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_156
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (v_177 Int) (v_178 Bool) (v_179 Int) (v_180 Bool) ) 
    (=>
      (and
        (transition-7 v_177
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_178
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1 v_177) (= v_178 false) (= 1 v_179) (= v_180 false))
      )
      (transition-7 v_179
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_180
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (v_201 Int) (v_202 Bool) (v_203 Int) (v_204 Bool) ) 
    (=>
      (and
        (transition-8 v_201
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_202
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1 v_201) (= v_202 false) (= 1 v_203) (= v_204 false))
      )
      (transition-8 v_203
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_204
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (v_10 Int) (v_11 Bool) (v_12 Int) (v_13 Bool) ) 
    (=>
      (and
        (transition-0 v_10 J I H G F E D C B A v_11)
        (and (= 3 v_10) (= v_11 false) (= 0 E) (= 1 v_12) (= v_13 false))
      )
      (transition-0 v_12 J I H G F E D C B A v_13)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (v_33 Int) (v_34 Bool) (v_35 Int) (v_36 Bool) ) 
    (=>
      (and
        (transition-1 v_33
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
              K
              J
              I
              v_34
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 3 v_33) (= v_34 false) (= 0 B1) (= 1 v_35) (= v_36 false))
      )
      (transition-1 v_35
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
              K
              J
              I
              v_36
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (v_57 Int) (v_58 Bool) (v_59 Int) (v_60 Bool) ) 
    (=>
      (and
        (transition-2 v_57
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
              v_58
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 3 v_57) (= v_58 false) (= 0 Z1) (= 1 v_59) (= v_60 false))
      )
      (transition-2 v_59
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
              v_60
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (v_81 Int) (v_82 Bool) (v_83 Int) (v_84 Bool) ) 
    (=>
      (and
        (transition-3 v_81
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_82
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 3 v_81) (= v_82 false) (= 0 X2) (= 1 v_83) (= v_84 false))
      )
      (transition-3 v_83
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_84
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (v_105 Int) (v_106 Bool) (v_107 Int) (v_108 Bool) ) 
    (=>
      (and
        (transition-4 v_105
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_106
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 3 v_105) (= v_106 false) (= 0 V3) (= 1 v_107) (= v_108 false))
      )
      (transition-4 v_107
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_108
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (v_129 Int) (v_130 Bool) (v_131 Int) (v_132 Bool) ) 
    (=>
      (and
        (transition-5 v_129
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_130
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 3 v_129) (= v_130 false) (= 0 T4) (= 1 v_131) (= v_132 false))
      )
      (transition-5 v_131
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_132
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (v_153 Int) (v_154 Bool) (v_155 Int) (v_156 Bool) ) 
    (=>
      (and
        (transition-6 v_153
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_154
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 3 v_153) (= v_154 false) (= 0 R5) (= 1 v_155) (= v_156 false))
      )
      (transition-6 v_155
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_156
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (v_177 Int) (v_178 Bool) (v_179 Int) (v_180 Bool) ) 
    (=>
      (and
        (transition-7 v_177
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_178
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 3 v_177) (= v_178 false) (= 0 P6) (= 1 v_179) (= v_180 false))
      )
      (transition-7 v_179
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_180
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (v_201 Int) (v_202 Bool) (v_203 Int) (v_204 Bool) ) 
    (=>
      (and
        (transition-8 v_201
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_202
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 3 v_201) (= v_202 false) (= 0 N7) (= 1 v_203) (= v_204 false))
      )
      (transition-8 v_203
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_204
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (v_9 Int) (v_10 Int) (v_11 Bool) ) 
    (=>
      (and
        (and true (= 4 v_9) (= 1 v_10) (= v_11 false))
      )
      (transition-0 v_9 I v_10 H G F E D C B A v_11)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (v_25 Int) (v_26 Int) (v_27 Bool) (v_28 Bool) (v_29 Bool) (v_30 Bool) (v_31 Bool) (v_32 Bool) (v_33 Bool) (v_34 Bool) ) 
    (=>
      (and
        (and (= G (- 1))
     (= F (- 1))
     (= E (- 1))
     (= D (- 1))
     (= C (- 1))
     (= B (- 1))
     (= A (- 1))
     (= H (- 1))
     (= 4 v_25)
     (= 1 v_26)
     (= v_27 false)
     (= v_28 false)
     (= v_29 false)
     (= v_30 false)
     (= v_31 false)
     (= v_32 false)
     (= v_33 false)
     (= v_34 false))
      )
      (transition-1 v_25
              Y
              v_26
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
              v_27
              v_28
              v_29
              v_30
              v_31
              v_32
              v_33
              v_34
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (v_41 Int) (v_42 Int) (v_43 Bool) (v_44 Bool) (v_45 Bool) (v_46 Bool) (v_47 Bool) (v_48 Bool) (v_49 Bool) (v_50 Bool) (v_51 Bool) (v_52 Bool) (v_53 Bool) (v_54 Bool) (v_55 Bool) (v_56 Bool) (v_57 Bool) (v_58 Bool) ) 
    (=>
      (and
        (and (= G (- 1))
     (= F (- 1))
     (= E (- 1))
     (= D (- 1))
     (= C (- 1))
     (= B (- 1))
     (= P (- 1))
     (= O (- 1))
     (= N (- 1))
     (= M (- 1))
     (= L (- 1))
     (= K (- 1))
     (= J (- 1))
     (= I (- 1))
     (= H (- 1))
     (= A (- 1))
     (= 4 v_41)
     (= 1 v_42)
     (= v_43 false)
     (= v_44 false)
     (= v_45 false)
     (= v_46 false)
     (= v_47 false)
     (= v_48 false)
     (= v_49 false)
     (= v_50 false)
     (= v_51 false)
     (= v_52 false)
     (= v_53 false)
     (= v_54 false)
     (= v_55 false)
     (= v_56 false)
     (= v_57 false)
     (= v_58 false))
      )
      (transition-2 v_41
              O1
              v_42
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
              v_43
              v_44
              v_45
              v_46
              v_47
              v_48
              v_49
              v_50
              v_51
              v_52
              v_53
              v_54
              v_55
              v_56
              v_57
              v_58
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (v_57 Int) (v_58 Int) (v_59 Bool) (v_60 Bool) (v_61 Bool) (v_62 Bool) (v_63 Bool) (v_64 Bool) (v_65 Bool) (v_66 Bool) (v_67 Bool) (v_68 Bool) (v_69 Bool) (v_70 Bool) (v_71 Bool) (v_72 Bool) (v_73 Bool) (v_74 Bool) (v_75 Bool) (v_76 Bool) (v_77 Bool) (v_78 Bool) (v_79 Bool) (v_80 Bool) (v_81 Bool) (v_82 Bool) ) 
    (=>
      (and
        (and (= O (- 1))
     (= N (- 1))
     (= M (- 1))
     (= L (- 1))
     (= K (- 1))
     (= Q (- 1))
     (= W (- 1))
     (= V (- 1))
     (= U (- 1))
     (= T (- 1))
     (= S (- 1))
     (= R (- 1))
     (= J (- 1))
     (= I (- 1))
     (= H (- 1))
     (= G (- 1))
     (= F (- 1))
     (= E (- 1))
     (= D (- 1))
     (= C (- 1))
     (= B (- 1))
     (= A (- 1))
     (= X (- 1))
     (= P (- 1))
     (= 4 v_57)
     (= 1 v_58)
     (= v_59 false)
     (= v_60 false)
     (= v_61 false)
     (= v_62 false)
     (= v_63 false)
     (= v_64 false)
     (= v_65 false)
     (= v_66 false)
     (= v_67 false)
     (= v_68 false)
     (= v_69 false)
     (= v_70 false)
     (= v_71 false)
     (= v_72 false)
     (= v_73 false)
     (= v_74 false)
     (= v_75 false)
     (= v_76 false)
     (= v_77 false)
     (= v_78 false)
     (= v_79 false)
     (= v_80 false)
     (= v_81 false)
     (= v_82 false))
      )
      (transition-3 v_57
              E2
              v_58
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
              v_59
              v_60
              v_61
              v_62
              v_63
              v_64
              v_65
              v_66
              v_67
              v_68
              v_69
              v_70
              v_71
              v_72
              v_73
              v_74
              v_75
              v_76
              v_77
              v_78
              v_79
              v_80
              v_81
              v_82
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (v_73 Int) (v_74 Int) (v_75 Bool) (v_76 Bool) (v_77 Bool) (v_78 Bool) (v_79 Bool) (v_80 Bool) (v_81 Bool) (v_82 Bool) (v_83 Bool) (v_84 Bool) (v_85 Bool) (v_86 Bool) (v_87 Bool) (v_88 Bool) (v_89 Bool) (v_90 Bool) (v_91 Bool) (v_92 Bool) (v_93 Bool) (v_94 Bool) (v_95 Bool) (v_96 Bool) (v_97 Bool) (v_98 Bool) (v_99 Bool) (v_100 Bool) (v_101 Bool) (v_102 Bool) (v_103 Bool) (v_104 Bool) (v_105 Bool) (v_106 Bool) ) 
    (=>
      (and
        (and (= G (- 1))
     (= F (- 1))
     (= E (- 1))
     (= D (- 1))
     (= C (- 1))
     (= F1 (- 1))
     (= E1 (- 1))
     (= D1 (- 1))
     (= C1 (- 1))
     (= B1 (- 1))
     (= A1 (- 1))
     (= I (- 1))
     (= O (- 1))
     (= N (- 1))
     (= M (- 1))
     (= L (- 1))
     (= K (- 1))
     (= J (- 1))
     (= B (- 1))
     (= A (- 1))
     (= Z (- 1))
     (= Y (- 1))
     (= X (- 1))
     (= W (- 1))
     (= V (- 1))
     (= U (- 1))
     (= T (- 1))
     (= S (- 1))
     (= R (- 1))
     (= Q (- 1))
     (= P (- 1))
     (= H (- 1))
     (= 4 v_73)
     (= 1 v_74)
     (= v_75 false)
     (= v_76 false)
     (= v_77 false)
     (= v_78 false)
     (= v_79 false)
     (= v_80 false)
     (= v_81 false)
     (= v_82 false)
     (= v_83 false)
     (= v_84 false)
     (= v_85 false)
     (= v_86 false)
     (= v_87 false)
     (= v_88 false)
     (= v_89 false)
     (= v_90 false)
     (= v_91 false)
     (= v_92 false)
     (= v_93 false)
     (= v_94 false)
     (= v_95 false)
     (= v_96 false)
     (= v_97 false)
     (= v_98 false)
     (= v_99 false)
     (= v_100 false)
     (= v_101 false)
     (= v_102 false)
     (= v_103 false)
     (= v_104 false)
     (= v_105 false)
     (= v_106 false))
      )
      (transition-4 v_73
              U2
              v_74
              T2
              S2
              R2
              Q2
              P2
              O2
              N2
              M2
              L2
              K2
              J2
              I2
              H2
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
              v_75
              v_76
              v_77
              v_78
              v_79
              v_80
              v_81
              v_82
              v_83
              v_84
              v_85
              v_86
              v_87
              v_88
              v_89
              v_90
              v_91
              v_92
              v_93
              v_94
              v_95
              v_96
              v_97
              v_98
              v_99
              v_100
              v_101
              v_102
              v_103
              v_104
              v_105
              v_106
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Int) (F3 Int) (G3 Int) (H3 Int) (I3 Int) (J3 Int) (K3 Int) (v_89 Int) (v_90 Int) (v_91 Bool) (v_92 Bool) (v_93 Bool) (v_94 Bool) (v_95 Bool) (v_96 Bool) (v_97 Bool) (v_98 Bool) (v_99 Bool) (v_100 Bool) (v_101 Bool) (v_102 Bool) (v_103 Bool) (v_104 Bool) (v_105 Bool) (v_106 Bool) (v_107 Bool) (v_108 Bool) (v_109 Bool) (v_110 Bool) (v_111 Bool) (v_112 Bool) (v_113 Bool) (v_114 Bool) (v_115 Bool) (v_116 Bool) (v_117 Bool) (v_118 Bool) (v_119 Bool) (v_120 Bool) (v_121 Bool) (v_122 Bool) (v_123 Bool) (v_124 Bool) (v_125 Bool) (v_126 Bool) (v_127 Bool) (v_128 Bool) (v_129 Bool) (v_130 Bool) ) 
    (=>
      (and
        (and (= W (- 1))
     (= V (- 1))
     (= U (- 1))
     (= T (- 1))
     (= S (- 1))
     (= A (- 1))
     (= Y (- 1))
     (= G (- 1))
     (= F (- 1))
     (= E (- 1))
     (= D (- 1))
     (= C (- 1))
     (= B (- 1))
     (= E1 (- 1))
     (= D1 (- 1))
     (= C1 (- 1))
     (= B1 (- 1))
     (= A1 (- 1))
     (= Z (- 1))
     (= R (- 1))
     (= Q (- 1))
     (= P (- 1))
     (= O (- 1))
     (= N (- 1))
     (= M (- 1))
     (= L (- 1))
     (= K (- 1))
     (= J (- 1))
     (= I (- 1))
     (= H (- 1))
     (= N1 (- 1))
     (= M1 (- 1))
     (= L1 (- 1))
     (= K1 (- 1))
     (= J1 (- 1))
     (= I1 (- 1))
     (= H1 (- 1))
     (= G1 (- 1))
     (= F1 (- 1))
     (= X (- 1))
     (= 4 v_89)
     (= 1 v_90)
     (= v_91 false)
     (= v_92 false)
     (= v_93 false)
     (= v_94 false)
     (= v_95 false)
     (= v_96 false)
     (= v_97 false)
     (= v_98 false)
     (= v_99 false)
     (= v_100 false)
     (= v_101 false)
     (= v_102 false)
     (= v_103 false)
     (= v_104 false)
     (= v_105 false)
     (= v_106 false)
     (= v_107 false)
     (= v_108 false)
     (= v_109 false)
     (= v_110 false)
     (= v_111 false)
     (= v_112 false)
     (= v_113 false)
     (= v_114 false)
     (= v_115 false)
     (= v_116 false)
     (= v_117 false)
     (= v_118 false)
     (= v_119 false)
     (= v_120 false)
     (= v_121 false)
     (= v_122 false)
     (= v_123 false)
     (= v_124 false)
     (= v_125 false)
     (= v_126 false)
     (= v_127 false)
     (= v_128 false)
     (= v_129 false)
     (= v_130 false))
      )
      (transition-5 v_89
              K3
              v_90
              J3
              I3
              H3
              G3
              F3
              E3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              N2
              M2
              L2
              K2
              J2
              I2
              H2
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
              v_91
              v_92
              v_93
              v_94
              v_95
              v_96
              v_97
              v_98
              v_99
              v_100
              v_101
              v_102
              v_103
              v_104
              v_105
              v_106
              v_107
              v_108
              v_109
              v_110
              v_111
              v_112
              v_113
              v_114
              v_115
              v_116
              v_117
              v_118
              v_119
              v_120
              v_121
              v_122
              v_123
              v_124
              v_125
              v_126
              v_127
              v_128
              v_129
              v_130
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Int) (F3 Int) (G3 Int) (H3 Int) (I3 Int) (J3 Int) (K3 Int) (L3 Int) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (v_105 Int) (v_106 Int) (v_107 Bool) (v_108 Bool) (v_109 Bool) (v_110 Bool) (v_111 Bool) (v_112 Bool) (v_113 Bool) (v_114 Bool) (v_115 Bool) (v_116 Bool) (v_117 Bool) (v_118 Bool) (v_119 Bool) (v_120 Bool) (v_121 Bool) (v_122 Bool) (v_123 Bool) (v_124 Bool) (v_125 Bool) (v_126 Bool) (v_127 Bool) (v_128 Bool) (v_129 Bool) (v_130 Bool) (v_131 Bool) (v_132 Bool) (v_133 Bool) (v_134 Bool) (v_135 Bool) (v_136 Bool) (v_137 Bool) (v_138 Bool) (v_139 Bool) (v_140 Bool) (v_141 Bool) (v_142 Bool) (v_143 Bool) (v_144 Bool) (v_145 Bool) (v_146 Bool) (v_147 Bool) (v_148 Bool) (v_149 Bool) (v_150 Bool) (v_151 Bool) (v_152 Bool) (v_153 Bool) (v_154 Bool) ) 
    (=>
      (and
        (and (= M1 (- 1))
     (= L1 (- 1))
     (= K1 (- 1))
     (= J1 (- 1))
     (= I1 (- 1))
     (= P (- 1))
     (= O (- 1))
     (= N (- 1))
     (= M (- 1))
     (= L (- 1))
     (= K (- 1))
     (= Q (- 1))
     (= O1 (- 1))
     (= W (- 1))
     (= V (- 1))
     (= U (- 1))
     (= T (- 1))
     (= S (- 1))
     (= R (- 1))
     (= J (- 1))
     (= I (- 1))
     (= H (- 1))
     (= G (- 1))
     (= F (- 1))
     (= E (- 1))
     (= D (- 1))
     (= C (- 1))
     (= B (- 1))
     (= A (- 1))
     (= U1 (- 1))
     (= T1 (- 1))
     (= S1 (- 1))
     (= R1 (- 1))
     (= Q1 (- 1))
     (= P1 (- 1))
     (= H1 (- 1))
     (= G1 (- 1))
     (= F1 (- 1))
     (= E1 (- 1))
     (= D1 (- 1))
     (= C1 (- 1))
     (= B1 (- 1))
     (= A1 (- 1))
     (= Z (- 1))
     (= Y (- 1))
     (= X (- 1))
     (= V1 (- 1))
     (= N1 (- 1))
     (= 4 v_105)
     (= 1 v_106)
     (= v_107 false)
     (= v_108 false)
     (= v_109 false)
     (= v_110 false)
     (= v_111 false)
     (= v_112 false)
     (= v_113 false)
     (= v_114 false)
     (= v_115 false)
     (= v_116 false)
     (= v_117 false)
     (= v_118 false)
     (= v_119 false)
     (= v_120 false)
     (= v_121 false)
     (= v_122 false)
     (= v_123 false)
     (= v_124 false)
     (= v_125 false)
     (= v_126 false)
     (= v_127 false)
     (= v_128 false)
     (= v_129 false)
     (= v_130 false)
     (= v_131 false)
     (= v_132 false)
     (= v_133 false)
     (= v_134 false)
     (= v_135 false)
     (= v_136 false)
     (= v_137 false)
     (= v_138 false)
     (= v_139 false)
     (= v_140 false)
     (= v_141 false)
     (= v_142 false)
     (= v_143 false)
     (= v_144 false)
     (= v_145 false)
     (= v_146 false)
     (= v_147 false)
     (= v_148 false)
     (= v_149 false)
     (= v_150 false)
     (= v_151 false)
     (= v_152 false)
     (= v_153 false)
     (= v_154 false))
      )
      (transition-6 v_105
              A4
              v_106
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              N2
              M2
              L2
              K2
              J2
              I2
              H2
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
              v_107
              v_108
              v_109
              v_110
              v_111
              v_112
              v_113
              v_114
              v_115
              v_116
              v_117
              v_118
              v_119
              v_120
              v_121
              v_122
              v_123
              v_124
              v_125
              v_126
              v_127
              v_128
              v_129
              v_130
              v_131
              v_132
              v_133
              v_134
              v_135
              v_136
              v_137
              v_138
              v_139
              v_140
              v_141
              v_142
              v_143
              v_144
              v_145
              v_146
              v_147
              v_148
              v_149
              v_150
              v_151
              v_152
              v_153
              v_154
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Int) (F3 Int) (G3 Int) (H3 Int) (I3 Int) (J3 Int) (K3 Int) (L3 Int) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Int) (D4 Int) (E4 Int) (F4 Int) (G4 Int) (H4 Int) (I4 Int) (J4 Int) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (v_121 Int) (v_122 Int) (v_123 Bool) (v_124 Bool) (v_125 Bool) (v_126 Bool) (v_127 Bool) (v_128 Bool) (v_129 Bool) (v_130 Bool) (v_131 Bool) (v_132 Bool) (v_133 Bool) (v_134 Bool) (v_135 Bool) (v_136 Bool) (v_137 Bool) (v_138 Bool) (v_139 Bool) (v_140 Bool) (v_141 Bool) (v_142 Bool) (v_143 Bool) (v_144 Bool) (v_145 Bool) (v_146 Bool) (v_147 Bool) (v_148 Bool) (v_149 Bool) (v_150 Bool) (v_151 Bool) (v_152 Bool) (v_153 Bool) (v_154 Bool) (v_155 Bool) (v_156 Bool) (v_157 Bool) (v_158 Bool) (v_159 Bool) (v_160 Bool) (v_161 Bool) (v_162 Bool) (v_163 Bool) (v_164 Bool) (v_165 Bool) (v_166 Bool) (v_167 Bool) (v_168 Bool) (v_169 Bool) (v_170 Bool) (v_171 Bool) (v_172 Bool) (v_173 Bool) (v_174 Bool) (v_175 Bool) (v_176 Bool) (v_177 Bool) (v_178 Bool) ) 
    (=>
      (and
        (and (= G (- 1))
     (= F (- 1))
     (= E (- 1))
     (= D (- 1))
     (= C (- 1))
     (= D2 (- 1))
     (= C2 (- 1))
     (= B2 (- 1))
     (= A2 (- 1))
     (= Z1 (- 1))
     (= Y1 (- 1))
     (= F1 (- 1))
     (= E1 (- 1))
     (= D1 (- 1))
     (= C1 (- 1))
     (= B1 (- 1))
     (= A1 (- 1))
     (= I (- 1))
     (= G1 (- 1))
     (= O (- 1))
     (= N (- 1))
     (= M (- 1))
     (= L (- 1))
     (= K (- 1))
     (= J (- 1))
     (= B (- 1))
     (= A (- 1))
     (= M1 (- 1))
     (= L1 (- 1))
     (= K1 (- 1))
     (= J1 (- 1))
     (= I1 (- 1))
     (= H1 (- 1))
     (= Z (- 1))
     (= Y (- 1))
     (= X (- 1))
     (= W (- 1))
     (= V (- 1))
     (= U (- 1))
     (= T (- 1))
     (= S (- 1))
     (= R (- 1))
     (= Q (- 1))
     (= P (- 1))
     (= X1 (- 1))
     (= W1 (- 1))
     (= V1 (- 1))
     (= U1 (- 1))
     (= T1 (- 1))
     (= S1 (- 1))
     (= R1 (- 1))
     (= Q1 (- 1))
     (= P1 (- 1))
     (= O1 (- 1))
     (= N1 (- 1))
     (= H (- 1))
     (= 4 v_121)
     (= 1 v_122)
     (= v_123 false)
     (= v_124 false)
     (= v_125 false)
     (= v_126 false)
     (= v_127 false)
     (= v_128 false)
     (= v_129 false)
     (= v_130 false)
     (= v_131 false)
     (= v_132 false)
     (= v_133 false)
     (= v_134 false)
     (= v_135 false)
     (= v_136 false)
     (= v_137 false)
     (= v_138 false)
     (= v_139 false)
     (= v_140 false)
     (= v_141 false)
     (= v_142 false)
     (= v_143 false)
     (= v_144 false)
     (= v_145 false)
     (= v_146 false)
     (= v_147 false)
     (= v_148 false)
     (= v_149 false)
     (= v_150 false)
     (= v_151 false)
     (= v_152 false)
     (= v_153 false)
     (= v_154 false)
     (= v_155 false)
     (= v_156 false)
     (= v_157 false)
     (= v_158 false)
     (= v_159 false)
     (= v_160 false)
     (= v_161 false)
     (= v_162 false)
     (= v_163 false)
     (= v_164 false)
     (= v_165 false)
     (= v_166 false)
     (= v_167 false)
     (= v_168 false)
     (= v_169 false)
     (= v_170 false)
     (= v_171 false)
     (= v_172 false)
     (= v_173 false)
     (= v_174 false)
     (= v_175 false)
     (= v_176 false)
     (= v_177 false)
     (= v_178 false))
      )
      (transition-7 v_121
              Q4
              v_122
              P4
              O4
              N4
              M4
              L4
              K4
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              F2
              E2
              v_123
              v_124
              v_125
              v_126
              v_127
              v_128
              v_129
              v_130
              v_131
              v_132
              v_133
              v_134
              v_135
              v_136
              v_137
              v_138
              v_139
              v_140
              v_141
              v_142
              v_143
              v_144
              v_145
              v_146
              v_147
              v_148
              v_149
              v_150
              v_151
              v_152
              v_153
              v_154
              v_155
              v_156
              v_157
              v_158
              v_159
              v_160
              v_161
              v_162
              v_163
              v_164
              v_165
              v_166
              v_167
              v_168
              v_169
              v_170
              v_171
              v_172
              v_173
              v_174
              v_175
              v_176
              v_177
              v_178
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) (M Int) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Int) (J1 Int) (K1 Int) (L1 Int) (M1 Int) (N1 Int) (O1 Int) (P1 Int) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Int) (H2 Int) (I2 Int) (J2 Int) (K2 Int) (L2 Int) (M2 Int) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Int) (F3 Int) (G3 Int) (H3 Int) (I3 Int) (J3 Int) (K3 Int) (L3 Int) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Int) (D4 Int) (E4 Int) (F4 Int) (G4 Int) (H4 Int) (I4 Int) (J4 Int) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Int) (B5 Int) (C5 Int) (D5 Int) (E5 Int) (F5 Int) (G5 Int) (v_137 Int) (v_138 Int) (v_139 Bool) (v_140 Bool) (v_141 Bool) (v_142 Bool) (v_143 Bool) (v_144 Bool) (v_145 Bool) (v_146 Bool) (v_147 Bool) (v_148 Bool) (v_149 Bool) (v_150 Bool) (v_151 Bool) (v_152 Bool) (v_153 Bool) (v_154 Bool) (v_155 Bool) (v_156 Bool) (v_157 Bool) (v_158 Bool) (v_159 Bool) (v_160 Bool) (v_161 Bool) (v_162 Bool) (v_163 Bool) (v_164 Bool) (v_165 Bool) (v_166 Bool) (v_167 Bool) (v_168 Bool) (v_169 Bool) (v_170 Bool) (v_171 Bool) (v_172 Bool) (v_173 Bool) (v_174 Bool) (v_175 Bool) (v_176 Bool) (v_177 Bool) (v_178 Bool) (v_179 Bool) (v_180 Bool) (v_181 Bool) (v_182 Bool) (v_183 Bool) (v_184 Bool) (v_185 Bool) (v_186 Bool) (v_187 Bool) (v_188 Bool) (v_189 Bool) (v_190 Bool) (v_191 Bool) (v_192 Bool) (v_193 Bool) (v_194 Bool) (v_195 Bool) (v_196 Bool) (v_197 Bool) (v_198 Bool) (v_199 Bool) (v_200 Bool) (v_201 Bool) (v_202 Bool) ) 
    (=>
      (and
        (and (= W (- 1))
     (= V (- 1))
     (= U (- 1))
     (= T (- 1))
     (= S (- 1))
     (= V1 (- 1))
     (= U1 (- 1))
     (= T1 (- 1))
     (= S1 (- 1))
     (= R1 (- 1))
     (= Q1 (- 1))
     (= A (- 1))
     (= Y (- 1))
     (= W1 (- 1))
     (= G (- 1))
     (= F (- 1))
     (= E (- 1))
     (= D (- 1))
     (= C (- 1))
     (= B (- 1))
     (= E1 (- 1))
     (= D1 (- 1))
     (= C1 (- 1))
     (= B1 (- 1))
     (= A1 (- 1))
     (= Z (- 1))
     (= R (- 1))
     (= Q (- 1))
     (= P (- 1))
     (= O (- 1))
     (= N (- 1))
     (= M (- 1))
     (= L (- 1))
     (= K (- 1))
     (= J (- 1))
     (= I (- 1))
     (= H (- 1))
     (= C2 (- 1))
     (= B2 (- 1))
     (= A2 (- 1))
     (= Z1 (- 1))
     (= Y1 (- 1))
     (= X1 (- 1))
     (= P1 (- 1))
     (= O1 (- 1))
     (= N1 (- 1))
     (= M1 (- 1))
     (= L1 (- 1))
     (= K1 (- 1))
     (= J1 (- 1))
     (= I1 (- 1))
     (= H1 (- 1))
     (= G1 (- 1))
     (= F1 (- 1))
     (= L2 (- 1))
     (= K2 (- 1))
     (= J2 (- 1))
     (= I2 (- 1))
     (= H2 (- 1))
     (= G2 (- 1))
     (= F2 (- 1))
     (= E2 (- 1))
     (= D2 (- 1))
     (= X (- 1))
     (= 4 v_137)
     (= 1 v_138)
     (= v_139 false)
     (= v_140 false)
     (= v_141 false)
     (= v_142 false)
     (= v_143 false)
     (= v_144 false)
     (= v_145 false)
     (= v_146 false)
     (= v_147 false)
     (= v_148 false)
     (= v_149 false)
     (= v_150 false)
     (= v_151 false)
     (= v_152 false)
     (= v_153 false)
     (= v_154 false)
     (= v_155 false)
     (= v_156 false)
     (= v_157 false)
     (= v_158 false)
     (= v_159 false)
     (= v_160 false)
     (= v_161 false)
     (= v_162 false)
     (= v_163 false)
     (= v_164 false)
     (= v_165 false)
     (= v_166 false)
     (= v_167 false)
     (= v_168 false)
     (= v_169 false)
     (= v_170 false)
     (= v_171 false)
     (= v_172 false)
     (= v_173 false)
     (= v_174 false)
     (= v_175 false)
     (= v_176 false)
     (= v_177 false)
     (= v_178 false)
     (= v_179 false)
     (= v_180 false)
     (= v_181 false)
     (= v_182 false)
     (= v_183 false)
     (= v_184 false)
     (= v_185 false)
     (= v_186 false)
     (= v_187 false)
     (= v_188 false)
     (= v_189 false)
     (= v_190 false)
     (= v_191 false)
     (= v_192 false)
     (= v_193 false)
     (= v_194 false)
     (= v_195 false)
     (= v_196 false)
     (= v_197 false)
     (= v_198 false)
     (= v_199 false)
     (= v_200 false)
     (= v_201 false)
     (= v_202 false))
      )
      (transition-8 v_137
              G5
              v_138
              F5
              E5
              D5
              C5
              B5
              A5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              N2
              M2
              v_139
              v_140
              v_141
              v_142
              v_143
              v_144
              v_145
              v_146
              v_147
              v_148
              v_149
              v_150
              v_151
              v_152
              v_153
              v_154
              v_155
              v_156
              v_157
              v_158
              v_159
              v_160
              v_161
              v_162
              v_163
              v_164
              v_165
              v_166
              v_167
              v_168
              v_169
              v_170
              v_171
              v_172
              v_173
              v_174
              v_175
              v_176
              v_177
              v_178
              v_179
              v_180
              v_181
              v_182
              v_183
              v_184
              v_185
              v_186
              v_187
              v_188
              v_189
              v_190
              v_191
              v_192
              v_193
              v_194
              v_195
              v_196
              v_197
              v_198
              v_199
              v_200
              v_201
              v_202
              L2
              K2
              J2
              I2
              H2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (v_11 Int) (v_12 Bool) (v_13 Int) (v_14 Bool) ) 
    (=>
      (and
        (transition-0 v_11 K I H G F E D C B A v_12)
        (and (= 1 v_11) (= v_12 false) (= 0 v_13) (= v_14 false))
      )
      (transition-0 v_13 J I H G F E D C B A v_14)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (v_34 Int) (v_35 Bool) (v_36 Int) (v_37 Bool) ) 
    (=>
      (and
        (transition-1 v_34
              H1
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
              K
              J
              I
              v_35
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 1 v_34)
     (= v_35 false)
     (or (not Q) (not (= A1 2)))
     (or (not P) (not (= A1 3)))
     (or (not O) (not (= A1 4)))
     (or (not N) (not (= A1 5)))
     (or (not M) (not (= A1 6)))
     (or (not L) (not (= A1 7)))
     (or (not R) (not (= A1 1)))
     (= 0 v_36)
     (= v_37 false))
      )
      (transition-1 v_36
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
              K
              J
              I
              v_37
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (v_58 Int) (v_59 Bool) (v_60 Int) (v_61 Bool) ) 
    (=>
      (and
        (transition-2 v_58
              F2
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
              v_59
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 1 v_58)
     (= v_59 false)
     (or (not R) (not (= Y1 9)))
     (or (not Q) (not (= Y1 10)))
     (or (not P) (not (= Y1 11)))
     (or (not O) (not (= Y1 12)))
     (or (not N) (not (= Y1 13)))
     (or (not M) (not (= Y1 14)))
     (or (not L) (not (= Y1 15)))
     (or (not P1) (not (= Y1 1)))
     (or (not O1) (not (= Y1 2)))
     (or (not N1) (not (= Y1 3)))
     (or (not M1) (not (= Y1 4)))
     (or (not L1) (not (= Y1 5)))
     (or (not K1) (not (= Y1 6)))
     (or (not J1) (not (= Y1 7)))
     (or (not I1) (not (= Y1 8)))
     (= 0 v_60)
     (= v_61 false))
      )
      (transition-2 v_60
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
              v_61
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (v_82 Int) (v_83 Bool) (v_84 Int) (v_85 Bool) ) 
    (=>
      (and
        (transition-3 v_82
              D3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_83
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1 v_82)
     (= v_83 false)
     (or (not R) (not (= W2 17)))
     (or (not Q) (not (= W2 18)))
     (or (not P) (not (= W2 19)))
     (or (not O) (not (= W2 20)))
     (or (not N) (not (= W2 21)))
     (or (not M) (not (= W2 22)))
     (or (not L) (not (= W2 23)))
     (or (not G2) (not (= W2 8)))
     (or (not P1) (not (= W2 9)))
     (or (not O1) (not (= W2 10)))
     (or (not N1) (not (= W2 11)))
     (or (not M1) (not (= W2 12)))
     (or (not L1) (not (= W2 13)))
     (or (not K1) (not (= W2 14)))
     (or (not J1) (not (= W2 15)))
     (or (not N2) (not (= W2 1)))
     (or (not M2) (not (= W2 2)))
     (or (not L2) (not (= W2 3)))
     (or (not K2) (not (= W2 4)))
     (or (not J2) (not (= W2 5)))
     (or (not I2) (not (= W2 6)))
     (or (not H2) (not (= W2 7)))
     (or (not I1) (not (= W2 16)))
     (= 0 v_84)
     (= v_85 false))
      )
      (transition-3 v_84
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_85
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (v_106 Int) (v_107 Bool) (v_108 Int) (v_109 Bool) ) 
    (=>
      (and
        (transition-4 v_106
              B4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_107
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 1 v_106)
     (= v_107 false)
     (or (not R) (not (= U3 25)))
     (or (not Q) (not (= U3 26)))
     (or (not P) (not (= U3 27)))
     (or (not O) (not (= U3 28)))
     (or (not N) (not (= U3 29)))
     (or (not M) (not (= U3 30)))
     (or (not L) (not (= U3 31)))
     (or (not G2) (not (= U3 16)))
     (or (not P1) (not (= U3 17)))
     (or (not O1) (not (= U3 18)))
     (or (not N1) (not (= U3 19)))
     (or (not M1) (not (= U3 20)))
     (or (not L1) (not (= U3 21)))
     (or (not K1) (not (= U3 22)))
     (or (not J1) (not (= U3 23)))
     (or (not E3) (not (= U3 8)))
     (or (not N2) (not (= U3 9)))
     (or (not M2) (not (= U3 10)))
     (or (not L2) (not (= U3 11)))
     (or (not K2) (not (= U3 12)))
     (or (not J2) (not (= U3 13)))
     (or (not I2) (not (= U3 14)))
     (or (not H2) (not (= U3 15)))
     (or (not L3) (not (= U3 1)))
     (or (not K3) (not (= U3 2)))
     (or (not J3) (not (= U3 3)))
     (or (not I3) (not (= U3 4)))
     (or (not H3) (not (= U3 5)))
     (or (not G3) (not (= U3 6)))
     (or (not F3) (not (= U3 7)))
     (or (not I1) (not (= U3 24)))
     (= 0 v_108)
     (= v_109 false))
      )
      (transition-4 v_108
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_109
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (v_130 Int) (v_131 Bool) (v_132 Int) (v_133 Bool) ) 
    (=>
      (and
        (transition-5 v_130
              Z4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_131
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 1 v_130)
     (= v_131 false)
     (or (not R) (not (= S4 33)))
     (or (not Q) (not (= S4 34)))
     (or (not P) (not (= S4 35)))
     (or (not O) (not (= S4 36)))
     (or (not N) (not (= S4 37)))
     (or (not M) (not (= S4 38)))
     (or (not L) (not (= S4 39)))
     (or (not G2) (not (= S4 24)))
     (or (not P1) (not (= S4 25)))
     (or (not O1) (not (= S4 26)))
     (or (not N1) (not (= S4 27)))
     (or (not M1) (not (= S4 28)))
     (or (not L1) (not (= S4 29)))
     (or (not K1) (not (= S4 30)))
     (or (not J1) (not (= S4 31)))
     (or (not E3) (not (= S4 16)))
     (or (not N2) (not (= S4 17)))
     (or (not M2) (not (= S4 18)))
     (or (not L2) (not (= S4 19)))
     (or (not K2) (not (= S4 20)))
     (or (not J2) (not (= S4 21)))
     (or (not I2) (not (= S4 22)))
     (or (not H2) (not (= S4 23)))
     (or (not C4) (not (= S4 8)))
     (or (not L3) (not (= S4 9)))
     (or (not K3) (not (= S4 10)))
     (or (not J3) (not (= S4 11)))
     (or (not I3) (not (= S4 12)))
     (or (not H3) (not (= S4 13)))
     (or (not G3) (not (= S4 14)))
     (or (not F3) (not (= S4 15)))
     (or (not J4) (not (= S4 1)))
     (or (not I4) (not (= S4 2)))
     (or (not H4) (not (= S4 3)))
     (or (not G4) (not (= S4 4)))
     (or (not F4) (not (= S4 5)))
     (or (not E4) (not (= S4 6)))
     (or (not D4) (not (= S4 7)))
     (or (not I1) (not (= S4 32)))
     (= 0 v_132)
     (= v_133 false))
      )
      (transition-5 v_132
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_133
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (v_154 Int) (v_155 Bool) (v_156 Int) (v_157 Bool) ) 
    (=>
      (and
        (transition-6 v_154
              X5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_155
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1 v_154)
     (= v_155 false)
     (or (not R) (not (= Q5 41)))
     (or (not Q) (not (= Q5 42)))
     (or (not P) (not (= Q5 43)))
     (or (not O) (not (= Q5 44)))
     (or (not N) (not (= Q5 45)))
     (or (not M) (not (= Q5 46)))
     (or (not L) (not (= Q5 47)))
     (or (not G2) (not (= Q5 32)))
     (or (not P1) (not (= Q5 33)))
     (or (not O1) (not (= Q5 34)))
     (or (not N1) (not (= Q5 35)))
     (or (not M1) (not (= Q5 36)))
     (or (not L1) (not (= Q5 37)))
     (or (not K1) (not (= Q5 38)))
     (or (not J1) (not (= Q5 39)))
     (or (not E3) (not (= Q5 24)))
     (or (not N2) (not (= Q5 25)))
     (or (not M2) (not (= Q5 26)))
     (or (not L2) (not (= Q5 27)))
     (or (not K2) (not (= Q5 28)))
     (or (not J2) (not (= Q5 29)))
     (or (not I2) (not (= Q5 30)))
     (or (not H2) (not (= Q5 31)))
     (or (not C4) (not (= Q5 16)))
     (or (not L3) (not (= Q5 17)))
     (or (not K3) (not (= Q5 18)))
     (or (not J3) (not (= Q5 19)))
     (or (not I3) (not (= Q5 20)))
     (or (not H3) (not (= Q5 21)))
     (or (not G3) (not (= Q5 22)))
     (or (not F3) (not (= Q5 23)))
     (or (not A5) (not (= Q5 8)))
     (or (not J4) (not (= Q5 9)))
     (or (not I4) (not (= Q5 10)))
     (or (not H4) (not (= Q5 11)))
     (or (not G4) (not (= Q5 12)))
     (or (not F4) (not (= Q5 13)))
     (or (not E4) (not (= Q5 14)))
     (or (not D4) (not (= Q5 15)))
     (or (not H5) (not (= Q5 1)))
     (or (not G5) (not (= Q5 2)))
     (or (not F5) (not (= Q5 3)))
     (or (not E5) (not (= Q5 4)))
     (or (not D5) (not (= Q5 5)))
     (or (not C5) (not (= Q5 6)))
     (or (not B5) (not (= Q5 7)))
     (or (not I1) (not (= Q5 40)))
     (= 0 v_156)
     (= v_157 false))
      )
      (transition-6 v_156
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_157
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (v_178 Int) (v_179 Bool) (v_180 Int) (v_181 Bool) ) 
    (=>
      (and
        (transition-7 v_178
              V6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_179
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1 v_178)
     (= v_179 false)
     (or (not R) (not (= O6 49)))
     (or (not Q) (not (= O6 50)))
     (or (not P) (not (= O6 51)))
     (or (not O) (not (= O6 52)))
     (or (not N) (not (= O6 53)))
     (or (not M) (not (= O6 54)))
     (or (not L) (not (= O6 55)))
     (or (not G2) (not (= O6 40)))
     (or (not P1) (not (= O6 41)))
     (or (not O1) (not (= O6 42)))
     (or (not N1) (not (= O6 43)))
     (or (not M1) (not (= O6 44)))
     (or (not L1) (not (= O6 45)))
     (or (not K1) (not (= O6 46)))
     (or (not J1) (not (= O6 47)))
     (or (not E3) (not (= O6 32)))
     (or (not N2) (not (= O6 33)))
     (or (not M2) (not (= O6 34)))
     (or (not L2) (not (= O6 35)))
     (or (not K2) (not (= O6 36)))
     (or (not J2) (not (= O6 37)))
     (or (not I2) (not (= O6 38)))
     (or (not H2) (not (= O6 39)))
     (or (not C4) (not (= O6 24)))
     (or (not L3) (not (= O6 25)))
     (or (not K3) (not (= O6 26)))
     (or (not J3) (not (= O6 27)))
     (or (not I3) (not (= O6 28)))
     (or (not H3) (not (= O6 29)))
     (or (not G3) (not (= O6 30)))
     (or (not F3) (not (= O6 31)))
     (or (not A5) (not (= O6 16)))
     (or (not J4) (not (= O6 17)))
     (or (not I4) (not (= O6 18)))
     (or (not H4) (not (= O6 19)))
     (or (not G4) (not (= O6 20)))
     (or (not F4) (not (= O6 21)))
     (or (not E4) (not (= O6 22)))
     (or (not D4) (not (= O6 23)))
     (or (not Y5) (not (= O6 8)))
     (or (not H5) (not (= O6 9)))
     (or (not G5) (not (= O6 10)))
     (or (not F5) (not (= O6 11)))
     (or (not E5) (not (= O6 12)))
     (or (not D5) (not (= O6 13)))
     (or (not C5) (not (= O6 14)))
     (or (not B5) (not (= O6 15)))
     (or (not F6) (not (= O6 1)))
     (or (not E6) (not (= O6 2)))
     (or (not D6) (not (= O6 3)))
     (or (not C6) (not (= O6 4)))
     (or (not B6) (not (= O6 5)))
     (or (not A6) (not (= O6 6)))
     (or (not Z5) (not (= O6 7)))
     (or (not I1) (not (= O6 48)))
     (= 0 v_180)
     (= v_181 false))
      )
      (transition-7 v_180
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_181
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (v_202 Int) (v_203 Bool) (v_204 Int) (v_205 Bool) ) 
    (=>
      (and
        (transition-8 v_202
              T7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_203
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 1 v_202)
     (= v_203 false)
     (or (not R) (not (= M7 57)))
     (or (not Q) (not (= M7 58)))
     (or (not P) (not (= M7 59)))
     (or (not O) (not (= M7 60)))
     (or (not N) (not (= M7 61)))
     (or (not M) (not (= M7 62)))
     (or (not L) (not (= M7 63)))
     (or (not G2) (not (= M7 48)))
     (or (not P1) (not (= M7 49)))
     (or (not O1) (not (= M7 50)))
     (or (not N1) (not (= M7 51)))
     (or (not M1) (not (= M7 52)))
     (or (not L1) (not (= M7 53)))
     (or (not K1) (not (= M7 54)))
     (or (not J1) (not (= M7 55)))
     (or (not E3) (not (= M7 40)))
     (or (not N2) (not (= M7 41)))
     (or (not M2) (not (= M7 42)))
     (or (not L2) (not (= M7 43)))
     (or (not K2) (not (= M7 44)))
     (or (not J2) (not (= M7 45)))
     (or (not I2) (not (= M7 46)))
     (or (not H2) (not (= M7 47)))
     (or (not C4) (not (= M7 32)))
     (or (not L3) (not (= M7 33)))
     (or (not K3) (not (= M7 34)))
     (or (not J3) (not (= M7 35)))
     (or (not I3) (not (= M7 36)))
     (or (not H3) (not (= M7 37)))
     (or (not G3) (not (= M7 38)))
     (or (not F3) (not (= M7 39)))
     (or (not A5) (not (= M7 24)))
     (or (not J4) (not (= M7 25)))
     (or (not I4) (not (= M7 26)))
     (or (not H4) (not (= M7 27)))
     (or (not G4) (not (= M7 28)))
     (or (not F4) (not (= M7 29)))
     (or (not E4) (not (= M7 30)))
     (or (not D4) (not (= M7 31)))
     (or (not Y5) (not (= M7 16)))
     (or (not H5) (not (= M7 17)))
     (or (not G5) (not (= M7 18)))
     (or (not F5) (not (= M7 19)))
     (or (not E5) (not (= M7 20)))
     (or (not D5) (not (= M7 21)))
     (or (not C5) (not (= M7 22)))
     (or (not B5) (not (= M7 23)))
     (or (not W6) (not (= M7 8)))
     (or (not F6) (not (= M7 9)))
     (or (not E6) (not (= M7 10)))
     (or (not D6) (not (= M7 11)))
     (or (not C6) (not (= M7 12)))
     (or (not B6) (not (= M7 13)))
     (or (not A6) (not (= M7 14)))
     (or (not Z5) (not (= M7 15)))
     (or (not D7) (not (= M7 1)))
     (or (not C7) (not (= M7 2)))
     (or (not B7) (not (= M7 3)))
     (or (not A7) (not (= M7 4)))
     (or (not Z6) (not (= M7 5)))
     (or (not Y6) (not (= M7 6)))
     (or (not X6) (not (= M7 7)))
     (or (not I1) (not (= M7 56)))
     (= 0 v_204)
     (= v_205 false))
      )
      (transition-8 v_204
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_205
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (v_33 Int) (v_34 Bool) (v_35 Int) (v_36 Bool) ) 
    (=>
      (and
        (transition-1 v_33
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
              K
              J
              I
              v_34
              R
              Q
              P
              O
              N
              M
              L
              H
              G
              F
              E
              D
              C
              B
              A)
        (and (= 0 v_33) (= v_34 false) (= 0 v_35) (= v_36 false))
      )
      (transition-0 v_35 G1 F1 E1 D1 C1 B1 A1 Z Y X v_36)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Int) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (v_80 Int) (v_81 Bool) (v_82 Int) (v_83 Bool) ) 
    (=>
      (and
        (transition-2 v_80
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              U1
              T1
              S1
              R1
              Q1
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
              v_81
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              W
              V
              U
              T
              S
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
        (and (= 0 v_80)
     (= v_81 false)
     (= L2 O1)
     (= K2 N1)
     (= J2 M1)
     (= I2 L1)
     (= H2 K1)
     (= G2 J1)
     (= F2 H1)
     (= Q2 T1)
     (= P2 S1)
     (= O2 R1)
     (= N2 Q1)
     (= E2 G1)
     (= D2 F1)
     (= C2 W)
     (= B2 V)
     (= A2 U)
     (= Z1 T)
     (= Y1 S)
     (= X1 K)
     (= W1 J)
     (= V1 I)
     (= R2 U1)
     (= M2 P1)
     (= 0 v_82)
     (= v_83 false))
      )
      (transition-1 v_82
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              N2
              F2
              E2
              D2
              v_83
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              C2
              B2
              A2
              Z1
              Y1
              X1
              W1
              V1)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Int) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (v_128 Int) (v_129 Bool) (v_130 Int) (v_131 Bool) ) 
    (=>
      (and
        (transition-3 v_128
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              S2
              R2
              Q2
              P2
              O2
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
              H1
              G1
              F1
              v_129
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 0 v_128)
     (= v_129 false)
     (= I4 N2)
     (= L3 G2)
     (= J3 O1)
     (= I3 N1)
     (= H3 M1)
     (= G3 L1)
     (= F3 K1)
     (= E3 J1)
     (= H4 M2)
     (= G4 L2)
     (= F4 K2)
     (= E4 J2)
     (= D4 I2)
     (= C4 H2)
     (= B4 F2)
     (= D3 Z)
     (= P3 D1)
     (= O3 C1)
     (= N3 B1)
     (= M3 A1)
     (= C3 Y)
     (= B3 X)
     (= A3 W)
     (= Z2 V)
     (= Y2 U)
     (= X2 T)
     (= W2 S)
     (= V2 K)
     (= U2 J)
     (= T2 I)
     (= M4 R2)
     (= L4 Q2)
     (= K4 P2)
     (= J4 O2)
     (= A4 E2)
     (= Z3 D2)
     (= Y3 C2)
     (= X3 B2)
     (= W3 A2)
     (= V3 Z1)
     (= U3 Y1)
     (= T3 X1)
     (= S3 W1)
     (= R3 V1)
     (= Q3 E1)
     (= N4 S2)
     (= K3 P1)
     (= 0 v_130)
     (= v_131 false))
      )
      (transition-2 v_130
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              J4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_131
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Int) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (v_176 Int) (v_177 Bool) (v_178 Int) (v_179 Bool) ) 
    (=>
      (and
        (transition-4 v_176
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
              v_177
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              U1
              T1
              S1
              R1
              Q1
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
        (and (= 0 v_176)
     (= v_177 false)
     (= G5 N2)
     (= I4 P1)
     (= E6 L3)
     (= H5 E3)
     (= H4 O1)
     (= G4 N1)
     (= F4 M1)
     (= E4 L1)
     (= D4 K1)
     (= C4 J1)
     (= F5 M2)
     (= E5 L2)
     (= D5 K2)
     (= C5 J2)
     (= B5 I2)
     (= A5 H2)
     (= D6 K3)
     (= C6 J3)
     (= B6 I3)
     (= A6 H3)
     (= Z5 G3)
     (= Y5 F3)
     (= B4 Z)
     (= X5 D3)
     (= Z4 F2)
     (= N4 D1)
     (= M4 C1)
     (= L4 B1)
     (= K4 A1)
     (= A4 Y)
     (= Z3 X)
     (= Y3 W)
     (= X3 V)
     (= W3 U)
     (= V3 T)
     (= U3 S)
     (= T3 K)
     (= S3 J)
     (= R3 I)
     (= L5 R2)
     (= K5 Q2)
     (= J5 P2)
     (= I5 O2)
     (= Y4 E2)
     (= X4 D2)
     (= W4 U1)
     (= V4 T1)
     (= U4 S1)
     (= T4 R1)
     (= S4 Q1)
     (= R4 H1)
     (= Q4 G1)
     (= P4 F1)
     (= O4 E1)
     (= I6 P3)
     (= H6 O3)
     (= G6 N3)
     (= F6 M3)
     (= W5 C3)
     (= V5 B3)
     (= U5 A3)
     (= T5 Z2)
     (= S5 Y2)
     (= R5 X2)
     (= Q5 W2)
     (= P5 V2)
     (= O5 U2)
     (= N5 T2)
     (= M5 S2)
     (= J6 Q3)
     (= J4 G2)
     (= 0 v_178)
     (= v_179 false))
      )
      (transition-3 v_178
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              F6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              v_179
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (U7 Int) (V7 Bool) (W7 Bool) (X7 Bool) (Y7 Bool) (Z7 Bool) (A8 Bool) (B8 Bool) (C8 Int) (D8 Int) (E8 Int) (F8 Int) (G8 Int) (H8 Int) (I8 Int) (J8 Int) (K8 Int) (L8 Int) (M8 Int) (N8 Int) (O8 Int) (P8 Int) (v_224 Int) (v_225 Bool) (v_226 Int) (v_227 Bool) ) 
    (=>
      (and
        (transition-5 v_224
              P8
              O8
              N8
              M8
              L8
              K8
              J8
              I8
              H8
              G8
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
              F2
              E2
              D2
              v_225
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
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
        (and (= 0 v_224)
     (= v_225 false)
     (= H5 G2)
     (= C7 L3)
     (= E6 N2)
     (= G5 P1)
     (= B8 J4)
     (= A8 I4)
     (= D7 C4)
     (= F5 O1)
     (= E5 N1)
     (= D5 M1)
     (= C5 L1)
     (= B5 K1)
     (= A5 J1)
     (= D6 M2)
     (= C6 L2)
     (= B6 K2)
     (= A6 J2)
     (= Z5 I2)
     (= Y5 H2)
     (= B7 K3)
     (= A7 J3)
     (= Z6 I3)
     (= Y6 H3)
     (= X6 G3)
     (= W6 F3)
     (= Z7 H4)
     (= Y7 G4)
     (= X7 F4)
     (= W7 E4)
     (= V7 D4)
     (= X5 X1)
     (= Z4 Z)
     (= U7 K4)
     (= T7 B4)
     (= V6 D3)
     (= L5 D1)
     (= K5 C1)
     (= J5 B1)
     (= I5 A1)
     (= Y4 Y)
     (= X4 X)
     (= W4 W)
     (= V4 V)
     (= U4 U)
     (= T4 T)
     (= S4 S)
     (= R4 K)
     (= Q4 J)
     (= P4 I)
     (= J6 B2)
     (= I6 A2)
     (= H6 Z1)
     (= G6 Y1)
     (= W5 W1)
     (= V5 V1)
     (= U5 U1)
     (= T5 T1)
     (= S5 S1)
     (= R5 R1)
     (= Q5 Q1)
     (= P5 H1)
     (= O5 G1)
     (= N5 F1)
     (= M5 E1)
     (= H7 P3)
     (= G7 O3)
     (= F7 N3)
     (= E7 M3)
     (= U6 C3)
     (= T6 B3)
     (= S6 A3)
     (= R6 Z2)
     (= Q6 Y2)
     (= P6 X2)
     (= O6 W2)
     (= N6 V2)
     (= M6 U2)
     (= L6 T2)
     (= K6 C2)
     (= E8 N4)
     (= D8 M4)
     (= C8 L4)
     (= S7 A4)
     (= R7 Z3)
     (= Q7 Y3)
     (= P7 X3)
     (= O7 W3)
     (= N7 V3)
     (= M7 U3)
     (= L7 T3)
     (= K7 S3)
     (= J7 R3)
     (= I7 Q3)
     (= F8 O4)
     (= F6 E3)
     (= 0 v_226)
     (= v_227 false))
      )
      (transition-4 v_226
              P8
              O8
              N8
              M8
              L8
              K8
              J8
              I8
              H8
              G8
              F8
              E8
              D8
              C8
              U7
              T7
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              v_227
              B8
              A8
              Z7
              Y7
              X7
              W7
              V7
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (U7 Int) (V7 Bool) (W7 Bool) (X7 Bool) (Y7 Bool) (Z7 Bool) (A8 Bool) (B8 Bool) (C8 Bool) (D8 Bool) (E8 Bool) (F8 Bool) (G8 Bool) (H8 Bool) (I8 Bool) (J8 Bool) (K8 Bool) (L8 Bool) (M8 Bool) (N8 Bool) (O8 Bool) (P8 Bool) (Q8 Bool) (R8 Int) (S8 Int) (T8 Int) (U8 Int) (V8 Int) (W8 Int) (X8 Int) (Y8 Int) (Z8 Int) (A9 Int) (B9 Int) (C9 Int) (D9 Int) (E9 Int) (F9 Int) (G9 Int) (H9 Bool) (I9 Int) (J9 Int) (K9 Int) (L9 Int) (M9 Int) (N9 Int) (O9 Int) (P9 Int) (Q9 Int) (R9 Int) (S9 Int) (T9 Int) (U9 Int) (V9 Int) (W9 Int) (X9 Int) (Y9 Int) (Z9 Int) (A10 Int) (B10 Int) (C10 Int) (D10 Int) (E10 Int) (F10 Int) (G10 Int) (H10 Int) (I10 Int) (J10 Int) (K10 Int) (L10 Int) (v_272 Int) (v_273 Bool) (v_274 Int) (v_275 Bool) ) 
    (=>
      (and
        (transition-6 v_272
              L10
              K10
              J10
              I10
              H10
              G10
              F10
              E10
              D10
              C10
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              v_273
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 0 v_272)
     (= v_273 false)
     (= H8 H4)
     (= G8 G4)
     (= F8 F4)
     (= E8 E4)
     (= D8 D4)
     (= C8 C4)
     (= B8 L3)
     (= D7 E3)
     (= F6 G2)
     (= A8 K3)
     (= C7 N2)
     (= E6 P1)
     (= H9 H5)
     (= O8 E5)
     (= N8 D5)
     (= M8 C5)
     (= L8 B5)
     (= K8 A5)
     (= J8 J4)
     (= P8 F5)
     (= D6 O1)
     (= C6 N1)
     (= B6 M1)
     (= A6 L1)
     (= Z5 K1)
     (= Y5 J1)
     (= B7 M2)
     (= A7 L2)
     (= Z6 K2)
     (= Y6 J2)
     (= X6 I2)
     (= W6 H2)
     (= Q8 G5)
     (= Z7 J3)
     (= Y7 I3)
     (= X7 H3)
     (= W7 G3)
     (= V7 F3)
     (= X5 Z)
     (= U7 M3)
     (= T7 D3)
     (= V6 X1)
     (= U9 X4)
     (= T9 W4)
     (= S9 V4)
     (= R9 U4)
     (= Q9 T4)
     (= P9 S4)
     (= W8 S3)
     (= V8 R3)
     (= U8 Q3)
     (= T8 P3)
     (= S8 O3)
     (= R8 N3)
     (= X8 T3)
     (= V9 Y4)
     (= J6 D1)
     (= I6 C1)
     (= H6 B1)
     (= G6 A1)
     (= W5 Y)
     (= V5 X)
     (= U5 W)
     (= T5 V)
     (= S5 U)
     (= R5 T)
     (= Q5 S)
     (= P5 K)
     (= O5 J)
     (= N5 I)
     (= H7 B2)
     (= G7 A2)
     (= F7 Z1)
     (= E7 Y1)
     (= U6 W1)
     (= T6 V1)
     (= S6 U1)
     (= R6 T1)
     (= Q6 S1)
     (= P6 R1)
     (= O6 Q1)
     (= N6 H1)
     (= M6 G1)
     (= L6 F1)
     (= K6 E1)
     (= S7 C3)
     (= R7 B3)
     (= Q7 S2)
     (= P7 R2)
     (= O7 Q2)
     (= N7 P2)
     (= M7 O2)
     (= L7 F2)
     (= K7 E2)
     (= J7 D2)
     (= I7 C2)
     (= D9 Z3)
     (= C9 Y3)
     (= B9 X3)
     (= A9 W3)
     (= Z8 V3)
     (= Y8 U3)
     (= A10 L5)
     (= Z9 K5)
     (= Y9 J5)
     (= X9 I5)
     (= W9 Z4)
     (= O9 R4)
     (= N9 Q4)
     (= M9 P4)
     (= L9 O4)
     (= K9 N4)
     (= J9 M4)
     (= I9 L4)
     (= G9 K4)
     (= F9 B4)
     (= E9 A4)
     (= B10 M5)
     (= I8 I4)
     (= 0 v_274)
     (= v_275 false))
      )
      (transition-5 v_274
              L10
              K10
              J10
              I10
              H10
              G10
              F10
              E10
              D10
              C10
              B10
              A10
              Z9
              Y9
              X9
              W9
              V9
              U9
              T9
              S9
              R9
              Q9
              P9
              O9
              N9
              M9
              L9
              K9
              J9
              I9
              G9
              F9
              E9
              D9
              C9
              B9
              A9
              Z8
              Y8
              X8
              W8
              V8
              U8
              T8
              S8
              R8
              U7
              T7
              S7
              R7
              v_275
              H9
              Q8
              P8
              O8
              N8
              M8
              L8
              K8
              J8
              I8
              H8
              G8
              F8
              E8
              D8
              C8
              B8
              A8
              Z7
              Y7
              X7
              W7
              V7
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (U7 Int) (V7 Bool) (W7 Bool) (X7 Bool) (Y7 Bool) (Z7 Bool) (A8 Bool) (B8 Bool) (C8 Bool) (D8 Bool) (E8 Bool) (F8 Bool) (G8 Bool) (H8 Bool) (I8 Bool) (J8 Bool) (K8 Bool) (L8 Bool) (M8 Bool) (N8 Bool) (O8 Bool) (P8 Bool) (Q8 Bool) (R8 Int) (S8 Int) (T8 Int) (U8 Int) (V8 Int) (W8 Int) (X8 Int) (Y8 Int) (Z8 Int) (A9 Int) (B9 Int) (C9 Int) (D9 Int) (E9 Int) (F9 Int) (G9 Int) (H9 Bool) (I9 Bool) (J9 Bool) (K9 Bool) (L9 Bool) (M9 Bool) (N9 Bool) (O9 Bool) (P9 Bool) (Q9 Bool) (R9 Bool) (S9 Bool) (T9 Bool) (U9 Bool) (V9 Bool) (W9 Bool) (X9 Bool) (Y9 Int) (Z9 Int) (A10 Int) (B10 Int) (C10 Int) (D10 Int) (E10 Int) (F10 Int) (G10 Int) (H10 Int) (I10 Int) (J10 Int) (K10 Int) (L10 Int) (M10 Int) (N10 Int) (O10 Int) (P10 Int) (Q10 Int) (R10 Int) (S10 Int) (T10 Int) (U10 Int) (V10 Int) (W10 Int) (X10 Int) (Y10 Int) (Z10 Int) (A11 Int) (B11 Int) (C11 Int) (D11 Int) (E11 Int) (F11 Int) (G11 Int) (H11 Int) (I11 Int) (J11 Int) (K11 Int) (L11 Int) (M11 Int) (N11 Int) (O11 Int) (P11 Int) (Q11 Int) (R11 Int) (S11 Int) (T11 Int) (U11 Int) (V11 Int) (W11 Int) (X11 Int) (Y11 Int) (Z11 Int) (A12 Int) (B12 Int) (C12 Int) (D12 Int) (E12 Int) (F12 Int) (G12 Int) (H12 Int) (v_320 Int) (v_321 Bool) (v_322 Int) (v_323 Bool) ) 
    (=>
      (and
        (transition-7 v_320
              H12
              G12
              F12
              E12
              D12
              C12
              B12
              A12
              Z11
              Y11
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              v_321
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 0 v_320)
     (= v_321 false)
     (= X9 F6)
     (= I8 K3)
     (= H8 J3)
     (= G8 I3)
     (= F8 H3)
     (= E8 G3)
     (= D8 F3)
     (= C8 E3)
     (= B8 N2)
     (= D7 G2)
     (= W9 E6)
     (= A8 M2)
     (= C7 P1)
     (= M9 E5)
     (= L9 D5)
     (= K9 C5)
     (= J9 B5)
     (= I9 A5)
     (= H9 J4)
     (= O8 G4)
     (= N8 F4)
     (= M8 E4)
     (= L8 D4)
     (= K8 C4)
     (= P8 H4)
     (= N9 F5)
     (= B7 O1)
     (= A7 N1)
     (= Z6 M1)
     (= Y6 L1)
     (= X6 K1)
     (= W6 J1)
     (= Q8 I4)
     (= Z7 L2)
     (= Y7 K2)
     (= X7 J2)
     (= W7 I2)
     (= V7 H2)
     (= O9 G5)
     (= V9 D6)
     (= U9 C6)
     (= T9 B6)
     (= S9 A6)
     (= R9 Z5)
     (= Q9 Y5)
     (= P9 H5)
     (= U7 Y1)
     (= T7 X1)
     (= V6 Z)
     (= W8 E2)
     (= V8 D2)
     (= U8 C2)
     (= T8 B2)
     (= S8 A2)
     (= R8 Z1)
     (= Q11 V5)
     (= P11 U5)
     (= O11 T5)
     (= N11 S5)
     (= M11 R5)
     (= L11 Q5)
     (= S10 P4)
     (= R10 O4)
     (= Q10 N4)
     (= P10 M4)
     (= O10 L4)
     (= N10 K4)
     (= X8 F2)
     (= T10 Q4)
     (= R11 W5)
     (= H7 D1)
     (= G7 C1)
     (= F7 B1)
     (= E7 A1)
     (= U6 Y)
     (= T6 X)
     (= S6 W)
     (= R6 V)
     (= Q6 U)
     (= P6 T)
     (= O6 S)
     (= N6 K)
     (= M6 J)
     (= L6 I)
     (= S7 W1)
     (= R7 V1)
     (= Q7 U1)
     (= P7 T1)
     (= O7 S1)
     (= N7 R1)
     (= M7 Q1)
     (= L7 H1)
     (= K7 G1)
     (= J7 F1)
     (= I7 E1)
     (= D9 T2)
     (= C9 S2)
     (= B9 R2)
     (= A9 Q2)
     (= Z8 P2)
     (= Y8 O2)
     (= B10 A3)
     (= A10 Z2)
     (= Z9 Y2)
     (= Y9 X2)
     (= G9 W2)
     (= F9 V2)
     (= E9 U2)
     (= Z10 W4)
     (= Y10 V4)
     (= X10 U4)
     (= W10 T4)
     (= V10 S4)
     (= U10 R4)
     (= M10 B4)
     (= L10 A4)
     (= K10 Z3)
     (= J10 Y3)
     (= I10 X3)
     (= H10 W3)
     (= G10 V3)
     (= F10 U3)
     (= E10 T3)
     (= D10 S3)
     (= C10 R3)
     (= W11 J6)
     (= V11 I6)
     (= U11 H6)
     (= T11 G6)
     (= S11 X5)
     (= K11 P5)
     (= J11 O5)
     (= I11 N5)
     (= H11 M5)
     (= G11 L5)
     (= F11 K5)
     (= E11 J5)
     (= D11 I5)
     (= C11 Z4)
     (= B11 Y4)
     (= A11 X4)
     (= X11 K6)
     (= J8 L3)
     (= 0 v_322)
     (= v_323 false))
      )
      (transition-6 v_322
              H12
              G12
              F12
              E12
              D12
              C12
              B12
              A12
              Z11
              Y11
              X11
              W11
              V11
              U11
              T11
              S11
              R11
              Q11
              P11
              O11
              N11
              M11
              L11
              K11
              J11
              I11
              H11
              G11
              F11
              E11
              D11
              C11
              B11
              A11
              Z10
              Y10
              X10
              W10
              V10
              U10
              T10
              S10
              R10
              Q10
              P10
              O10
              N10
              M10
              L10
              K10
              J10
              I10
              H10
              G10
              F10
              E10
              D10
              C10
              v_323
              X9
              W9
              V9
              U9
              T9
              S9
              R9
              Q9
              P9
              O9
              N9
              M9
              L9
              K9
              J9
              I9
              H9
              Q8
              P8
              O8
              N8
              M8
              L8
              K8
              J8
              I8
              H8
              G8
              F8
              E8
              D8
              C8
              B8
              A8
              Z7
              Y7
              X7
              W7
              V7
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              B10
              A10
              Z9
              Y9
              G9
              F9
              E9
              D9
              C9
              B9
              A9
              Z8
              Y8
              X8
              W8
              V8
              U8
              T8
              S8
              R8
              U7
              T7
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Bool) (M Bool) (N Bool) (O Bool) (P Bool) (Q Bool) (R Bool) (S Int) (T Int) (U Int) (V Int) (W Int) (X Int) (Y Int) (Z Int) (A1 Int) (B1 Int) (C1 Int) (D1 Int) (E1 Int) (F1 Int) (G1 Int) (H1 Int) (I1 Bool) (J1 Bool) (K1 Bool) (L1 Bool) (M1 Bool) (N1 Bool) (O1 Bool) (P1 Bool) (Q1 Int) (R1 Int) (S1 Int) (T1 Int) (U1 Int) (V1 Int) (W1 Int) (X1 Int) (Y1 Int) (Z1 Int) (A2 Int) (B2 Int) (C2 Int) (D2 Int) (E2 Int) (F2 Int) (G2 Bool) (H2 Bool) (I2 Bool) (J2 Bool) (K2 Bool) (L2 Bool) (M2 Bool) (N2 Bool) (O2 Int) (P2 Int) (Q2 Int) (R2 Int) (S2 Int) (T2 Int) (U2 Int) (V2 Int) (W2 Int) (X2 Int) (Y2 Int) (Z2 Int) (A3 Int) (B3 Int) (C3 Int) (D3 Int) (E3 Bool) (F3 Bool) (G3 Bool) (H3 Bool) (I3 Bool) (J3 Bool) (K3 Bool) (L3 Bool) (M3 Int) (N3 Int) (O3 Int) (P3 Int) (Q3 Int) (R3 Int) (S3 Int) (T3 Int) (U3 Int) (V3 Int) (W3 Int) (X3 Int) (Y3 Int) (Z3 Int) (A4 Int) (B4 Int) (C4 Bool) (D4 Bool) (E4 Bool) (F4 Bool) (G4 Bool) (H4 Bool) (I4 Bool) (J4 Bool) (K4 Int) (L4 Int) (M4 Int) (N4 Int) (O4 Int) (P4 Int) (Q4 Int) (R4 Int) (S4 Int) (T4 Int) (U4 Int) (V4 Int) (W4 Int) (X4 Int) (Y4 Int) (Z4 Int) (A5 Bool) (B5 Bool) (C5 Bool) (D5 Bool) (E5 Bool) (F5 Bool) (G5 Bool) (H5 Bool) (I5 Int) (J5 Int) (K5 Int) (L5 Int) (M5 Int) (N5 Int) (O5 Int) (P5 Int) (Q5 Int) (R5 Int) (S5 Int) (T5 Int) (U5 Int) (V5 Int) (W5 Int) (X5 Int) (Y5 Bool) (Z5 Bool) (A6 Bool) (B6 Bool) (C6 Bool) (D6 Bool) (E6 Bool) (F6 Bool) (G6 Int) (H6 Int) (I6 Int) (J6 Int) (K6 Int) (L6 Int) (M6 Int) (N6 Int) (O6 Int) (P6 Int) (Q6 Int) (R6 Int) (S6 Int) (T6 Int) (U6 Int) (V6 Int) (W6 Bool) (X6 Bool) (Y6 Bool) (Z6 Bool) (A7 Bool) (B7 Bool) (C7 Bool) (D7 Bool) (E7 Int) (F7 Int) (G7 Int) (H7 Int) (I7 Int) (J7 Int) (K7 Int) (L7 Int) (M7 Int) (N7 Int) (O7 Int) (P7 Int) (Q7 Int) (R7 Int) (S7 Int) (T7 Int) (U7 Int) (V7 Bool) (W7 Bool) (X7 Bool) (Y7 Bool) (Z7 Bool) (A8 Bool) (B8 Bool) (C8 Bool) (D8 Bool) (E8 Bool) (F8 Bool) (G8 Bool) (H8 Bool) (I8 Bool) (J8 Bool) (K8 Bool) (L8 Bool) (M8 Bool) (N8 Bool) (O8 Bool) (P8 Bool) (Q8 Bool) (R8 Int) (S8 Int) (T8 Int) (U8 Int) (V8 Int) (W8 Int) (X8 Int) (Y8 Int) (Z8 Int) (A9 Int) (B9 Int) (C9 Int) (D9 Int) (E9 Int) (F9 Int) (G9 Int) (H9 Bool) (I9 Bool) (J9 Bool) (K9 Bool) (L9 Bool) (M9 Bool) (N9 Bool) (O9 Bool) (P9 Bool) (Q9 Bool) (R9 Bool) (S9 Bool) (T9 Bool) (U9 Bool) (V9 Bool) (W9 Bool) (X9 Bool) (Y9 Bool) (Z9 Bool) (A10 Bool) (B10 Bool) (C10 Bool) (D10 Bool) (E10 Bool) (F10 Int) (G10 Int) (H10 Int) (I10 Int) (J10 Int) (K10 Int) (L10 Int) (M10 Int) (N10 Int) (O10 Int) (P10 Int) (Q10 Int) (R10 Int) (S10 Int) (T10 Int) (U10 Int) (V10 Int) (W10 Int) (X10 Int) (Y10 Int) (Z10 Int) (A11 Int) (B11 Int) (C11 Int) (D11 Int) (E11 Int) (F11 Int) (G11 Int) (H11 Int) (I11 Int) (J11 Int) (K11 Int) (L11 Int) (M11 Int) (N11 Int) (O11 Int) (P11 Int) (Q11 Int) (R11 Int) (S11 Int) (T11 Bool) (U11 Bool) (V11 Bool) (W11 Bool) (X11 Bool) (Y11 Bool) (Z11 Bool) (A12 Bool) (B12 Bool) (C12 Int) (D12 Int) (E12 Int) (F12 Int) (G12 Int) (H12 Int) (I12 Int) (J12 Int) (K12 Int) (L12 Int) (M12 Int) (N12 Int) (O12 Int) (P12 Int) (Q12 Int) (R12 Int) (S12 Int) (T12 Int) (U12 Int) (V12 Int) (W12 Int) (X12 Int) (Y12 Int) (Z12 Int) (A13 Int) (B13 Int) (C13 Int) (D13 Int) (E13 Int) (F13 Int) (G13 Int) (H13 Int) (I13 Int) (J13 Int) (K13 Int) (L13 Int) (M13 Int) (N13 Int) (O13 Int) (P13 Int) (Q13 Int) (R13 Int) (S13 Int) (T13 Int) (U13 Int) (V13 Int) (W13 Int) (X13 Int) (Y13 Int) (Z13 Int) (A14 Int) (B14 Int) (C14 Int) (D14 Int) (v_368 Int) (v_369 Bool) (v_370 Int) (v_371 Bool) ) 
    (=>
      (and
        (transition-8 v_368
              D14
              C14
              B14
              A14
              Z13
              Y13
              X13
              W13
              V13
              U13
              I7
              H7
              G7
              F7
              E7
              V6
              U6
              T6
              S6
              R6
              Q6
              P6
              O6
              N6
              M6
              L6
              K6
              J6
              I6
              H6
              G6
              X5
              W5
              V5
              U5
              T5
              S5
              R5
              Q5
              P5
              O5
              N5
              M5
              L5
              K5
              J5
              I5
              Z4
              Y4
              X4
              W4
              V4
              U4
              T4
              S4
              R4
              Q4
              P4
              O4
              N4
              M4
              L4
              K4
              B4
              A4
              Z3
              Y3
              X3
              W3
              V3
              U3
              T3
              S3
              R3
              v_369
              D7
              C7
              B7
              A7
              Z6
              Y6
              X6
              W6
              F6
              E6
              D6
              C6
              B6
              A6
              Z5
              Y5
              H5
              G5
              F5
              E5
              D5
              C5
              B5
              A5
              J4
              I4
              H4
              G4
              F4
              E4
              D4
              C4
              L3
              K3
              J3
              I3
              H3
              G3
              F3
              E3
              N2
              M2
              L2
              K2
              J2
              I2
              H2
              G2
              P1
              O1
              N1
              M1
              L1
              K1
              J1
              I1
              R
              Q
              P
              O
              N
              M
              L
              Q3
              P3
              O3
              N3
              M3
              D3
              C3
              B3
              A3
              Z2
              Y2
              X2
              W2
              V2
              U2
              T2
              S2
              R2
              Q2
              P2
              O2
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
        (and (= 0 v_368)
     (= v_369 false)
     (= L9 F4)
     (= K9 E4)
     (= J9 D4)
     (= I9 C4)
     (= H9 L3)
     (= O8 I3)
     (= N8 H3)
     (= M8 G3)
     (= L8 F3)
     (= K8 E3)
     (= J8 N2)
     (= A12 C7)
     (= Z11 B7)
     (= Y11 A7)
     (= X11 Z6)
     (= W11 Y6)
     (= V11 X6)
     (= U11 W6)
     (= T11 F6)
     (= E10 E6)
     (= D10 D6)
     (= C10 C6)
     (= B10 B6)
     (= A10 A6)
     (= Z9 Z5)
     (= Y9 Y5)
     (= X9 H5)
     (= I8 M2)
     (= H8 L2)
     (= G8 K2)
     (= F8 J2)
     (= E8 I2)
     (= D8 H2)
     (= C8 G2)
     (= B8 P1)
     (= W9 G5)
     (= A8 O1)
     (= B12 D7)
     (= P8 J3)
     (= N9 H4)
     (= Q8 K3)
     (= Z7 N1)
     (= Y7 M1)
     (= X7 L1)
     (= W7 K1)
     (= V7 J1)
     (= O9 I4)
     (= V9 F5)
     (= U9 E5)
     (= T9 D5)
     (= S9 C5)
     (= R9 B5)
     (= Q9 A5)
     (= P9 J4)
     (= W8 G1)
     (= V8 F1)
     (= U8 E1)
     (= T8 D1)
     (= S8 C1)
     (= R8 B1)
     (= U7 A1)
     (= T7 Z)
     (= Q11 Q4)
     (= P11 P4)
     (= O11 O4)
     (= N11 N4)
     (= M11 M4)
     (= L11 L4)
     (= S10 U2)
     (= R10 T2)
     (= Q10 S2)
     (= P10 R2)
     (= O10 Q2)
     (= N10 P2)
     (= M13 T6)
     (= L13 S6)
     (= K13 R6)
     (= J13 Q6)
     (= I13 P6)
     (= H13 O6)
     (= O12 N5)
     (= N12 M5)
     (= M12 L5)
     (= L12 K5)
     (= K12 J5)
     (= J12 I5)
     (= X8 H1)
     (= T10 V2)
     (= R11 R4)
     (= P12 O5)
     (= N13 U6)
     (= S7 Y)
     (= R7 X)
     (= Q7 W)
     (= P7 V)
     (= O7 U)
     (= N7 T)
     (= M7 S)
     (= L7 K)
     (= K7 J)
     (= J7 I)
     (= D9 V1)
     (= C9 U1)
     (= B9 T1)
     (= A9 S1)
     (= Z8 R1)
     (= Y8 Q1)
     (= G9 Y1)
     (= F9 X1)
     (= E9 W1)
     (= Z10 B3)
     (= Y10 A3)
     (= X10 Z2)
     (= W10 Y2)
     (= V10 X2)
     (= U10 W2)
     (= M10 O2)
     (= L10 F2)
     (= K10 E2)
     (= J10 D2)
     (= I10 C2)
     (= H10 B2)
     (= G10 A2)
     (= F10 Z1)
     (= S11 S4)
     (= K11 K4)
     (= J11 B4)
     (= I11 A4)
     (= H11 Z3)
     (= G11 Q3)
     (= F11 P3)
     (= E11 O3)
     (= D11 N3)
     (= C11 M3)
     (= B11 D3)
     (= A11 C3)
     (= V12 U5)
     (= U12 T5)
     (= T12 S5)
     (= S12 R5)
     (= R12 Q5)
     (= Q12 P5)
     (= I12 Z4)
     (= H12 Y4)
     (= G12 X4)
     (= F12 W4)
     (= E12 V4)
     (= D12 U4)
     (= C12 T4)
     (= S13 H7)
     (= R13 G7)
     (= Q13 F7)
     (= P13 E7)
     (= O13 V6)
     (= G13 N6)
     (= F13 M6)
     (= E13 L6)
     (= D13 K6)
     (= C13 J6)
     (= B13 I6)
     (= A13 H6)
     (= Z12 G6)
     (= Y12 X5)
     (= X12 W5)
     (= W12 V5)
     (= T13 I7)
     (= M9 G4)
     (= 0 v_370)
     (= v_371 false))
      )
      (transition-7 v_370
              D14
              C14
              B14
              A14
              Z13
              Y13
              X13
              W13
              V13
              U13
              T13
              S13
              R13
              Q13
              P13
              O13
              N13
              M13
              L13
              K13
              J13
              I13
              H13
              G13
              F13
              E13
              D13
              C13
              B13
              A13
              Z12
              Y12
              X12
              W12
              V12
              U12
              T12
              S12
              R12
              Q12
              P12
              O12
              N12
              M12
              L12
              K12
              J12
              I12
              H12
              G12
              F12
              E12
              D12
              C12
              S11
              R11
              Q11
              P11
              O11
              N11
              M11
              L11
              K11
              J11
              I11
              H11
              v_371
              B12
              A12
              Z11
              Y11
              X11
              W11
              V11
              U11
              T11
              E10
              D10
              C10
              B10
              A10
              Z9
              Y9
              X9
              W9
              V9
              U9
              T9
              S9
              R9
              Q9
              P9
              O9
              N9
              M9
              L9
              K9
              J9
              I9
              H9
              Q8
              P8
              O8
              N8
              M8
              L8
              K8
              J8
              I8
              H8
              G8
              F8
              E8
              D8
              C8
              B8
              A8
              Z7
              Y7
              X7
              W7
              V7
              G11
              F11
              E11
              D11
              C11
              B11
              A11
              Z10
              Y10
              X10
              W10
              V10
              U10
              T10
              S10
              R10
              Q10
              P10
              O10
              N10
              M10
              L10
              K10
              J10
              I10
              H10
              G10
              F10
              G9
              F9
              E9
              D9
              C9
              B9
              A9
              Z8
              Y8
              X8
              W8
              V8
              U8
              T8
              S8
              R8
              U7
              T7
              S7
              R7
              Q7
              P7
              O7
              N7
              M7
              L7
              K7
              J7)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (v_10 Int) (v_11 Bool) ) 
    (=>
      (and
        (transition-0 v_10 A B C D E F G H I J v_11)
        (and (= 0 v_10) (= v_11 false))
      )
      false
    )
  )
)

(check-sat)
(exit)
