(set-logic HORN)


(declare-fun |inv_main26| ( Int Int Int ) Bool)
(declare-fun |inv_main13| ( Int Int Int Int ) Bool)
(declare-fun |inv_main3| ( Int ) Bool)
(declare-fun |inv_main22| ( Int Int Int Int Int ) Bool)
(declare-fun |inv_main8| ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) )
    (=>
      (and
        true
      )
      (inv_main3 A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) )
    (=>
      (and
        (inv_main22 D F G C E)
        (and (= B (+ C G)) (<= 1 E) (= A (+ (- 1) E)))
      )
      (inv_main22 D F G B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and
        (inv_main8 D C F E)
        (and (= B (+ F C)) (<= 1 E) (= A (+ (- 1) E)))
      )
      (inv_main8 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (v_4 Int) (v_5 Int) )
    (=>
      (and
        (inv_main8 B A D C)
        (and (not (<= 1 C)) (= 0 v_4) (= v_5 A))
      )
      (inv_main13 B A v_4 v_5)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and
        (inv_main13 D C F E)
        (and (= B (+ F C)) (<= 1 E) (= A (+ (- 1) E)))
      )
      (inv_main13 D C B A)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) )
    (=>
      (and
        (inv_main22 B D E A C)
        (not (<= 1 C))
      )
      (inv_main26 B D A)
    )
  )
)
(assert
  (forall ( (A Int) (v_1 Int) (v_2 Int) (v_3 Int) )
    (=>
      (and
        (inv_main3 A)
        (and (= v_1 A) (= 0 v_2) (= v_3 A))
      )
      (inv_main8 A v_1 v_2 v_3)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (v_4 Int) (v_5 Int) (v_6 Int) )
    (=>
      (and
        (inv_main13 B A D C)
        (and (not (<= 1 C)) (= v_4 B) (= 0 v_5) (= v_6 B))
      )
      (inv_main22 B D v_4 v_5 v_6)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) )
    (=>
      (and
        (inv_main26 A C B)
        (not (= C B))
      )
      false
    )
  )
)

(check-sat)
(exit)
