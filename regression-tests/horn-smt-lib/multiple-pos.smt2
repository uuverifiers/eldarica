(set-logic HORN)

(declare-fun itp ( Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (and (= C 0) (= D 0) (= B 0) (= A 0))
      )
      (itp A B C D)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) ) 
    (=>
      (and
        (itp A B C D)
        (and (= G (+ C F)) (= H (+ D G)) (= F (+ B E)) (= E (+ 1 A)))
      )
      (itp E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) ) 
    (=>
      (and
        (itp A B C D)
        (not (>= D 0))
      )
      false
    )
  )
)

(check-sat)
(exit)
