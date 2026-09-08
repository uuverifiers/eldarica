(set-logic HORN)


(declare-fun |INV1| ( Int Int Int Int Int Int ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (INV1 A B C D G H)
        (let ((a!1 (not (>= (+ (* 2 A) (* (- 1) B)) 1))))
  (and (= H (+ (- 2) F)) (= G (+ (- 1) E)) a!1 (>= (+ D (* (- 1) G)) 1) (= I J)))
      )
      (INV1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) (L Int) )
    (=>
      (and
        (INV1 A G H D I J)
        (and (= J (+ (- 2) F))
     (= I (+ (- 1) E))
     (= H (+ (- 1) C))
     (= G (+ (- 1) B))
     (>= (+ (* 2 A) (* (- 1) G)) 1)
     (>= (+ D (* (- 1) I)) 1)
     (= K L))
      )
      (INV1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (INV1 A G H D E F)
        (let ((a!1 (not (>= (+ D (* (- 1) E)) 1))))
  (and (= H (+ (- 1) C))
       (= G (+ (- 1) B))
       (>= (+ (* 2 A) (* (- 1) G)) 1)
       a!1
       (= I J)))
      )
      (INV1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and
        (and (= E 0) (= C 0) (= B 0) (= A D) (= F 0))
      )
      (INV1 A B C D E F)
    )
  )
)
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) )
    (=>
      (and
        (INV1 C D A E F B)
        (let ((a!1 (not (>= (+ (* 2 C) (* (- 1) D)) 1)))
      (a!2 (not (>= (+ E (* (- 1) F)) 1))))
  (and (not (= A B)) a!1 a!2 (= G H)))
      )
      false
    )
  )
)

(check-sat)
(exit)
