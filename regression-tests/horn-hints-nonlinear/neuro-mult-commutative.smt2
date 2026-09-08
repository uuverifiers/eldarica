(set-logic HORN)


(declare-fun |main@mult.exit6.split| ( ) Bool)
(declare-fun |main@entry| ( ) Bool)
(declare-fun |main@tailrecurse.i| ( Int Int Int Int ) Bool)
(declare-fun |main@tailrecurse.outer.i3| ( Int Int Int Int Int ) Bool)
(declare-fun |main@tailrecurse.outer.i| ( Int Int Int Int ) Bool)
(declare-fun |main@tailrecurse.i5| ( Int Int Int Int Int ) Bool)

(assert
  (forall ( (CHC_COMP_UNUSED Bool) )
    (=>
      (and
        true
      )
      main@entry
    )
  )
)
(assert
  (forall ( (A Bool) (B Bool) (C Int) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        main@entry
        (let ((a!1 (= B (or (not (<= H 46340)) (not (>= H 0)))))
      (a!2 (= A (or (not (<= G 46340)) (not (>= G 0))))))
  (and a!1
       (or (not E) (not D) (= C 0))
       (or (not E) (not D) (= F H))
       (or (not E) (not D) (= I C))
       (or (not E) (not D) (= J F))
       (or (not D) (and E D))
       (not A)
       (not B)
       (= D true)
       a!2))
      )
      (main@tailrecurse.outer.i G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Int) (L Int) (M Bool) (N Bool) (O Int) (P Int) (Q Int) (R Int) (S Int) )
    (=>
      (and
        (main@tailrecurse.i P Q I C)
        (and (not (= (<= 0 C) B))
     (or (not F) (not D) (= E C))
     (or (not F) (not D) (= H E))
     (or (not F) (not D) (not B))
     (or (not N) (not G) (not F))
     (or (not N) (not M) (= L J))
     (or (not N) (not M) (= O K))
     (or (not N) (not M) (= R L))
     (or (not N) (not M) (= S O))
     (or (not F) (= G (= H 0)))
     (or (not F) (and F D))
     (or (not M) (and N M))
     (or (not N) (= J (+ I P)))
     (or (not N) (= K (+ (- 1) H)))
     (or (not N) (and N F))
     (= M true)
     (= A (* (- 1) C)))
      )
      (main@tailrecurse.outer.i P Q R S)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) )
    (=>
      (and
        (main@tailrecurse.outer.i E F G A)
        (and (or (not C) (not B) (= H D))
     (or (not B) (and C B))
     (= B true)
     (or (not C) (not B) (= D A)))
      )
      (main@tailrecurse.i E F G H)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (main@tailrecurse.i G H I A)
        (and (not (= (<= 0 A) B))
     (or (not E) (not D) (= F C))
     (or (not E) (not D) (= J F))
     (or (not E) (not D) B)
     (or (not D) (and E D))
     (= D true)
     (= C (* (- 1) A)))
      )
      (main@tailrecurse.i G H I J)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) (F Int) (G Bool) (H Int) (I Bool) (J Int) (K Int) (L Bool) (M Bool) (N Int) (O Int) (P Int) (Q Int) (R Int) (S Int) )
    (=>
      (and
        (main@tailrecurse.i P Q H C)
        (and (not (= (<= 0 C) B))
     (or (not D) (= F E) (not I))
     (or (= E C) (not D) (not I))
     (or (not B) (not D) (not I))
     (or (not M) (not I) (= J H))
     (or (not M) (not I) (= O J))
     (or (not M) (not L) (= N P))
     (or (not M) (not L) (= K 0))
     (or (not M) (not L) (= R K))
     (or (not M) (not L) (= S N))
     (or (not M) G (not I))
     (or (not I) (= G (= F 0)))
     (or (not I) (and D I))
     (or (not L) (and M L))
     (or (not M) (and M I))
     (= L true)
     (= A (* (- 1) C)))
      )
      (main@tailrecurse.outer.i3 O P Q R S)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) (F Bool) (G Bool) (H Int) (I Int) (J Int) (K Int) (L Int) (M Bool) (N Bool) (O Int) (P Int) (Q Int) (R Int) (S Int) (T Int) )
    (=>
      (and
        (main@tailrecurse.i5 P Q R I C)
        (and (not (= (<= 0 C) B))
     (or (not F) (not D) (= E C))
     (or (not F) (not D) (= H E))
     (or (not F) (not D) (not B))
     (or (not N) (not M) (= O K))
     (or (not N) (not M) (= L J))
     (or (not N) (not M) (= S L))
     (or (not N) (not M) (= T O))
     (or (not N) (not G) (not F))
     (or (not F) (= G (= H 0)))
     (or (not F) (and F D))
     (or (not M) (and N M))
     (or (not N) (= J (+ I R)))
     (or (not N) (= K (+ (- 1) H)))
     (or (not N) (and N F))
     (= M true)
     (= A (* (- 1) C)))
      )
      (main@tailrecurse.outer.i3 P Q R S T)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Bool) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) )
    (=>
      (and
        (main@tailrecurse.outer.i3 E F G H A)
        (and (or (not C) (not B) (= I D))
     (or (not B) (and C B))
     (= B true)
     (or (not C) (not B) (= D A)))
      )
      (main@tailrecurse.i5 E F G H I)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Bool) (F Int) (G Int) (H Int) (I Int) (J Int) (K Int) )
    (=>
      (and
        (main@tailrecurse.i5 G H I J A)
        (and (not (= (<= 0 A) B))
     (or (not E) (not D) (= F C))
     (or (not E) (not D) (= K F))
     (or (not E) B (not D))
     (or (not D) (and E D))
     (= D true)
     (= C (* (- 1) A)))
      )
      (main@tailrecurse.i5 G H I J K)
    )
  )
)
(assert
  (forall ( (A Int) (B Bool) (C Int) (D Bool) (E Int) (F Int) (G Bool) (H Int) (I Bool) (J Int) (K Int) (L Int) (M Int) (N Bool) (O Bool) (P Int) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) )
    (=>
      (and
        (main@tailrecurse.i5 K M P H C)
        (let ((a!1 (or (not T) (not (= (= K L) O))))
      (a!2 (or (not T) (not (= (<= P 0) Q))))
      (a!3 (or (not T) (not (= (<= M 0) N)))))
  (and (not (= (<= 0 C) B))
       (or (not I) (= J H) (not T))
       (or (not I) (= L J) (not T))
       (or (not I) G (not T))
       (or (not I) (not D) (= F E))
       (or (not I) (not D) (= E C))
       (or (not I) (not D) (not B))
       a!1
       a!2
       a!3
       (or (not T) (= R (and O N)))
       (or (not T) (= S (and R Q)))
       (or (not T) (and I T))
       (or (not T) S)
       (or (not U) (and U T))
       (or (not I) (= G (= F 0)))
       (or (not I) (and I D))
       (= U true)
       (= A (* (- 1) C))))
      )
      main@mult.exit6.split
    )
  )
)
(assert
  (forall ( (CHC_COMP_UNUSED Bool) )
    (=>
      (and
        main@mult.exit6.split
        true
      )
      false
    )
  )
)

(check-sat)
(exit)
