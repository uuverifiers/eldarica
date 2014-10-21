;/*
; * Initializes all elements of a to a specified constant c.
; */
;void init(int* a, int c, int size)
;{
;  int i;
;  for(i=0; i<size; i++) 
;  {
;        a[i] = c;
;  }
;
;  for(i=0; i<size; i++)
;  {
;        static_assert(a[i] == c);
;  }
;}



; none
(set-info :status unknown)
(set-logic HORN)
(declare-fun inv1 (Int Int Int Int Int) Bool)
(declare-fun inv2 (Int Int Int Int Int) Bool)

(assert
  (forall ((I Int) (A (Array Int Int)) (Q Int) (C Int) (N Int) )
    (=> (= I 0) 
        (inv1 I C N Q (select A Q))
    )
  )
)

(assert
  (forall ((A1 (Array Int Int)) (A (Array Int Int)) (I Int) (C Int) (I1 Int) (N Int) )
    (=> (and (= A1 (store A I C)) (= I1 (+ 1 I)) (< I N)
             (forall ((Q Int)) (inv1 I C N Q (select A Q))))
        (forall ((Q Int)) (inv1 I1 C N Q (select A1 Q)))
    )
  )
)

(assert
  (forall ((I1 Int) (I Int) (C Int) (N Int) (A (Array Int Int)) )
    (=> (and (= I1 0) (not (< I N))
             (forall ((Q Int)) (inv1 I C N Q (select A Q))))
        (forall ((Q Int)) (inv2 I1 C N Q (select A Q)))
    )
  )
)

(assert
  (forall ((I1 Int) (I Int) (C Int) (N Int) (A (Array Int Int)) )
    (=> (and (= I1 (+ 1 I)) (< I N)
             (forall ((Q Int)) (inv2 I C N Q (select A Q))))
        (forall ((Q Int)) (inv2 I1 C N Q (select A Q)))
    )
  )
)

(assert
  (forall ((A (Array Int Int)) (I Int) (C Int) (N Int) )
    (=> (and (< I N)
             (forall ((Q Int)) (inv2 I C N Q (select A Q))))
        (= (select A I) C)
    )
  )
)


(check-sat)
