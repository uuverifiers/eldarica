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
  (forall ((I Int) (C Int) (N Int) (A (Array Int Int)) (Q Int))
    (=> (and (not (< I N)) (> N 0)
             (forall ((Q Int)) (inv1 I C N Q (select A Q))))
        (= (select A 0) C)
    )
  )
)

(check-sat)
