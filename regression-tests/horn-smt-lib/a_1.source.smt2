; Problem that could not be verified before interval propagation became a bit more powerful

; Manual translation to smt
; This is the 1-program-problem of proving a contract correct - not yet the relational one.

; Contract pre: 1=1, post: \result >= 0

(declare-fun INV (Int Int Int) Bool)

;(define-fun INV ((n Int)(i Int)(s Int)) Bool
;  (and (>= i 2) (>= s 0)))

(assert 
 (forall ((n Int))
  (INV n 2 0)))

(assert
 (forall ((sum Int)(i Int)(n Int))
  (=> 
   (and (INV n i sum) (<= i n)) 
   (INV n (+ i 1) (+ sum i)))))

(assert
 (forall ((sum Int)(i Int)(n Int))
  (=> 
   (and (INV n i sum) (not (<= i n))) 
   (>= sum 0))))
   

(check-sat)



