; Problem that could not be verified before interval propagation became a bit more powerful

; Manual translation to smt
; This is the 1-program-problem of proving a contract correct - not yet the relational one.

; Contract pre: 1=1, post: \result >= 0

(declare-fun INV ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)

;(define-fun INV ((n Int)(i Int)(s Int)) Bool
;  (and (>= i 2) (>= s 0)))

(assert 
 (forall ((n (_ BitVec 32)))
  (INV n (_ bv2 32) (_ bv0 32))))

(assert
 (forall ((sum (_ BitVec 32))(i (_ BitVec 32))(n (_ BitVec 32)))
  (=> 
   (and (INV n i sum) (bvsle i n)) 
   (INV n (bvadd i (_ bv1 32)) (bvadd sum i)))))

(assert
 (forall ((sum (_ BitVec 32))(i (_ BitVec 32))(n (_ BitVec 32)))
  (=> 
   (and (INV n i sum) (not (bvsle i n))) 
   (bvsge sum (_ bv0 32)))))
   

(check-sat)



