; Example in which Eldarica previously incorrectly cloned arrays

(declare-datatypes ((k 0)) (((k (y Int)))))
(declare-datatypes ((e 0)) (((e (f (Array Int k))))))
(declare-datatypes ((g 0)) (((g (h (Array Int e))))))
(declare-fun j (g) Bool)

(assert (forall ((r g))
    (=>  (> (y (select (f (select (h r) 0)) 0)) 0) (j r))))

(assert (forall ((r g))
    (=  (> (y (select (f (select (h r) 0)) 0)) 0) (j r))))
    
(check-sat)