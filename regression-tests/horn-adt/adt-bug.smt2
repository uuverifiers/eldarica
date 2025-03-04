; Case in which Eldarica incorrectly returned unsat; the problem is sat

(set-logic HORN)

(declare-datatype f_type ((cons (b Int))))
(declare-datatype abi_type ((a)))

(declare-fun pred1 (Int abi_type f_type f_type) Bool)

(assert (forall ((l abi_type) (p f_type)) (pred1 0 l p p)))
(assert (forall ((m abi_type) (o Int) (aa f_type) (ab f_type))
  (=> (pred1 o m aa ab) 
      (or (exists ((var0 abi_type)) (not (= var0 a))) 
          (and (= ab aa) (= o 0)))))
)

(check-sat)