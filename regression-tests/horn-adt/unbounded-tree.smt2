(declare-datatypes ((Tree 0) (TreeList 0)) (
   ((node (data Int) (children TreeList)))
   ((nil) (cons (head Tree) (tail TreeList)))))
   
(assert (forall ((h Tree)(t TreeList)(i1 Int)(i2 Int)(i3 Int)) 
  (=> (and (= (_size (cons h t)) i1) (= (_size h) i2) (= (_size t) i3) ) (>= i1 (+ i2 i3)))))

(check-sat)
