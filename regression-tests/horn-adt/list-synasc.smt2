(set-logic HORN)

(declare-datatype IList ( (Nil) (Cons (head Int) (tail IList)) ))

(declare-fun Concat (IList IList IList) Bool)

(assert (forall ((y IList))
           (Concat Nil y y)))

(assert (forall ((x IList)(y IList)(r IList)(i Int))
           (=> (Concat x y r) (Concat (Cons i x) y (Cons i r)) )))

(assert (forall ((x IList)(y IList)(r IList))
           (=> (and (not (= r Nil)) (Concat x y r)) (or (= (head r) (head x)) (= (head r) (head y)) ))))

(assert (forall ((x IList)(y IList)(r IList)(nx Int)(ny Int)(nr Int))
           (=> (and (Concat x y r) (= nx (_size x)) (= ny (_size y)) (= nr (_size r))) (= (+ nr 1) (+ nx ny)))))

(check-sat)
