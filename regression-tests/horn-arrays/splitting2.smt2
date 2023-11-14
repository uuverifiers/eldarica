(set-logic HORN)

(declare-fun inv ((Array Int Int) (Array Int Int) Int) Bool)

(assert (forall ((f (Array Int Int)) (g (Array Int Int)))
                (inv f g 0)))

(assert (forall ((f (Array Int Int)) (g (Array Int Int)) (x Int))
                (=> (inv f g x) (inv (store f x 1) (store g x 2) (+ x 1)))))

(assert (forall ((f (Array Int Int)) (g (Array Int Int)) (x Int))
                (=> (inv f g x) (or (<= x 0) (> (select g 0) (select f 0))))))

(check-sat)
