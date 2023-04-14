(set-logic HORN)

(declare-fun inv ((Array Int Int) (Array Int Int) Int Int) Bool)

(assert (forall ((f (Array Int Int)) (g (Array Int Int)))
                (inv f g 0 0)))

(assert (forall ((f (Array Int Int)) (g (Array Int Int)) (x Int) (y Int))
                (=> (inv f g x y) (inv f g (select f x) (select g y)))))

(assert (forall ((f (Array Int Int)) (g (Array Int Int)) (x Int) (y Int))
                (=> (inv f g x y) (= x y))))

(check-sat)
