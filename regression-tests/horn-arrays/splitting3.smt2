(set-logic HORN)

(declare-fun inv ((Array Int Int) (Array Int Int) Int) Bool)

(assert (forall ((f (Array Int Int)) (g (Array Int Int)))
                (inv ((as const (Array Int Int)) 10)
                     ((as const (Array Int Int)) 11) 0)))

(assert (forall ((f (Array Int Int)) (g (Array Int Int)) (x Int))
                (=> (inv f g x) (inv (store f x 1) (store g x 2) (+ x 1)))))

(assert (forall ((f (Array Int Int)) (g (Array Int Int)) (x Int) (i Int))
                (=> (inv f g x) (> (select g i) 0))))

(check-sat)
