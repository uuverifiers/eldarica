(set-info :status unknown)
(set-logic HORN)

(declare-fun p0 (Int Int Int (Array Int Int)) Bool)
(declare-fun p1 (Int Int Int (Array Int Int)) Bool)
(declare-fun p2 (Int Int Int (Array Int Int)) Bool)
(declare-fun p3 (Int Int Int (Array Int Int)) Bool)

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (>= len 0)
             (p0 1 cnt len a))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (p0 1 cnt len a)
             (p1 0 0 len a))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (and (p1 c cnt len a) (< cnt (- len 1)))
             (p2 c cnt len a))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (and (p1 c cnt len a) (>= cnt (- len 1)))
             (p0 c cnt len a))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (and (p2 c cnt len a) (<= (select a cnt) (select a (+ cnt 1))))
             (p1 c (+ cnt 1) len a))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (and (p2 c cnt len a) (> (select a cnt) (select a (+ cnt 1))))
             (p1 1 (+ cnt 1) len (store (store a cnt (select a (+ cnt 1)))
                                        (+ cnt 1) (select a cnt))))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (p0 0 cnt len a)
             (p3 0 cnt len a))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (p3 c cnt len a) (> len 0)
             (>= (select a 0) 0))))

(check-sat)
