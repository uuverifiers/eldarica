(set-info :status unknown)
(set-logic HORN)

(declare-fun sp0 (Int Int Int Int Int Int Int) Bool)
(declare-fun sp1 (Int Int Int Int Int Int Int) Bool)
(declare-fun sp2 (Int Int Int Int Int Int Int) Bool)
(declare-fun sp3 (Int Int Int Int Int Int Int) Bool)

(define-fun p0 ((c Int) (cnt Int) (len Int) (a (Array Int Int))) Bool
            (forall ((i Int) (j Int))
               (sp0 c cnt len i (select a i) j (select a j))))
(define-fun p1 ((c Int) (cnt Int) (len Int) (a (Array Int Int))) Bool
            (forall ((i Int) (j Int))
               (sp1 c cnt len i (select a i) j (select a j))))
(define-fun p2 ((c Int) (cnt Int) (len Int) (a (Array Int Int))) Bool
            (forall ((i Int) (j Int))
               (sp2 c cnt len i (select a i) j (select a j))))
(define-fun p3 ((c Int) (cnt Int) (len Int) (a (Array Int Int))) Bool
            (forall ((i Int) (j Int))
               (sp3 c cnt len i (select a i) j (select a j))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (and (>= len 0) (forall ((i Int)) (>= (select a i) 0)))
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
         (=> (and (sp2 c cnt len cnt (select a cnt) (+ cnt 1) (select a (+ cnt 1))) ; (p2 c cnt len a)
                  (<= (select a cnt) (select a (+ cnt 1))))
             (p1 c (+ cnt 1) len a))))

(assert (forall ((a (Array Int Int)) (b (Array Int Int)) (c Int) (cnt Int) (len Int) (i Int) (j Int))
         (=> (and (= b (store (store a cnt (select a (+ cnt 1)))
                                       (+ cnt 1) (select a cnt)))
                  (sp2 c cnt len i (select a i) j (select a j)) ; (p2 c cnt len a)
                  (> (select a cnt) (select a (+ cnt 1))))
             (sp1 1 (+ cnt 1) len b i (select b i) j (select b j)))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (p0 0 cnt len a)
             (p3 0 cnt len a))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int) (n Int))
         (=> (and (p3 c cnt len a) (>= n 0) (< n (- len 1)))
             (<= (select a n) (select a (+ n 1))))))

(check-sat)
