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
         (=> (and (p2 c cnt len a)
                  (<= (select a cnt) (select a (+ cnt 1))))
             (p1 c (+ cnt 1) len a))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (and (p2 c cnt len a)
                  (> (select a cnt) (select a (+ cnt 1))))
             (p1 1 (+ cnt 1) len (store (store a cnt (select a (+ cnt 1)))
                                        (+ cnt 1) (select a cnt))))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (p0 0 cnt len a)
             (p3 0 cnt len a))))

(assert (forall ((a (Array Int Int)) (c Int) (cnt Int) (len Int))
         (=> (and (p3 c cnt len a) (>= len 2))
             (<= (select a 0) (select a 1)))))

(check-sat)
