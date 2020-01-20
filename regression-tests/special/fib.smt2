;Generated with /home/mattze/unison/sync/Documents/Research/Improve/Horn/sml/horn ../experiments/arrays/fib
;On Mon Oct 27 22:26:50 2014
;By mattze

(set-logic HORN)
(declare-fun INV1 
 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)
(assert 
 (forall 
  (
   (i$1_1 Int) 
   (a$1_1 Int) 
   (b$1_1 Int) 
   (t$1_1 Int) 
   ($heap$1_1 
    (Array Int Int)) 
   (n$1_1 Int) 
   (x$1_1 Int) 
   (i$2_1 Int) 
   (r$2_1 Int) 
   ($heap$2_1 
    (Array Int Int)) 
   (n$2_1 Int) 
   (a$2_1 Int)) 
  (let 
   (
    ($heap$1_1 $heap$2_1)
    (n$1_1 n$2_1)
    (x$1_1 a$2_1)) 
   (=> 
    (and 
     (>= n$2_1 0)) 
    (let 
     (
      (i$1_2 2)) 
     (let 
      (
       (a$1_2 1)) 
      (let 
       (
        (b$1_2 1)) 
       (let 
        (
         (i$2_2 2)) 
        (let 
         (
          ($heap$2_2 
           (store $heap$2_1 
            (+ a$2_1 0) 1))) 
         (let 
          (
           ($heap$2_3 
            (store $heap$2_2 
             (+ a$2_1 1) 1))) 
          (and 
           (forall 
            (
             ($i2 Int) 
             ($i1 Int)) 
            (INV1 $i2 
             (select $heap$1_1 $i2) n$1_1 x$1_1 i$1_2 a$1_2 b$1_2 t$1_1 $i1 
             (select $heap$2_3 $i1) n$2_1 a$2_1 i$2_2 r$2_1))
           (forall 
            (
             ($heap$1_2 
              (Array Int Int)) 
             (n$1_2 Int) 
             (x$1_2 Int) 
             (i$1_3 Int) 
             (a$1_3 Int) 
             (b$1_3 Int) 
             (t$1_2 Int) 
             ($heap$2_4 
              (Array Int Int)) 
             (n$2_2 Int) 
             (a$2_2 Int) 
             (i$2_3 Int) 
             (r$2_2 Int)) 
            (and 
             (=> 
              (and 
               (forall 
                (
                 ($i2 Int) 
                 ($i1 Int)) 
                (INV1 $i2 
                 (select $heap$1_2 $i2) n$1_2 x$1_2 i$1_3 a$1_3 b$1_3 t$1_2 $i1 
                 (select $heap$2_4 $i1) n$2_2 a$2_2 i$2_3 r$2_2)) 
               (< i$2_3 n$2_2) 
               (< i$1_3 n$1_2)) 
              (let 
               (
                ($heap$2_5 
                 (store $heap$2_4 
                  (+ a$2_2 i$2_3) 
                  (+ 
                   (select $heap$2_4 
                    (+ a$2_2 
                     (- i$2_3 1))) 
                   (select $heap$2_4 
                    (+ a$2_2 
                     (- i$2_3 2))))))) 
               (let 
                (
                 (i$2_4 
                  (+ i$2_3 1))) 
                (let 
                 (
                  (t$1_3 a$1_3)) 
                 (let 
                  (
                   (a$1_4 b$1_3)) 
                  (let 
                   (
                    (b$1_4 
                     (+ a$1_4 t$1_3))) 
                   (let 
                    (
                     (i$1_4 
                      (+ i$1_3 1))) 
                    (forall 
                     (
                      ($i2 Int) 
                      ($i1 Int)) 
                     (INV1 $i2 
                      (select $heap$1_2 $i2) n$1_2 x$1_2 i$1_4 a$1_4 b$1_4 t$1_3 $i1 
                      (select $heap$2_5 $i1) n$2_2 a$2_2 i$2_4 r$2_2))))))))) 
             (=> 
              (and 
               (forall 
                (
                 ($i2 Int) 
                 ($i1 Int)) 
                (INV1 $i2 
                 (select $heap$1_2 $i2) n$1_2 x$1_2 i$1_3 a$1_3 b$1_3 t$1_2 $i1 
                 (select $heap$2_4 $i1) n$2_2 a$2_2 i$2_3 r$2_2)) 
               (< i$2_3 n$2_2) 
               (not 
                (< i$1_3 n$1_2))) 
              (let 
               (
                ($heap$2_5 
                 (store $heap$2_4 
                  (+ a$2_2 i$2_3) 
                  (+ 
                   (select $heap$2_4 
                    (+ a$2_2 
                     (- i$2_3 1))) 
                   (select $heap$2_4 
                    (+ a$2_2 
                     (- i$2_3 2))))))) 
               (let 
                (
                 (i$2_4 
                  (+ i$2_3 1))) 
                (forall 
                 (
                  ($i2 Int) 
                  ($i1 Int)) 
                 (INV1 $i2 
                  (select $heap$1_2 $i2) n$1_2 x$1_2 i$1_3 a$1_3 b$1_3 t$1_2 $i1 
                  (select $heap$2_5 $i1) n$2_2 a$2_2 i$2_4 r$2_2))))) 
             (=> 
              (and 
               (forall 
                (
                 ($i2 Int) 
                 ($i1 Int)) 
                (INV1 $i2 
                 (select $heap$1_2 $i2) n$1_2 x$1_2 i$1_3 a$1_3 b$1_3 t$1_2 $i1 
                 (select $heap$2_4 $i1) n$2_2 a$2_2 i$2_3 r$2_2)) 
               (not 
                (< i$2_3 n$2_2)) 
               (< i$1_3 n$1_2)) 
              (let 
               (
                (t$1_3 a$1_3)) 
               (let 
                (
                 (a$1_4 b$1_3)) 
                (let 
                 (
                  (b$1_4 
                   (+ a$1_4 t$1_3))) 
                 (let 
                  (
                   (i$1_4 
                    (+ i$1_3 1))) 
                  (forall 
                   (
                    ($i2 Int) 
                    ($i1 Int)) 
                   (INV1 $i2 
                    (select $heap$1_2 $i2) n$1_2 x$1_2 i$1_4 a$1_4 b$1_4 t$1_3 $i1 
                    (select $heap$2_4 $i1) n$2_2 a$2_2 i$2_3 r$2_2))))))) 
             (=> 
              (and 
               (forall 
                (
                 ($i2 Int) 
                 ($i1 Int)) 
                (INV1 $i2 
                 (select $heap$1_2 $i2) n$1_2 x$1_2 i$1_3 a$1_3 b$1_3 t$1_2 $i1 
                 (select $heap$2_4 $i1) n$2_2 a$2_2 i$2_3 r$2_2)) 
               (not 
                (< i$2_3 n$2_2)) 
               (not 
                (< i$1_3 n$1_2))) 
              (let 
               (
                (r$2_3 
                 (select $heap$2_4 
                  (+ a$2_2 
                   (- i$2_3 1))))) 
               (and 
                (= r$2_3 b$1_3)))))))))))))))))
(check-sat) 
(get-model) 
(exit)
