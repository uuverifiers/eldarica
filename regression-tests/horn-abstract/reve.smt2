
(set-logic HORN)
(declare-fun INV4 
 (Int Int Int Int) Bool) 
(declare-fun INV3 
 (Int Int Int Int) Bool) 
(declare-fun INV2 
 (Int Int Int Int Int Int Int Int) Bool) 
(declare-fun INV1 
 (Int Int Int Int Int Int Int Int) Bool)
(assert 
 (forall 
  (
   (n1_1 Int) 
   (i1_1 Int) 
   (j1_1 Int) 
   (x1_1 Int) 
   (n2_1 Int) 
   (i2_1 Int) 
   (j2_1 Int) 
   (x2_1 Int)) 
  (=> 
   (and 
    (and 
     (>= n2_1 0)) 
    (and 
     (= n1_1 n2_1))) 
   (let 
    (
     (i1_2 0)) 
    (let 
     (
      (j1_2 0)) 
     (let 
      (
       (x1_2 0)) 
      (let 
       (
        (i2_2 0)) 
       (let 
        (
         (j2_2 0)) 
        (let 
         (
          (x2_2 0)) 
         (and 
          (INV1 n1_1 i1_2 j1_2 x1_2 n2_1 i2_2 j2_2 x2_2)
          (forall 
           (
            (n1_2 Int) 
            (i1_3 Int) 
            (j1_3 Int) 
            (x1_3 Int) 
            (n2_2 Int) 
            (i2_3 Int) 
            (j2_3 Int) 
            (x2_3 Int)) 
           (and 
            (=> 
             (and 
              (INV1 n1_2 i1_3 j1_3 x1_3 n2_2 i2_3 j2_3 x2_3) 
              (< i2_3 n2_2) 
              (< i1_3 n1_2)) 
             (let 
              (
               (j2_4 0)) 
              (let 
               (
                (j1_4 0)) 
               (and 
                (INV2 n1_2 i1_3 j1_4 x1_3 n2_2 i2_3 j2_4 x2_3)
                (forall 
                 (
                  (n1_3 Int) 
                  (i1_4 Int) 
                  (j1_5 Int) 
                  (x1_4 Int) 
                  (n2_3 Int) 
                  (i2_4 Int) 
                  (j2_5 Int) 
                  (x2_4 Int)) 
                 (and 
                  (=> 
                   (and 
                    (INV2 n1_3 i1_4 j1_5 x1_4 n2_3 i2_4 j2_5 x2_4) 
                    (< j1_5 n1_3) 
                    (< j2_5 n2_3)) 
                   (and 
                    (=> 
                     (= i1_4 1) 
                     (let 
                      (
                       (x1_5 
                        (+ x1_4 1))) 
                      (let 
                       (
                        (j1_6 
                         (+ j1_5 1))) 
                       (and 
                        (=> 
                         (= i2_4 1) 
                         (let 
                          (
                           (x2_5 
                            (+ x2_4 1))) 
                          (let 
                           (
                            (j2_6 
                             (+ j2_5 1))) 
                           (INV2 n1_3 i1_4 j1_6 x1_5 n2_3 i2_4 j2_6 x2_5)))) 
                        (=> 
                         (not 
                          (= i2_4 1)) 
                         (let 
                          (
                           (x2_5 
                            (+ x2_4 1))) 
                          (let 
                           (
                            (x2_6 
                             (+ x2_5 1))) 
                           (let 
                            (
                             (j2_6 
                              (+ j2_5 1))) 
                            (INV2 n1_3 i1_4 j1_6 x1_5 n2_3 i2_4 j2_6 x2_6))))))))) 
                    (=> 
                     (not 
                      (= i1_4 1)) 
                     (let 
                      (
                       (x1_5 
                        (+ x1_4 1))) 
                      (let 
                       (
                        (x1_6 
                         (+ x1_5 1))) 
                       (let 
                        (
                         (j1_6 
                          (+ j1_5 1))) 
                        (and 
                         (=> 
                          (= i2_4 1) 
                          (let 
                           (
                            (x2_5 
                             (+ x2_4 1))) 
                           (let 
                            (
                             (j2_6 
                              (+ j2_5 1))) 
                            (INV2 n1_3 i1_4 j1_6 x1_6 n2_3 i2_4 j2_6 x2_5)))) 
                         (=> 
                          (not 
                           (= i2_4 1)) 
                          (let 
                           (
                            (x2_5 
                             (+ x2_4 1))) 
                           (let 
                            (
                             (x2_6 
                              (+ x2_5 1))) 
                            (let 
                             (
                              (j2_6 
                               (+ j2_5 1))) 
                             (INV2 n1_3 i1_4 j1_6 x1_6 n2_3 i2_4 j2_6 x2_6)))))))))))) 
                  (=> 
                   (and 
                    (INV2 n1_3 i1_4 j1_5 x1_4 n2_3 i2_4 j2_5 x2_4) 
                    (< j1_5 n1_3) 
                    (not 
                     (< j2_5 n2_3))) 
                   (and 
                    (=> 
                     (= i1_4 1) 
                     (let 
                      (
                       (x1_5 
                        (+ x1_4 1))) 
                      (let 
                       (
                        (j1_6 
                         (+ j1_5 1))) 
                       (INV2 n1_3 i1_4 j1_6 x1_5 n2_3 i2_4 j2_5 x2_4)))) 
                    (=> 
                     (not 
                      (= i1_4 1)) 
                     (let 
                      (
                       (x1_5 
                        (+ x1_4 1))) 
                      (let 
                       (
                        (x1_6 
                         (+ x1_5 1))) 
                       (let 
                        (
                         (j1_6 
                          (+ j1_5 1))) 
                        (INV2 n1_3 i1_4 j1_6 x1_6 n2_3 i2_4 j2_5 x2_4))))))) 
                  (=> 
                   (and 
                    (INV2 n1_3 i1_4 j1_5 x1_4 n2_3 i2_4 j2_5 x2_4) 
                    (not 
                     (< j1_5 n1_3)) 
                    (< j2_5 n2_3)) 
                   (and 
                    (=> 
                     (= i2_4 1) 
                     (let 
                      (
                       (x2_5 
                        (+ x2_4 1))) 
                      (let 
                       (
                        (j2_6 
                         (+ j2_5 1))) 
                       (INV2 n1_3 i1_4 j1_5 x1_4 n2_3 i2_4 j2_6 x2_5)))) 
                    (=> 
                     (not 
                      (= i2_4 1)) 
                     (let 
                      (
                       (x2_5 
                        (+ x2_4 1))) 
                      (let 
                       (
                        (x2_6 
                         (+ x2_5 1))) 
                       (let 
                        (
                         (j2_6 
                          (+ j2_5 1))) 
                        (INV2 n1_3 i1_4 j1_5 x1_4 n2_3 i2_4 j2_6 x2_6))))))) 
                  (=> 
                   (and 
                    (INV2 n1_3 i1_4 j1_5 x1_4 n2_3 i2_4 j2_5 x2_4) 
                    (not 
                     (< j1_5 n1_3)) 
                    (not 
                     (< j2_5 n2_3))) 
                   (let 
                    (
                     (i1_5 
                      (+ i1_4 1))) 
                    (let 
                     (
                      (i2_5 
                       (+ i2_4 1))) 
                     (INV1 n1_3 i1_5 j1_5 x1_4 n2_3 i2_5 j2_5 x2_4)))))))))) 
            (=> 
             (and 
              (INV1 n1_2 i1_3 j1_3 x1_3 n2_2 i2_3 j2_3 x2_3) 
              (< i2_3 n2_2) 
              (not 
               (< i1_3 n1_2))) 
             (let 
              (
               (j2_4 0)) 
              (and 
               (INV3 n2_2 i2_3 j2_4 x2_3) 
               (forall 
                (
                 (n2_3 Int) 
                 (i2_4 Int) 
                 (j2_5 Int) 
                 (x2_4 Int)) 
                (and 
                 (=> 
                  (and 
                   (INV3 n2_3 i2_4 j2_5 x2_4) 
                   (< j2_5 n2_3)) 
                  (and 
                   (=> 
                    (= i2_4 1) 
                    (let 
                     (
                      (x2_5 
                       (+ x2_4 1))) 
                     (let 
                      (
                       (j2_6 
                        (+ j2_5 1))) 
                      (INV3 n2_3 i2_4 j2_6 x2_5)))) 
                   (=> 
                    (not 
                     (= i2_4 1)) 
                    (let 
                     (
                      (x2_5 
                       (+ x2_4 1))) 
                     (let 
                      (
                       (x2_6 
                        (+ x2_5 1))) 
                      (let 
                       (
                        (j2_6 
                         (+ j2_5 1))) 
                       (INV3 n2_3 i2_4 j2_6 x2_6))))))) 
                 (=> 
                  (and 
                   (INV3 n2_3 i2_4 j2_5 x2_4) 
                   (not 
                    (< j2_5 n2_3))) 
                  (let 
                   (
                    (i2_5 
                     (+ i2_4 1))) 
                   (INV1 n1_2 i1_3 j1_3 x1_3 n2_3 i2_5 j2_5 x2_4)))))))) 
            (=> 
             (and 
              (INV1 n1_2 i1_3 j1_3 x1_3 n2_2 i2_3 j2_3 x2_3) 
              (not 
               (< i2_3 n2_2)) 
              (< i1_3 n1_2)) 
             (let 
              (
               (j1_4 0)) 
              (and 
               (INV4 n1_2 i1_3 j1_4 x1_3) 
               (forall 
                (
                 (n1_3 Int) 
                 (i1_4 Int) 
                 (j1_5 Int) 
                 (x1_4 Int)) 
                (and 
                 (=> 
                  (and 
                   (INV4 n1_3 i1_4 j1_5 x1_4) 
                   (< j1_5 n1_3)) 
                  (and 
                   (=> 
                    (= i1_4 1) 
                    (let 
                     (
                      (x1_5 
                       (+ x1_4 1))) 
                     (let 
                      (
                       (j1_6 
                        (+ j1_5 1))) 
                      (INV4 n1_3 i1_4 j1_6 x1_5)))) 
                   (=> 
                    (not 
                     (= i1_4 1)) 
                    (let 
                     (
                      (x1_5 
                       (+ x1_4 1))) 
                     (let 
                      (
                       (x1_6 
                        (+ x1_5 1))) 
                      (let 
                       (
                        (j1_6 
                         (+ j1_5 1))) 
                       (INV4 n1_3 i1_4 j1_6 x1_6))))))) 
                 (=> 
                  (and 
                   (INV4 n1_3 i1_4 j1_5 x1_4) 
                   (not 
                    (< j1_5 n1_3))) 
                  (let 
                   (
                    (i1_5 
                     (+ i1_4 1))) 
                   (INV1 n1_3 i1_5 j1_5 x1_4 n2_2 i2_3 j2_3 x2_3)))))))) 
            (=> 
             (and 
              (INV1 n1_2 i1_3 j1_3 x1_3 n2_2 i2_3 j2_3 x2_3) 
              (not 
               (< i2_3 n2_2)) 
              (not 
               (< i1_3 n1_2))) 
             (and 
              (= x1_3 x2_3)))))))))))))))
(check-sat) 
(get-model) 
(exit)
