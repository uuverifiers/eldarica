(set-logic HORN)
(define-fun
   IN_INV
   ((votes$1_0 Int)
    (res$1_0 Int)
    (length$1_0 Int)
    (v$1_0 Int)
    (w$1_0 Int)
    (HEAP$1 (Array Int Int))
    (votes$2_0 Int)
    (res$2_0 Int)
    (length$2_0 Int)
    (v$2_0 Int)
    (w$2_0 Int)
    (HEAP$2 (Array Int Int)))
   Bool
   (and
      (= votes$1_0 votes$2_0)
      (= res$1_0 res$2_0) 
      (= v$1_0 v$2_0)
      (= w$1_0 w$2_0) 
      (< v$1_0 length$1_0)
      (>= v$1_0 0)
      (>= w$1_0 0)
      (< w$1_0 length$1_0)
      (forall ((i Int))
              (= (select HEAP$1 i) (select HEAP$2 i)))))
(define-fun
   OUT_INV
   ((result$1 Int)
    (result$2 Int)
    (HEAP$1 (Array Int Int))
    (HEAP$2 (Array Int Int)))
   Bool
   (forall
    ((i Int))
    (= (select HEAP$1 i) (select HEAP$2 i))))
(declare-fun
   INV_MAIN_0
   (Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int
    Int)
   Bool)
(assert
   (forall
      ((votes$1_0 Int)
       (res$1_0 Int)
       (length$1_0 Int)
       (v$1_0 Int)
       (w$1_0 Int)
       (HEAP$1 (Array Int Int))
       (votes$2_0 Int)
       (res$2_0 Int)
       (length$2_0 Int)
       (v$2_0 Int)
       (w$2_0 Int)
       (HEAP$2 (Array Int Int)))
      (=>
         (IN_INV votes$1_0 res$1_0 length$1_0 v$1_0 w$1_0 HEAP$1 votes$2_0 res$2_0 length$2_0 v$2_0 w$2_0 HEAP$2)
         (let
             ((_$2_1 (+ votes$2_0 (* 4 v$2_0))))
           (let
               ((_$2_2 (select HEAP$2 _$2_1)))
             (let
                 ((_$2_4 (+ votes$2_0 (* 4 w$2_0))))
               (let
                   ((_$2_5 (select HEAP$2 _$2_4)))
                 (let
                     ((_$2_7 (+ votes$2_0 (* 4 v$2_0))))
                   (let
                       ((HEAP$2 (store HEAP$2 _$2_7 _$2_5))
                        (_$2_8 w$2_0))
                     (let
                         ((_$2_9 (+ votes$2_0 (* 4 _$2_8))))
                       (let
                           ((HEAP$2 (store HEAP$2 _$2_9 _$2_2)))
                         (forall
                          ((i1 Int)
                           (i2 Int))
                          (INV_MAIN_0 0 length$1_0 res$1_0 votes$1_0 i1 (select HEAP$1 i1) _$2_2 0 length$2_0 res$2_0 v$2_0 votes$2_0 w$2_0 i2 (select HEAP$2 i2))))))))))))))
(assert
 (forall
  ((i.0$1_0 Int)
   (length$1_0 Int)
   (res$1_0 Int)
   (votes$1_0 Int)
   (HEAP$1 (Array Int Int))
   (_$2_2 Int)
   (i.0$2_0 Int)
   (length$2_0 Int)
   (res$2_0 Int)
   (v$2_0 Int)
   (votes$2_0 Int)
   (w$2_0 Int)
   (HEAP$2 (Array Int Int)))
  (=>
   (and
    (forall
     ((i1 Int)
      (i2 Int))
     (INV_MAIN_0 i.0$1_0 length$1_0 res$1_0 votes$1_0 i1 (select HEAP$1 i1) _$2_2 i.0$2_0 length$2_0 res$2_0 v$2_0 votes$2_0 w$2_0 i2 (select HEAP$2 i2))))
   (=> 
    (let
        ((_$2_23 (select HEAP$2 (+ votes$2_0 (* 4 v$2_0)))))
      (let
          ((HEAP$2 (store HEAP$2 (+ votes$2_0 (* 4 w$2_0)) _$2_23)))
        (let
            ((HEAP$2 (store HEAP$2 (+ votes$2_0 (* 4 v$2_0)) _$2_2)))
          (OUT_INV 0 0 HEAP$1 HEAP$2))))))))
(assert
 (forall
  ((i.0$1_0 Int)
   (length$1_0 Int)
   (res$1_0 Int)
   (votes$1_0 Int)
   (HEAP$1 (Array Int Int))
   (_$2_2 Int)
   (i.0$2_0 Int)
   (length$2_0 Int)
   (res$2_0 Int)
   (v$2_0 Int)
   (votes$2_0 Int)
   (w$2_0 Int)
   (HEAP$2 (Array Int Int)))
  (=>
   (forall
    ((i1 Int)
     (i2 Int))
    (INV_MAIN_0 i.0$1_0 length$1_0 res$1_0 votes$1_0 i1 (select HEAP$1 i1) _$2_2 i.0$2_0 length$2_0 res$2_0 v$2_0 votes$2_0 w$2_0 i2 (select HEAP$2 i2)))
   (=> 
    (let
        ((_$1_5 (select HEAP$1 (+ votes$1_0 (* 4 i.0$1_0)))))
      (let
          ((_$1_8 (select HEAP$1 (+ res$1_0 (* 4 _$1_5)))))
        (let
            ((HEAP$1 (store HEAP$1 (+ res$1_0 (* 4 _$1_5)) (+ _$1_8 1))))
          (let
              ((i.0$1_0 (+ i.0$1_0 1)))
            (let
                ((_$2_14 (+ votes$2_0 (* 4 i.0$2_0))))
              (let
                  ((_$2_15 (select HEAP$2 _$2_14)))
                (let
                    ((_$2_17 (+ res$2_0 (* 4 _$2_15))))
                  (let
                      ((_$2_18 (select HEAP$2 _$2_17)))
                    (let
                        ((HEAP$2 (store HEAP$2 _$2_17 (+ _$2_18 1))))
                      (let
                          ((i.0$2_0 (+ i.0$2_0 1)))
                        (forall
                         ((i1 Int)
                          (i2 Int))
                         (INV_MAIN_0 i.0$1_0 length$1_0 res$1_0 votes$1_0 i1 (select HEAP$1 i1) _$2_2 i.0$2_0 length$2_0 res$2_0 v$2_0 votes$2_0 w$2_0 i2 (select HEAP$2 i2)))))))))))))))))
(check-sat)
(get-model)
