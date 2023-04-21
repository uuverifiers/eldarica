(set-logic HORN)
(define-fun
   IN_INV
   ((HEAP$2 (Array Int Int)))
   Bool
   (and
    (= 1 (select HEAP$2 (+ (- 0) 1)))
    (= 2 (select HEAP$2 (+ (- 0) 2)))
    (= 3 (select HEAP$2 (+ (- 0) 3)))
    (= 4 (select HEAP$2 (+ (- 0) 4)))
    (= 5 (select HEAP$2 (+ (- 0) 5)))
    (= 6 (select HEAP$2 (+ (- 0) 6)))
    (= 7 (select HEAP$2 (+ (- 0) 7)))
    (= 8 (select HEAP$2 (+ (- 0) 8)))
    (= 9 (select HEAP$2 (+ (- 0) 9)))
    (= 10 (select HEAP$2 (+ (- 0) 10)))))
(check-sat)
(get-model)
