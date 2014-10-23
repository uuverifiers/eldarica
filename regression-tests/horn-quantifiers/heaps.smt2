;Generated with /home/mulbrich/sync/Documents/Research/Improve/Horn/sml/horn --arrays=heap a.spl a.spl
;On Wed Oct 22 18:28:37 2014
;By mulbrich

(set-logic HORN)
(declare-fun INV1 
 (Int Int Int Int Int Int Int Int) Bool)
(assert 
 (forall 
  (
   (i$1_1 Int) 
   ($heap$1_1 
    (Array Int Int)) 
   (n$1_1 Int) 
   (i$2_1 Int) 
   ($heap$2_1 
    (Array Int Int)) 
   (n$2_1 Int)) 
  (let 
   (
    ($heap$1_1 $heap$2_1)
    (n$1_1 n$2_1)) 
   (=> true 
    (let 
     (
      (i$1_2 0)) 
     (let 
      (
       (i$2_2 0)) 
      (and 
       (forall 
        (
         ($i2 Int) 
         ($i1 Int)) 
        (INV1 $i2 
         (select $heap$1_1 $i2) n$1_1 i$1_2 $i1 
         (select $heap$2_1 $i1) n$2_1 i$2_2))
       (forall 
        (
         ($heap$1_2 
          (Array Int Int)) 
         (n$1_2 Int) 
         (i$1_3 Int) 
         ($heap$2_2 
          (Array Int Int)) 
         (n$2_2 Int) 
         (i$2_3 Int)) 
        (and 
         (=> 
          (and 
           (forall 
            (
             ($i2 Int) 
             ($i1 Int)) 
            (INV1 $i2 
             (select $heap$1_2 $i2) n$1_2 i$1_3 $i1 
             (select $heap$2_2 $i1) n$2_2 i$2_3)) 
           (< i$2_3 n$2_2) 
           (< i$1_3 n$1_2)) 
          (let 
           (
            (i$2_4 
             (+ i$2_3 1))) 
           (let 
            (
             (i$1_4 
              (+ i$1_3 1))) 
            (forall 
             (
              ($i2 Int) 
              ($i1 Int)) 
             (INV1 $i2 
              (select $heap$1_2 $i2) n$1_2 i$1_4 $i1 
              (select $heap$2_2 $i1) n$2_2 i$2_4))))) 
         (=> 
          (and 
           (forall 
            (
             ($i2 Int) 
             ($i1 Int)) 
            (INV1 $i2 
             (select $heap$1_2 $i2) n$1_2 i$1_3 $i1 
             (select $heap$2_2 $i1) n$2_2 i$2_3)) 
           (< i$2_3 n$2_2) 
           (not 
            (< i$1_3 n$1_2))) 
          (let 
           (
            (i$2_4 
             (+ i$2_3 1))) 
           (forall 
            (
             ($i2 Int) 
             ($i1 Int)) 
            (INV1 $i2 
             (select $heap$1_2 $i2) n$1_2 i$1_3 $i1 
             (select $heap$2_2 $i1) n$2_2 i$2_4)))) 
         (=> 
          (and 
           (forall 
            (
             ($i2 Int) 
             ($i1 Int)) 
            (INV1 $i2 
             (select $heap$1_2 $i2) n$1_2 i$1_3 $i1 
             (select $heap$2_2 $i1) n$2_2 i$2_3)) 
           (not 
            (< i$2_3 n$2_2)) 
           (< i$1_3 n$1_2)) 
          (let 
           (
            (i$1_4 
             (+ i$1_3 1))) 
           (forall 
            (
             ($i2 Int) 
             ($i1 Int)) 
            (INV1 $i2 
             (select $heap$1_2 $i2) n$1_2 i$1_4 $i1 
             (select $heap$2_2 $i1) n$2_2 i$2_3)))) 
         (=> 
          (and 
           (forall 
            (
             ($i2 Int) 
             ($i1 Int)) 
            (INV1 $i2 
             (select $heap$1_2 $i2) n$1_2 i$1_3 $i1 
             (select $heap$2_2 $i1) n$2_2 i$2_3)) 
           (not 
            (< i$2_3 n$2_2)) 
           (not 
            (< i$1_3 n$1_2))) 
          (and 
           (= i$1_3 i$2_3) 
           (forall 
            (
             ($i Int)) 
            (= 
             (select $heap$1_2 $i) 
             (select $heap$2_2 $i))))))))))))))
(check-sat) 
(get-model) 
(exit)
