;Generated with /amd.home/home/klebanov/Oldworkingcopies/Reve/Horn/sml/horn /home/i57/klebanov/Oldworkingcopies/Reve/Horn/experiments/arrays/equalize
;On Sat Oct 25 21:36:25 2014
;By klebanov

(set-logic HORN)
(assert 
 (forall 
  (
   (i$1_1 Int) 
   ($heap$1_1 
    (Array Int Int)) 
   (a$1_1 Int) 
   (n$1_1 Int) 
   (i$2_1 Int) 
   ($heap$2_1 
    (Array Int Int)) 
   (a$2_1 Int) 
   (n$2_1 Int)) 
  (let 
   (
    ($heap$1_1 $heap$2_1)
    (a$1_1 a$2_1)
    (n$1_1 n$2_1)) 
   (=> true 
    (let 
     (
      (i$1_2 0)) 
     (let 
      (
       (i$1_3 
        (select $heap$1_1 
         (+ a$1_1 0)))) 
      (let 
       (
        (i$2_2 0)) 
       (let 
        (
         (i$2_3 
          (select $heap$2_1 
           (+ a$2_1 0)))) 
        (and 
         (= i$1_3 i$2_3) 
         (forall 
          (
           ($i Int)) 
          (= 
           (select $heap$1_1 $i) 
           (select $heap$2_1 $i))))))))))))
(check-sat) 
(get-model) 
(exit)
