(set-logic HORN)
(declare-fun REC__g 
 (Int Int Int) Bool) 
(declare-fun REC_g_ 
 (Int Int) Bool) 
(declare-fun REC_g_g 
 (Int Int Int Int Int) Bool)
(assert 
 (forall 
  (
   (n1_1 Int) 
   (r1_1 Int) 
   (n2_1 Int) 
   (r2_1 Int)) 
  (=> 
   (and true 
    (and 
     (= n1_1 n2_1))) 
   (forall 
    (
     (r2_2 Int)
     (r1_2 Int)) 
    (=> 
     (REC_g_g n1_1 r1_2 n2_1 0 r2_2) 
     (and 
      (= r1_2 r2_2)))))))
(assert 
 (forall 
  (
   (n1_1 Int) 
   (n2_1 Int) 
   (s2_1 Int)) 
  (let 
   (
    (r1_2 0)) 
   (and 
    (=> 
     (<= n1_1 0) 
     (let 
      (
       (r1_3 0)) 
      (let 
       (
        (r2_2 0)) 
       (and 
        (=> 
         (<= n2_1 0) 
         (let 
          (
           (r2_3 s2_1)) 
          (REC_g_g n1_1 r1_3 n2_1 s2_1 r2_3))) 
        (=> 
         (not 
          (<= n2_1 0)) 
         (forall 
          (
           (r2_3 Int)) 
          (=> 
           (REC__g 
            (- n2_1 1) 
            (+ n2_1 s2_1) r2_3) 
           (REC_g_g n1_1 r1_3 n2_1 s2_1 r2_3)))))))) 
    (=> 
     (not 
      (<= n1_1 0)) 
     (let 
      (
       (r2_2 0)) 
      (and 
       (=> 
        (<= n2_1 0) 
        (let 
         (
          (r2_3 s2_1)) 
         (forall 
          (
           (r1_3 Int)) 
          (=> 
           (REC_g_ 
            (- n1_1 1) r1_3) 
           (let 
            (
             (r1_4 
              (+ n1_1 r1_3))) 
            (REC_g_g n1_1 r1_4 n2_1 s2_1 r2_3)))))) 
       (=> 
        (not 
         (<= n2_1 0)) 
        (forall 
         (
          (r2_3 Int)
          (r1_3 Int)) 
         (=> 
          (REC_g_g 
           (- n1_1 1) r1_3 
           (- n2_1 1) 
           (+ n2_1 s2_1) r2_3) 
          (let 
           (
            (r1_4 
             (+ n1_1 r1_3))) 
           (REC_g_g n1_1 r1_4 n2_1 s2_1 r2_3)))))))))))) 
(assert 
 (forall 
  (
   (n1_1 Int)) 
  (let 
   (
    (r1_2 0)) 
   (and 
    (=> 
     (<= n1_1 0) 
     (let 
      (
       (r1_3 0)) 
      (REC_g_ n1_1 r1_3))) 
    (=> 
     (not 
      (<= n1_1 0)) 
     (forall 
      (
       (r1_3 Int)) 
      (=> 
       (REC_g_ 
        (- n1_1 1) r1_3) 
       (let 
        (
         (r1_4 
          (+ n1_1 r1_3))) 
        (REC_g_ n1_1 r1_4))))))))) 
(assert 
 (forall 
  (
   (n2_1 Int) 
   (s2_1 Int)) 
  (let 
   (
    (r2_2 0)) 
   (and 
    (=> 
     (<= n2_1 0) 
     (let 
      (
       (r2_3 s2_1)) 
      (REC__g n2_1 s2_1 r2_3))) 
    (=> 
     (not 
      (<= n2_1 0)) 
     (forall 
      (
       (r2_3 Int)) 
      (=> 
       (REC__g 
        (- n2_1 1) 
        (+ n2_1 s2_1) r2_3) 
       (REC__g n2_1 s2_1 r2_3))))))))
(check-sat) 
(get-model) 
(exit)
