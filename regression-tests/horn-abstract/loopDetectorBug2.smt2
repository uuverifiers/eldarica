(set-info :origin "Verification conditions for the caml program
  
  let rec bot _ = bot ()
  let fail _ = assert false
  
     let rec c1_COEFFICIENT_1086 = 0
     let rec c0_COEFFICIENT_1085 = 0
  
     let rec succ_without_checking_1117 set_flag_succ_1093 s_succ_n_1090 n_1031 =
       let set_flag_succ_1093 = true
       in
       let s_succ_n_1090 = n_1031
       in
         n_1031 + 1
  
     let rec succ_1030 prev_set_flag_succ_1092 s_prev_succ_n_1091 n_1031 =
       let u = if prev_set_flag_succ_1092 then
                let u_1232 = fail ()
                in
                  bot()
               else () in
              succ_without_checking_1117 prev_set_flag_succ_1092
                s_prev_succ_n_1091 n_1031
  
  
     let g_1032 x_DO_NOT_CARE_1200 x_DO_NOT_CARE_1201 r_EXPARAM_1088 x_DO_NOT_CARE_1198 x_DO_NOT_CARE_1199 r_1033 set_flag_succ_1093 s_succ_n_1090 a_1034 =
       r_1033 set_flag_succ_1093 s_succ_n_1090
         (r_1033 set_flag_succ_1093 s_succ_n_1090 a_1034)
  
     let rec f_1035 set_flag_succ_1093 s_succ_n_1090 n_1036 =
       if n_1036 = 0 then
         succ_1030
       else
         g_1032 set_flag_succ_1093 s_succ_n_1090
           ((c0_COEFFICIENT_1085 * n_1036) + c1_COEFFICIENT_1086)
           set_flag_succ_1093 s_succ_n_1090
           (f_1035 set_flag_succ_1093 s_succ_n_1090 (n_1036 - 1))
  
     let main n_1038 x_1039 =
       let x_DO_NOT_CARE_1196 = false in
       let x_DO_NOT_CARE_1197 = 0 in
       let set_flag_succ_1093 = false in
       let s_succ_n_1090 = 0 in
            if n_1038 >= 0 && x_1039 >= 0 then
         f_1035 set_flag_succ_1093 s_succ_n_1090 n_1038 set_flag_succ_1093
           s_succ_n_1090 x_1039
       else
         0
")

(set-logic HORN)

(declare-fun |fail$unknown:10|
  ( Int ) Bool
)

(declare-fun |g_1032$unknown:20|
  ( Int Int Int Int Int Int Int Int Int ) Bool
)

(declare-fun |g_1032$unknown:19|
  ( Int Int Int Int Int Int Int Int ) Bool
)

(declare-fun |f_1035$unknown:9|
  ( Int Int Int Int Int Int Int ) Bool
)

(declare-fun |g_1032$unknown:24|
  ( Int Int Int Int Int Int Int Int Int ) Bool
)

(declare-fun |g_1032$unknown:23|
  ( Int Int Int Int Int Int Int Int ) Bool
)

(declare-fun |f_1035$unknown:8|
  ( Int Int Int Int Int Int ) Bool
)

(declare-fun |succ_1030$unknown:28|
  ( Int Int Int Int ) Bool
)

(declare-fun |succ_without_checking_1117$unknown:32|
  ( Int Int Int Int ) Bool
)

(declare-fun |succ_1030$unknown:27|
  ( Int Int Int ) Bool
)

(declare-fun |fail$unknown:11|
  ( Int Int ) Bool
)

(declare-fun |bot$unknown:2|
  ( Int Int ) Bool
)

(assert
  (forall ( (|$V-reftype:65| Int) (|$alpha-1:$$tmp::1| Int) (|$knormal:1| Int) (|$knormal:2| Int) )
    (=>
      ( and (= |$knormal:1| 1) (= |$V-reftype:65| |$knormal:2|) (|bot$unknown:2| |$knormal:2| |$knormal:1|) true )
      (|bot$unknown:2| |$V-reftype:65| |$alpha-1:$$tmp::1|)
    )
  )
)
(assert
  (forall ( (|$knormal:1| Int) )
    (=>
      ( and (= |$knormal:1| 1) true )
      true
    )
  )
)
(assert
  (forall ( (|$V-reftype:71| Int) (|$alpha-10:n_1031| Int) (|$alpha-8:prev_set_flag_succ_1092| Int) (|$alpha-9:s_prev_succ_n_1091| Int) (|$knormal:10| Int) (|$knormal:11| Int) (|$knormal:7| Int) (|$knormal:8| Int) (|$knormal:9| Int) )
    (=>
      ( and (= |$knormal:8| 1) (= |$knormal:10| 1) (= |$V-reftype:71| |$knormal:7|) (not (= 0 |$alpha-8:prev_set_flag_succ_1092|)) (|succ_without_checking_1117$unknown:32| |$knormal:7| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) (|succ_1030$unknown:27| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) true true (|fail$unknown:11| |$knormal:11| |$knormal:10|) (|bot$unknown:2| |$knormal:9| |$knormal:8|) )
      (|succ_1030$unknown:28| |$V-reftype:71| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|)
    )
  )
)
(assert
  (forall ( (|$alpha-10:n_1031| Int) (|$alpha-8:prev_set_flag_succ_1092| Int) (|$alpha-9:s_prev_succ_n_1091| Int) (|$knormal:10| Int) (|$knormal:11| Int) (|$knormal:8| Int) (|$knormal:9| Int) )
    (=>
      ( and (= |$knormal:8| 1) (= |$knormal:10| 1) (not (= 0 |$alpha-8:prev_set_flag_succ_1092|)) (|succ_1030$unknown:27| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) true true (|fail$unknown:11| |$knormal:11| |$knormal:10|) (|bot$unknown:2| |$knormal:9| |$knormal:8|) )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-10:n_1031| Int) (|$alpha-8:prev_set_flag_succ_1092| Int) (|$alpha-9:s_prev_succ_n_1091| Int) (|$knormal:10| Int) (|$knormal:11| Int) (|$knormal:8| Int) (|$knormal:9| Int) )
    (=>
      ( and (= |$knormal:8| 1) (= |$knormal:10| 1) (not (= 0 |$alpha-8:prev_set_flag_succ_1092|)) (|succ_1030$unknown:27| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) true true (|fail$unknown:11| |$knormal:11| |$knormal:10|) (|bot$unknown:2| |$knormal:9| |$knormal:8|) )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-10:n_1031| Int) (|$alpha-8:prev_set_flag_succ_1092| Int) (|$alpha-9:s_prev_succ_n_1091| Int) (|$knormal:10| Int) (|$knormal:11| Int) (|$knormal:8| Int) (|$knormal:9| Int) )
    (=>
      ( and (= |$knormal:8| 1) (= |$knormal:10| 1) (not (= 0 |$alpha-8:prev_set_flag_succ_1092|)) (|succ_1030$unknown:27| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) true true (|fail$unknown:11| |$knormal:11| |$knormal:10|) (|bot$unknown:2| |$knormal:9| |$knormal:8|) )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (= 0 |$knormal:23|)) true true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true true true )
      true
    )
  )
)
(assert
  (forall ( (|$V-reftype:14| Int) (|$V-reftype:39| Int) (|$V-reftype:41| Int) (|$alpha-22:set_flag_succ_1093| Int) (|$alpha-23:s_succ_n_1090| Int) (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) (|f_1035$unknown:8| |$V-reftype:14| |$V-reftype:41| |$V-reftype:39| |$alpha-24:n_1036| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|) true true true true true )
      (|g_1032$unknown:23| |$V-reftype:14| |$V-reftype:41| |$V-reftype:39| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093| |$knormal:34| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:39| Int) (|$V-reftype:41| Int) (|$V-reftype:43| Int) (|$V-reftype:44| Int) (|$alpha-22:set_flag_succ_1093| Int) (|$alpha-23:s_succ_n_1090| Int) (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) (|g_1032$unknown:24| |$V-reftype:44| |$V-reftype:43| |$V-reftype:41| |$V-reftype:39| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093| |$knormal:34| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|) (|f_1035$unknown:8| |$V-reftype:43| |$V-reftype:41| |$V-reftype:39| |$alpha-24:n_1036| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|) true true true true true )
      (|f_1035$unknown:9| |$V-reftype:44| |$V-reftype:43| |$V-reftype:41| |$V-reftype:39| |$alpha-24:n_1036| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|)
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (= 0 |$knormal:23|)) true true true true true )
      true
    )
  )
)
(assert
  (forall ( (|$V-reftype:14| Int) (|$V-reftype:51| Int) (|$V-reftype:53| Int) (|$alpha-22:set_flag_succ_1093| Int) (|$alpha-23:s_succ_n_1090| Int) (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (= 0 |$knormal:23|)) (|f_1035$unknown:8| |$V-reftype:14| |$V-reftype:53| |$V-reftype:51| |$alpha-24:n_1036| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|) true true true true true )
      (|succ_1030$unknown:27| |$V-reftype:14| |$V-reftype:53| |$V-reftype:51|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:51| Int) (|$V-reftype:53| Int) (|$V-reftype:55| Int) (|$V-reftype:56| Int) (|$alpha-22:set_flag_succ_1093| Int) (|$alpha-23:s_succ_n_1090| Int) (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (= 0 |$knormal:23|)) (|succ_1030$unknown:28| |$V-reftype:56| |$V-reftype:55| |$V-reftype:53| |$V-reftype:51|) (|f_1035$unknown:8| |$V-reftype:55| |$V-reftype:53| |$V-reftype:51| |$alpha-24:n_1036| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|) true true true true true )
      (|f_1035$unknown:9| |$V-reftype:56| |$V-reftype:55| |$V-reftype:53| |$V-reftype:51| |$alpha-24:n_1036| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:13| Int) (|$V-reftype:15| Int) (|$V-reftype:16| Int) (|$alpha-22:set_flag_succ_1093| Int) (|$alpha-23:s_succ_n_1090| Int) (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:30| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) (|g_1032$unknown:19| |$V-reftype:15| |$V-reftype:13| |$knormal:30| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093| |$knormal:34| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|) true true (|f_1035$unknown:9| |$V-reftype:16| |$V-reftype:15| |$V-reftype:13| |$knormal:30| |$knormal:28| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|) true true true )
      (|g_1032$unknown:20| |$V-reftype:16| |$V-reftype:15| |$V-reftype:13| |$knormal:30| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093| |$knormal:34| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|)
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true true )
      true
    )
  )
)
(assert
  (forall ( (|$V-reftype:13| Int) (|$V-reftype:34| Int) (|$alpha-22:set_flag_succ_1093| Int) (|$alpha-23:s_succ_n_1090| Int) (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:30| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) (|g_1032$unknown:19| |$V-reftype:34| |$V-reftype:13| |$knormal:30| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093| |$knormal:34| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|) true true true true true )
      (|f_1035$unknown:8| |$V-reftype:34| |$V-reftype:13| |$knormal:30| |$knormal:28| |$alpha-23:s_succ_n_1090| |$alpha-22:set_flag_succ_1093|)
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:24| Int) (|$knormal:28| Int) (|$knormal:34| Int) )
    (=>
      ( and (= |$knormal:34| (+ |$knormal:24| |$alpha-25:c1_COEFFICIENT_1086|)) (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= |$knormal:24| (* |$alpha-26:c0_COEFFICIENT_1085| |$alpha-24:n_1036|)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:28| Int) )
    (=>
      ( and (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:28| Int) )
    (=>
      ( and (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-24:n_1036| Int) (|$alpha-25:c1_COEFFICIENT_1086| Int) (|$alpha-26:c0_COEFFICIENT_1085| Int) (|$knormal:23| Int) (|$knormal:28| Int) )
    (=>
      ( and (= |$knormal:28| (- |$alpha-24:n_1036| 1)) (= (not (= 0 |$knormal:23|)) (= |$alpha-24:n_1036| 0)) (= |$alpha-26:c0_COEFFICIENT_1085| 0) (= |$alpha-25:c1_COEFFICIENT_1086| 0) (not (not (= 0 |$knormal:23|))) true true true )
      true
    )
  )
)
(assert
  (not (exists ( (|$alpha-2:$$tmp::2| Int) )
    ( and (|fail$unknown:10| |$alpha-2:$$tmp::2|) )
    )
  )
)
(assert
  (forall ( (|$alpha-10:n_1031| Int) (|$alpha-8:prev_set_flag_succ_1092| Int) (|$alpha-9:s_prev_succ_n_1091| Int) (|$knormal:10| Int) (|$knormal:11| Int) (|$knormal:8| Int) )
    (=>
      ( and (= |$knormal:8| 1) (= |$knormal:10| 1) (not (= 0 |$alpha-8:prev_set_flag_succ_1092|)) (|succ_1030$unknown:27| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) true true (|fail$unknown:11| |$knormal:11| |$knormal:10|) )
      true
    )
  )
)
(assert
  (forall ( (|$V-reftype:74| Int) (|$alpha-13:x_DO_NOT_CARE_1200| Int) (|$alpha-14:x_DO_NOT_CARE_1201| Int) (|$alpha-15:r_EXPARAM_1088| Int) (|$alpha-16:x_DO_NOT_CARE_1198| Int) (|$alpha-17:x_DO_NOT_CARE_1199| Int) (|$alpha-19:set_flag_succ_1093| Int) (|$alpha-20:s_succ_n_1090| Int) (|$alpha-21:a_1034| Int) (|$knormal:16| Int) (|$knormal:22| Int) )
    (=>
      ( and (= |$V-reftype:74| |$knormal:22|) (|g_1032$unknown:23| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) true true (|g_1032$unknown:20| |$knormal:22| |$knormal:16| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) (|g_1032$unknown:20| |$knormal:16| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) true true true true true )
      (|g_1032$unknown:24| |$V-reftype:74| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|)
    )
  )
)
(assert
  (forall ( (|$alpha-13:x_DO_NOT_CARE_1200| Int) (|$alpha-14:x_DO_NOT_CARE_1201| Int) (|$alpha-15:r_EXPARAM_1088| Int) (|$alpha-16:x_DO_NOT_CARE_1198| Int) (|$alpha-17:x_DO_NOT_CARE_1199| Int) (|$alpha-19:set_flag_succ_1093| Int) (|$alpha-20:s_succ_n_1090| Int) (|$alpha-21:a_1034| Int) (|$knormal:16| Int) )
    (=>
      ( and (|g_1032$unknown:23| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) true true (|g_1032$unknown:20| |$knormal:16| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) true true true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-13:x_DO_NOT_CARE_1200| Int) (|$alpha-14:x_DO_NOT_CARE_1201| Int) (|$alpha-15:r_EXPARAM_1088| Int) (|$alpha-16:x_DO_NOT_CARE_1198| Int) (|$alpha-17:x_DO_NOT_CARE_1199| Int) (|$alpha-19:set_flag_succ_1093| Int) (|$alpha-20:s_succ_n_1090| Int) (|$alpha-21:a_1034| Int) (|$knormal:16| Int) )
    (=>
      ( and (|g_1032$unknown:23| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) true true (|g_1032$unknown:20| |$knormal:16| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) true true true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-13:x_DO_NOT_CARE_1200| Int) (|$alpha-14:x_DO_NOT_CARE_1201| Int) (|$alpha-15:r_EXPARAM_1088| Int) (|$alpha-16:x_DO_NOT_CARE_1198| Int) (|$alpha-17:x_DO_NOT_CARE_1199| Int) (|$alpha-19:set_flag_succ_1093| Int) (|$alpha-20:s_succ_n_1090| Int) (|$alpha-21:a_1034| Int) (|$knormal:16| Int) )
    (=>
      ( and (|g_1032$unknown:23| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) true true (|g_1032$unknown:20| |$knormal:16| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) true true true true true )
      (|g_1032$unknown:19| |$knormal:16| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|)
    )
  )
)
(assert
  (forall ( (|$alpha-13:x_DO_NOT_CARE_1200| Int) (|$alpha-14:x_DO_NOT_CARE_1201| Int) (|$alpha-15:r_EXPARAM_1088| Int) (|$alpha-16:x_DO_NOT_CARE_1198| Int) (|$alpha-17:x_DO_NOT_CARE_1199| Int) (|$alpha-19:set_flag_succ_1093| Int) (|$alpha-20:s_succ_n_1090| Int) (|$alpha-21:a_1034| Int) )
    (=>
      ( and (|g_1032$unknown:23| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) true true true true true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-13:x_DO_NOT_CARE_1200| Int) (|$alpha-14:x_DO_NOT_CARE_1201| Int) (|$alpha-15:r_EXPARAM_1088| Int) (|$alpha-16:x_DO_NOT_CARE_1198| Int) (|$alpha-17:x_DO_NOT_CARE_1199| Int) (|$alpha-19:set_flag_succ_1093| Int) (|$alpha-20:s_succ_n_1090| Int) (|$alpha-21:a_1034| Int) )
    (=>
      ( and (|g_1032$unknown:23| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) true true true true true true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-13:x_DO_NOT_CARE_1200| Int) (|$alpha-14:x_DO_NOT_CARE_1201| Int) (|$alpha-15:r_EXPARAM_1088| Int) (|$alpha-16:x_DO_NOT_CARE_1198| Int) (|$alpha-17:x_DO_NOT_CARE_1199| Int) (|$alpha-19:set_flag_succ_1093| Int) (|$alpha-20:s_succ_n_1090| Int) (|$alpha-21:a_1034| Int) )
    (=>
      ( and (|g_1032$unknown:23| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|) true true true true true true true )
      (|g_1032$unknown:19| |$alpha-21:a_1034| |$alpha-20:s_succ_n_1090| |$alpha-19:set_flag_succ_1093| |$alpha-17:x_DO_NOT_CARE_1199| |$alpha-16:x_DO_NOT_CARE_1198| |$alpha-15:r_EXPARAM_1088| |$alpha-14:x_DO_NOT_CARE_1201| |$alpha-13:x_DO_NOT_CARE_1200|)
    )
  )
)
(assert
  (forall ( (|$V-reftype:73| Int) (|$alpha-10:n_1031| Int) (|$alpha-12:u| Int) (|$alpha-8:prev_set_flag_succ_1092| Int) (|$alpha-9:s_prev_succ_n_1091| Int) (|$knormal:7| Int) )
    (=>
      ( and (= |$alpha-12:u| 1) (= |$V-reftype:73| |$knormal:7|) (not (not (= 0 |$alpha-8:prev_set_flag_succ_1092|))) (|succ_without_checking_1117$unknown:32| |$knormal:7| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) (|succ_1030$unknown:27| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) true true )
      (|succ_1030$unknown:28| |$V-reftype:73| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|)
    )
  )
)
(assert
  (forall ( (|$alpha-10:n_1031| Int) (|$alpha-8:prev_set_flag_succ_1092| Int) (|$alpha-9:s_prev_succ_n_1091| Int) (|$knormal:10| Int) )
    (=>
      ( and (= |$knormal:10| 1) (not (= 0 |$alpha-8:prev_set_flag_succ_1092|)) (|succ_1030$unknown:27| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) true true )
      (|fail$unknown:10| |$knormal:10|)
    )
  )
)
(assert
  (forall ( (|$alpha-10:n_1031| Int) (|$alpha-12:u| Int) (|$alpha-8:prev_set_flag_succ_1092| Int) (|$alpha-9:s_prev_succ_n_1091| Int) )
    (=>
      ( and (= |$alpha-12:u| 1) (not (not (= 0 |$alpha-8:prev_set_flag_succ_1092|))) (|succ_1030$unknown:27| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-10:n_1031| Int) (|$alpha-12:u| Int) (|$alpha-8:prev_set_flag_succ_1092| Int) (|$alpha-9:s_prev_succ_n_1091| Int) )
    (=>
      ( and (= |$alpha-12:u| 1) (not (not (= 0 |$alpha-8:prev_set_flag_succ_1092|))) (|succ_1030$unknown:27| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) true true )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-10:n_1031| Int) (|$alpha-12:u| Int) (|$alpha-8:prev_set_flag_succ_1092| Int) (|$alpha-9:s_prev_succ_n_1091| Int) )
    (=>
      ( and (= |$alpha-12:u| 1) (not (not (= 0 |$alpha-8:prev_set_flag_succ_1092|))) (|succ_1030$unknown:27| |$alpha-10:n_1031| |$alpha-9:s_prev_succ_n_1091| |$alpha-8:prev_set_flag_succ_1092|) true true )
      true
    )
  )
)
(assert
  (forall ( (|$V-reftype:68| Int) (|$alpha-3:set_flag_succ_1093| Int) (|$alpha-4:s_succ_n_1090| Int) (|$alpha-5:n_1031| Int) (|$alpha-6:set_flag_succ_1093| Int) )
    (=>
      ( and (= |$alpha-6:set_flag_succ_1093| 1) (= |$V-reftype:68| (+ |$alpha-5:n_1031| 1)) true true true )
      (|succ_without_checking_1117$unknown:32| |$V-reftype:68| |$alpha-5:n_1031| |$alpha-4:s_succ_n_1090| |$alpha-3:set_flag_succ_1093|)
    )
  )
)
(assert
  (forall ( (|$alpha-27:n_1038| Int) (|$alpha-28:x_1039| Int) (|$alpha-29:x_DO_NOT_CARE_1196| Int) (|$alpha-30:x_DO_NOT_CARE_1197| Int) (|$alpha-31:set_flag_succ_1093| Int) (|$alpha-32:s_succ_n_1090| Int) (|$knormal:44| Int) (|$knormal:45| Int) (|$knormal:46| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:46|)) (and (not (= 0 |$knormal:44|)) (not (= 0 |$knormal:45|)))) (= (not (= 0 |$knormal:45|)) (>= |$alpha-28:x_1039| 0)) (= (not (= 0 |$knormal:44|)) (>= |$alpha-27:n_1038| 0)) (= |$alpha-32:s_succ_n_1090| 0) (= |$alpha-31:set_flag_succ_1093| 0) (= |$alpha-30:x_DO_NOT_CARE_1197| 0) (= |$alpha-29:x_DO_NOT_CARE_1196| 0) (not (= 0 |$knormal:46|)) )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-27:n_1038| Int) (|$alpha-28:x_1039| Int) (|$alpha-29:x_DO_NOT_CARE_1196| Int) (|$alpha-30:x_DO_NOT_CARE_1197| Int) (|$alpha-31:set_flag_succ_1093| Int) (|$alpha-32:s_succ_n_1090| Int) (|$knormal:44| Int) (|$knormal:45| Int) (|$knormal:46| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:46|)) (and (not (= 0 |$knormal:44|)) (not (= 0 |$knormal:45|)))) (= (not (= 0 |$knormal:45|)) (>= |$alpha-28:x_1039| 0)) (= (not (= 0 |$knormal:44|)) (>= |$alpha-27:n_1038| 0)) (= |$alpha-32:s_succ_n_1090| 0) (= |$alpha-31:set_flag_succ_1093| 0) (= |$alpha-30:x_DO_NOT_CARE_1197| 0) (= |$alpha-29:x_DO_NOT_CARE_1196| 0) (not (= 0 |$knormal:46|)) )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-27:n_1038| Int) (|$alpha-28:x_1039| Int) (|$alpha-29:x_DO_NOT_CARE_1196| Int) (|$alpha-30:x_DO_NOT_CARE_1197| Int) (|$alpha-31:set_flag_succ_1093| Int) (|$alpha-32:s_succ_n_1090| Int) (|$knormal:44| Int) (|$knormal:45| Int) (|$knormal:46| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:46|)) (and (not (= 0 |$knormal:44|)) (not (= 0 |$knormal:45|)))) (= (not (= 0 |$knormal:45|)) (>= |$alpha-28:x_1039| 0)) (= (not (= 0 |$knormal:44|)) (>= |$alpha-27:n_1038| 0)) (= |$alpha-32:s_succ_n_1090| 0) (= |$alpha-31:set_flag_succ_1093| 0) (= |$alpha-30:x_DO_NOT_CARE_1197| 0) (= |$alpha-29:x_DO_NOT_CARE_1196| 0) (not (= 0 |$knormal:46|)) )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-27:n_1038| Int) (|$alpha-28:x_1039| Int) (|$alpha-29:x_DO_NOT_CARE_1196| Int) (|$alpha-30:x_DO_NOT_CARE_1197| Int) (|$alpha-31:set_flag_succ_1093| Int) (|$alpha-32:s_succ_n_1090| Int) (|$knormal:44| Int) (|$knormal:45| Int) (|$knormal:46| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:46|)) (and (not (= 0 |$knormal:44|)) (not (= 0 |$knormal:45|)))) (= (not (= 0 |$knormal:45|)) (>= |$alpha-28:x_1039| 0)) (= (not (= 0 |$knormal:44|)) (>= |$alpha-27:n_1038| 0)) (= |$alpha-32:s_succ_n_1090| 0) (= |$alpha-31:set_flag_succ_1093| 0) (= |$alpha-30:x_DO_NOT_CARE_1197| 0) (= |$alpha-29:x_DO_NOT_CARE_1196| 0) (not (= 0 |$knormal:46|)) )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-27:n_1038| Int) (|$alpha-28:x_1039| Int) (|$alpha-29:x_DO_NOT_CARE_1196| Int) (|$alpha-30:x_DO_NOT_CARE_1197| Int) (|$alpha-31:set_flag_succ_1093| Int) (|$alpha-32:s_succ_n_1090| Int) (|$knormal:44| Int) (|$knormal:45| Int) (|$knormal:46| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:46|)) (and (not (= 0 |$knormal:44|)) (not (= 0 |$knormal:45|)))) (= (not (= 0 |$knormal:45|)) (>= |$alpha-28:x_1039| 0)) (= (not (= 0 |$knormal:44|)) (>= |$alpha-27:n_1038| 0)) (= |$alpha-32:s_succ_n_1090| 0) (= |$alpha-31:set_flag_succ_1093| 0) (= |$alpha-30:x_DO_NOT_CARE_1197| 0) (= |$alpha-29:x_DO_NOT_CARE_1196| 0) (not (= 0 |$knormal:46|)) )
      true
    )
  )
)
(assert
  (forall ( (|$alpha-27:n_1038| Int) (|$alpha-28:x_1039| Int) (|$alpha-29:x_DO_NOT_CARE_1196| Int) (|$alpha-30:x_DO_NOT_CARE_1197| Int) (|$alpha-31:set_flag_succ_1093| Int) (|$alpha-32:s_succ_n_1090| Int) (|$knormal:44| Int) (|$knormal:45| Int) (|$knormal:46| Int) )
    (=>
      ( and (= (not (= 0 |$knormal:46|)) (and (not (= 0 |$knormal:44|)) (not (= 0 |$knormal:45|)))) (= (not (= 0 |$knormal:45|)) (>= |$alpha-28:x_1039| 0)) (= (not (= 0 |$knormal:44|)) (>= |$alpha-27:n_1038| 0)) (= |$alpha-32:s_succ_n_1090| 0) (= |$alpha-31:set_flag_succ_1093| 0) (= |$alpha-30:x_DO_NOT_CARE_1197| 0) (= |$alpha-29:x_DO_NOT_CARE_1196| 0) (not (= 0 |$knormal:46|)) )
      (|f_1035$unknown:8| |$alpha-28:x_1039| |$alpha-32:s_succ_n_1090| |$alpha-31:set_flag_succ_1093| |$alpha-27:n_1038| |$alpha-32:s_succ_n_1090| |$alpha-31:set_flag_succ_1093|)
    )
  )
)
(check-sat)

(exit)

