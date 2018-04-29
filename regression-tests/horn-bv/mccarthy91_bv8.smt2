(set-info :origin "Bit-vector version of NTS benchmark")

(set-logic HORN)

(declare-fun main_sf ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)
(declare-fun main_s3 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)
(declare-fun main_s1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)
(declare-fun main_s2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)
(declare-fun f_s1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)
(declare-fun f_s2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)
(declare-fun f_sf ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)
(declare-fun f_s3 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)

(assert(forall((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8))(?E (_ BitVec 8))(?F (_ BitVec 8)))(=>(and (main_s3 ?A ?B ?E ?F)(and (= ?E (_ bv91 8)) (and (= ?E ?C) (= ?F ?D)))) (main_sf ?A ?B ?C ?D))))

(assert(not (exists((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8))(?E (_ BitVec 8))(?F (_ BitVec 8)))(and (main_s3 ?A ?B ?C ?D)(and (not (= ?C (_ bv91 8))) (and (= ?C ?E) (= ?D ?F)))))))

(assert(forall((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8))(?E (_ BitVec 8))(?F (_ BitVec 8)))(=>(and (main_s1 ?A ?B ?E ?F)(and (bvsle ?D (_ bv100 8)) (= ?E ?C))) (main_s2 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8)))(=>(and (= ?A ?C) (= ?B ?D)) (main_s1 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8))(?E (_ BitVec 8))(?F (_ BitVec 8)))(=>(and (f_s1 ?A ?B ?E ?F)(and (and (bvsle ?F (_ bv100 8)) (= ?C (bvadd ?F (_ bv11 8)))) (= ?F ?D))) (f_s2 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8))(?E (_ BitVec 8))(?F (_ BitVec 8)))(=>(and (f_s1 ?A ?B ?E ?F)(and (and (bvsgt ?F (_ bv100 8)) (= ?C (bvsub ?F (_ bv10 8)))) (= ?F ?D))) (f_sf ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8))(?E (_ BitVec 8))(?F (_ BitVec 8))(?G (_ BitVec 8))(?H (_ BitVec 8))(?I (_ BitVec 8))(?J (_ BitVec 8)))(=>(and (and (and (and (f_s2 ?A ?B ?E ?F)(= ?G ?E))(f_sf ?H ?G ?I ?J))(= ?I ?C))(= ?F ?D)) (f_s3 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8))(?E (_ BitVec 8))(?F (_ BitVec 8))(?G (_ BitVec 8))(?H (_ BitVec 8)))(=>(and (and (f_s2 ?E ?F ?G ?H)(= ?B ?G))(and (= ?A ?C) (= ?B ?D))) (f_s1 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8))(?E (_ BitVec 8))(?F (_ BitVec 8))(?G (_ BitVec 8))(?H (_ BitVec 8))(?I (_ BitVec 8))(?J (_ BitVec 8)))(=>(and (and (and (and (f_s3 ?A ?B ?E ?F)(= ?G ?E))(f_sf ?H ?G ?I ?J))(= ?I ?C))(= ?F ?D)) (f_sf ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8))(?E (_ BitVec 8))(?F (_ BitVec 8))(?G (_ BitVec 8))(?H (_ BitVec 8)))(=>(and (and (f_s3 ?E ?F ?G ?H)(= ?B ?G))(and (= ?A ?C) (= ?B ?D))) (f_s1 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8))(?E (_ BitVec 8))(?F (_ BitVec 8))(?G (_ BitVec 8))(?H (_ BitVec 8))(?I (_ BitVec 8))(?J (_ BitVec 8)))(=>(and (and (and (and (main_s2 ?A ?B ?E ?F)(= ?G ?F))(f_sf ?H ?G ?I ?J))(= ?I ?C))(= ?F ?D)) (main_s3 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 8))(?B (_ BitVec 8))(?C (_ BitVec 8))(?D (_ BitVec 8))(?E (_ BitVec 8))(?F (_ BitVec 8))(?G (_ BitVec 8))(?H (_ BitVec 8)))(=>(and (and (main_s2 ?E ?F ?G ?H)(= ?B ?H))(and (= ?A ?C) (= ?B ?D))) (f_s1 ?A ?B ?C ?D))))

(check-sat)
