(set-info :origin "Bit-vector version of NTS benchmark")

(set-logic HORN)

(declare-fun main_sf ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun main_s3 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun main_s1 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun main_s2 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun f_s1 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun f_s2 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun f_sf ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)
(declare-fun f_s3 ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)

(assert(forall((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32))(?E (_ BitVec 32))(?F (_ BitVec 32)))(=>(and (main_s3 ?A ?B ?E ?F)(and (= ?E (_ bv91 32)) (and (= ?E ?C) (= ?F ?D)))) (main_sf ?A ?B ?C ?D))))

(assert(not (exists((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32))(?E (_ BitVec 32))(?F (_ BitVec 32)))(and (main_s3 ?A ?B ?C ?D)(and (not (= ?C (_ bv91 32))) (and (= ?C ?E) (= ?D ?F)))))))

(assert(forall((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32))(?E (_ BitVec 32))(?F (_ BitVec 32)))(=>(and (main_s1 ?A ?B ?E ?F)(and (bvsle ?D (_ bv100 32)) (= ?E ?C))) (main_s2 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32)))(=>(and (= ?A ?C) (= ?B ?D)) (main_s1 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32))(?E (_ BitVec 32))(?F (_ BitVec 32)))(=>(and (f_s1 ?A ?B ?E ?F)(and (and (bvsle ?F (_ bv100 32)) (= ?C (bvadd ?F (_ bv11 32)))) (= ?F ?D))) (f_s2 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32))(?E (_ BitVec 32))(?F (_ BitVec 32)))(=>(and (f_s1 ?A ?B ?E ?F)(and (and (bvsgt ?F (_ bv100 32)) (= ?C (bvsub ?F (_ bv10 32)))) (= ?F ?D))) (f_sf ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32))(?E (_ BitVec 32))(?F (_ BitVec 32))(?G (_ BitVec 32))(?H (_ BitVec 32))(?I (_ BitVec 32))(?J (_ BitVec 32)))(=>(and (and (and (and (f_s2 ?A ?B ?E ?F)(= ?G ?E))(f_sf ?H ?G ?I ?J))(= ?I ?C))(= ?F ?D)) (f_s3 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32))(?E (_ BitVec 32))(?F (_ BitVec 32))(?G (_ BitVec 32))(?H (_ BitVec 32)))(=>(and (and (f_s2 ?E ?F ?G ?H)(= ?B ?G))(and (= ?A ?C) (= ?B ?D))) (f_s1 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32))(?E (_ BitVec 32))(?F (_ BitVec 32))(?G (_ BitVec 32))(?H (_ BitVec 32))(?I (_ BitVec 32))(?J (_ BitVec 32)))(=>(and (and (and (and (f_s3 ?A ?B ?E ?F)(= ?G ?E))(f_sf ?H ?G ?I ?J))(= ?I ?C))(= ?F ?D)) (f_sf ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32))(?E (_ BitVec 32))(?F (_ BitVec 32))(?G (_ BitVec 32))(?H (_ BitVec 32)))(=>(and (and (f_s3 ?E ?F ?G ?H)(= ?B ?G))(and (= ?A ?C) (= ?B ?D))) (f_s1 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32))(?E (_ BitVec 32))(?F (_ BitVec 32))(?G (_ BitVec 32))(?H (_ BitVec 32))(?I (_ BitVec 32))(?J (_ BitVec 32)))(=>(and (and (and (and (main_s2 ?A ?B ?E ?F)(= ?G ?F))(f_sf ?H ?G ?I ?J))(= ?I ?C))(= ?F ?D)) (main_s3 ?A ?B ?C ?D))))

(assert(forall((?A (_ BitVec 32))(?B (_ BitVec 32))(?C (_ BitVec 32))(?D (_ BitVec 32))(?E (_ BitVec 32))(?F (_ BitVec 32))(?G (_ BitVec 32))(?H (_ BitVec 32)))(=>(and (and (main_s2 ?E ?F ?G ?H)(= ?B ?H))(and (= ?A ?C) (= ?B ?D))) (f_s1 ?A ?B ?C ?D))))

(check-sat)
