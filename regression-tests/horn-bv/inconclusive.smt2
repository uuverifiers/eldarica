(set-logic HORN)
(declare-fun
   INV_MAIN_0
   ((_ BitVec 32)
    (_ BitVec 32))
   Bool)
(assert
 (forall
  ((HEAP$1 (Array (_ BitVec 32) (_ BitVec 32)))
   (i1 (_ BitVec 32)))
  (INV_MAIN_0 i1 (select HEAP$1 i1))))
(assert
 (forall
  ((i1 (_ BitVec 32))
   (heap1 (_ BitVec 32)))
  (=>
   (INV_MAIN_0 i1 heap1)
   true)))
(check-sat)
(get-model)
