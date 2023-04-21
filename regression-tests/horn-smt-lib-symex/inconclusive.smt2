(set-logic HORN)
(declare-fun
   INV_MAIN_0
   (Int
    Int)
   Bool)
(assert
 (forall
  ((HEAP$1 (Array Int Int))
   (i1 Int))
  (INV_MAIN_0 i1 (select HEAP$1 i1))))
(assert
 (forall
  ((i1 Int)
   (heap1 Int))
  (=>
   (INV_MAIN_0 i1 heap1)
   true)))
(check-sat)
(get-model)
