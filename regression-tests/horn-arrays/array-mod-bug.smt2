; Case in which Eldarica previously produced an incorrect model.
; Bug #66

(set-logic HORN)

(declare-fun pl24 ( ( Array Int ( Array Int Int ) ) Bool ) Bool)
(declare-fun pbool ( Bool ) Bool)

(assert ( pbool false ))
(assert (forall ( ( m ( Array Int ( Array Int Int ) ) ) ) ( => ( pl24 m true ) false )))
(assert (forall ( ( m ( Array Int ( Array Int Int ) ) ) ( aq Bool ) ( ar1 ( Array Int ( Array Int Int ) ) ) ( ar2 ( Array Int Int ) ) ) ( => ( and ( pbool aq ) ( = m ( store ar1 1 ( store ar2 ( + ( ite ( <= ( mod ( + 5 ( mod 5 6 ) ) 6 ) 7 ) ( mod ( + ( mod 5 6 ) ) 6 ) 2 ) ) 0 ) ) ) ) ( pl24 m aq ) )))

(check-sat)
(get-model)
