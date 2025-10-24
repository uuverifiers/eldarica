( declare-datatypes ( ( list_tp 0 ) )
    ( ( empty_list ( list ( hd Int ) ( tail list_tp ) ) ) ) )

(declare-fun p ( list_tp ) Bool)

(assert (p (list 0 empty_list)))

(assert (forall ( ( l list_tp ) ) (=> (p l) (p l))))

(assert (=> (p ( list 1 empty_list ) ) false))

(check-sat)
