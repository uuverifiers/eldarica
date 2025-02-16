; Input that previously led to an exception during preprocessing

(set-logic HORN)
(declare-fun Inv (Real Real Real Int) Bool)

(assert (forall 
	((x Real) (y Real)(z Real) (i Int))

        (Inv x y z i)
))

(assert (forall 
	((x Real) (y Real)
	 (z Real) (i Int)
	 (x0 Real) (y0 Real)
	 (z0 Real) (i0 Int)
	)

	(=> 
                (Inv x y z i)
		(Inv x0 y0 z0 i0))
))

(assert (forall 
	((x Real) (y Real)
	 (z Real) (i Int)
	 (x0 Real) (y0 Real)
	)

	(=> 
		(and
			( Inv x y z i)
			(not 
				(and
					(<= (- 0.1) (- 10.0 y0))
                                        (<= (- 10.0 y0) 0.1)
				))
		)
		false)
))

(check-sat)