
(set-logic HORN)

(declare-datatype XS ( (XS_empty)
                       (XS_cons (XS_head Int) (XS_tail XS)) ))

(define-fun XS_len ((x XS)) Int (- (_size x) 1))

(declare-fun p1 (XS XS XS) Bool)
(declare-fun p2 (XS XS XS XS XS) Bool)
(declare-fun p3 (XS XS XS XS) Bool)
(declare-fun p4 (XS XS XS) Bool)

; p1("Hello", "World", "")
(assert (p1 (XS_cons 72 (XS_cons 101 (XS_cons 108 (XS_cons 108 (XS_cons 111 XS_empty)))))
            (XS_cons 87 (XS_cons 111 (XS_cons 114 (XS_cons 108 (XS_cons 100 XS_empty)))))
            XS_empty))

; ... -> p2("Hello", "", "olleH", "World", "")
(assert (forall ((x XS) (y XS) (z XS))
                (=> (p1 x y z) (p2 x x XS_empty y z))))
(assert (forall ((x XS) (y XS) (z XS) (t XS) (c Int) (s XS))
                (=> (p2 x (XS_cons c t) s y z) (p2 x t (XS_cons c s) y z))))

; ... -> p3("Hello", "", "World", "HelloWorld")
(assert (forall ((x XS) (y XS) (z XS) (t XS))
                (=> (p2 x XS_empty t y z) (p3 x t y y))))
(assert (forall ((x XS) (y XS) (z XS) (t XS) (c Int))
                (=> (p3 x (XS_cons c t) y z) (p3 x t y (XS_cons c z)))))

(assert (forall ((x XS) (y XS) (z XS))
                (=> (p3 x XS_empty y z)
                    (p4 x y z))))

; p4(x, y, z) -> z[2] = 87
(assert (forall ((x XS) (y XS) (z XS))
                (=> (p4 x y z) (= 87 (XS_head (XS_tail (XS_tail z)))))))

(check-sat)
(get-model)

