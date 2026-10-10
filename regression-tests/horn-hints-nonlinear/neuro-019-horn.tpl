(initial-predicates INV1 ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int))
  (and (= v3 v0) (= v2 v1) (= v5 (* 2 v4)) (>= v1 0) (>= v4 0)
       (or (<= v1 (* 2 v0)) (<= v1 0))
       (or (<= v4 v3) (<= v4 0))))
