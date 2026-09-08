(initial-predicates inv
  ((a (Array Int Int)) (x Int))
  (= (select a 0) 42)
  (= (select (store a 0 x) 0) x)
)
