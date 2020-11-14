(declare-const obs!0 (_ BitVec 32))
(assert (and (or (= false (bvsle  obs!0  (_ bv255 32))) (bvsle (_ bv0 32) obs!0))  (or (= false (= (_ bv0 32) obs!0))  (bvsle (_ bv0 32) obs!0))))