(declare-const lhole_argument (_ BitVec 32))
(declare-const rhole_argument (_ BitVec 32))
(declare-const rreturn (_ BitVec 32))
(assert (and (= rreturn rhole_argument)
             (= lhole_argument (bvsub  rhole_argument (_ bv1 32)))))