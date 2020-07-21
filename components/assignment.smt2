(declare-const lhole_left (_ BitVec 32))
(declare-const rhole_right (_ BitVec 32))
(declare-const rreturn (_ BitVec 32))
(assert (and (= rreturn rhole_right) (= lhole_left rhole_right)))