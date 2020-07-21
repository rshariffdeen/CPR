(declare-const rhole_left (_ BitVec 32))
(declare-const rhole_right (_ BitVec 32))
(declare-const rreturn (_ BitVec 32))
(assert (= rreturn (bvsrem rhole_left rhole_right)))
