(declare-const rvalue_size (_ BitVec 32))
(declare-const lvalue_size (_ BitVec 32))
(declare-const rreturn (_ BitVec 32))
(declare-const lreturn (_ BitVec 32))
(assert (and (= rreturn rvalue_size) (= lreturn lvalue_size)))