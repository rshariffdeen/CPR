(declare-const rvalue_initial_read (_ BitVec 32))
(declare-const lvalue_initial_read (_ BitVec 32))
(declare-const rreturn (_ BitVec 32))
(declare-const lreturn (_ BitVec 32))
(assert (and (= rreturn rvalue_initial_read) (= lreturn lvalue_initial_read)))