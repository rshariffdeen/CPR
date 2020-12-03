(declare-const lvalue_x (_ BitVec 32))
(declare-const rvalue_x (_ BitVec 32))
(declare-const rreturn (_ BitVec 32))
(assert (and (= rreturn (_ bv0 32)) (= lvalue_x (bvadd rvalue_x (_ bv1 32)))))