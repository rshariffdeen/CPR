(declare-const rvalue_x (_ BitVec 32))
(declare-const rreturn (_ BitVec 32))
(assert (= rreturn (bvadd rvalue_x (_ bv1 32))))