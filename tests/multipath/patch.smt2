(declare-const rvalue_x (_ BitVec 32))
(declare-const rreturn Bool)
(assert (= rreturn (bvsle rvalue_x (_ bv2 32))))