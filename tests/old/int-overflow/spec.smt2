(declare-fun output!i32!x!0 () (Array (_ BitVec 32) (_ BitVec 8) ) )
(assert (= true (bvsle (bvmul (_ bv214748364 32) (concat  (select  output!i32!x!0 (_ bv3 32) ) (concat  (select  output!i32!x!0 (_ bv2 32) ) (concat  (select  output!i32!x!0 (_ bv1 32) ) (select  output!i32!x!0 (_ bv0 32) ) ) )) ) (_ bv2147483647 32) )))
