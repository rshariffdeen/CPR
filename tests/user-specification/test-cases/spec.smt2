(declare-fun output!i32!obs!0 () (Array (_ BitVec 32) (_ BitVec 8) ) )
(declare-fun choice!rvalue!L9!0!x () (Array (_ BitVec 32) (_ BitVec 8) ) )
(assert (let (( ?B1 (concat  (select  output!i32!obs!0  (_ bv3 32) ) (concat  (select  output!i32!obs!0  (_ bv2 32) ) (concat  (select  output!i32!obs!0  (_ bv1 32) ) (select  output!i32!obs!0  (_ bv0 32) ) ) ) ))) ( let (( ?B2 (concat  (select  choice!rvalue!L9!0!x  (_ bv3 32) ) (concat  (select  choice!rvalue!L9!0!x  (_ bv2 32) ) (concat  (select  choice!rvalue!L9!0!x (_ bv1 32) ) (select  choice!rvalue!L9!0!x  (_ bv0 32) ) ) ) ))) (= true (= ?B1 (bvmul ?B2 ?B2) )) ) ))

