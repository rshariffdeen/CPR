(declare-fun i () (Array (_ BitVec 32) (_ BitVec 8) ) )
(declare-fun size () (Array (_ BitVec 32) (_ BitVec 8) ) )
(assert
(let (( B1 (concat  (select  i (_ bv3 32) ) (concat  (select  i (_ bv2 32) ) (concat  (select  i (_ bv1 32) ) (select  i (_ bv0 32) ) ) ) )))
(let (( B2 (concat  (select  size (_ bv3 32) ) (concat  (select  size (_ bv2 32) ) (concat  (select  size (_ bv1 32) ) (select  size (_ bv0 32) ) ) ) )))
(let (( B3 (bvmul (_ bv2 32) B1)))
(= true (bvsle B3 B2 ) )
))))