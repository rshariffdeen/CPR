(declare-fun x () (Array (_ BitVec 32) (_ BitVec 8) ) )
(assert (= false (bvsle (concat  (select  x (_ bv3 32) ) (concat  (select  x (_ bv2 32) ) (concat  (select  x (_ bv1 32) ) (select  x (_ bv0 32) ) ) ) ) (_ bv5 32)) ))


