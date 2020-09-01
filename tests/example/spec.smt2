(declare-fun res () (Array (_ BitVec 32) (_ BitVec 8) ) )
(assert (= false (bvsle (concat  (select  res (_ bv3 32) ) (concat  (select  res (_ bv2 32) ) (concat  (select  res (_ bv1 32) ) (select  res (_ bv0 32) ) ) ) ) (_ bv5 32)) ))


