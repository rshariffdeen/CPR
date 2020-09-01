(declare-fun res!0 () (Array (_ BitVec 32) (_ BitVec 8) ) )
(assert (= false (bvsle (concat  (select  res!0 (_ bv3 32) ) (concat  (select  res!0 (_ bv2 32) ) (concat  (select  res!0 (_ bv1 32) ) (select  res!0 (_ bv0 32) ) ) ) ) (_ bv5 32)) ))


