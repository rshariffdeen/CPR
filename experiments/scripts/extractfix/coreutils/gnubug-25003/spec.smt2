(declare-fun initial_read () (Array (_ BitVec 32) (_ BitVec 8) ) )
(declare-fun start () (Array (_ BitVec 32) (_ BitVec 8) ) )
(assert
(let (( B1 (concat  (select  initial_read (_ bv3 32) ) (concat  (select  initial_read (_ bv2 32) ) (concat  (select  initial_read (_ bv1 32) ) (select  initial_read (_ bv0 32) ) ) ) )))
(let (( B2 (concat  (select  start (_ bv3 32) ) (concat  (select  start (_ bv2 32) ) (concat  (select  start (_ bv1 32) ) (select  start (_ bv0 32) ) ) ) )))
(And (Or (Not (Eq false
                   (Eq 18446744073709551615
                        B1)))
          (Ule 0
               (Sub  B1
                     B2)))
      (Or (Not (And (Eq 18446744073709551615
                         B1)
                    (Ult  B2
                         18446744073709551615)))
          (Ule 0
               (Sub  B1
                     B2))))
))))