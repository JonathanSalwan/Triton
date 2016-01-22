
(set-logic QF_AUFBV)
(declare-fun Sym1 () (_ BitVec 8))

(assert (= (bvsub ((_ extract 31 0) (bvxor (bvsub ((_ sign_extend 24) ((_ extract 7 0) ((_ zero_extend 24) Sym1))) (_ bv1 32)) (_ bv85 32))) ((_ extract 31 0) ((_ sign_extend 24) ((_ extract 7 0) ((_ zero_extend 24) (_ bv49 8)))))) (_ bv0 32)))

(check-sat)
(get-model)

