(set-logic QF_AUFBV)

(declare-fun SymVar_0 () (_ BitVec 32))

(assert (= (bvsub SymVar_0 ((_ sign_extend 0) (_ bv4 32))) (_ bv0 32)))

(check-sat)
(get-model)
