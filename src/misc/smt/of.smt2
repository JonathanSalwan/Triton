(set-logic QF_AUFBV)

(declare-fun SymVar_0 () (_ BitVec 64))
(declare-fun SymVar_1 () (_ BitVec 64))
(declare-fun SymVar_2 () (_ BitVec 64))

(assert (= ((_ extract 63 63)(bvand (bvxor SymVar_0 (bvnot SymVar_1)) (bvxor SymVar_0 SymVar_2))) (_ bv1 1)))

(check-sat)
(get-model)
