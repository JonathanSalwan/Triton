(set-logic QF_AUFBV)

(declare-fun SymVar_0 () (_ BitVec 64))
(declare-fun SymVar_1 () (_ BitVec 64))
(declare-fun SymVar_2 () (_ BitVec 64))

(assert (= (_ bv16 64) (bvand (_ bv16 64) (bvxor SymVar_0 (bvxor SymVar_1 SymVar_2)))))

(check-sat)
(get-model)
