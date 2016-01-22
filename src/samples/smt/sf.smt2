(set-logic QF_AUFBV)
(declare-fun SymVar_0 () (_ BitVec 64))

(assert (= 
            ((_ extract 63 63)SymVar_0) (_ bv1 1)
        )
)

(check-sat)
(get-model)
;(get-value (SymVar_1))

