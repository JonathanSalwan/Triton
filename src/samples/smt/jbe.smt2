(set-logic QF_AUFBV)

(declare-fun zf () (_ BitVec 1))
(declare-fun cf () (_ BitVec 1))

(assert (= (bvor zf cf) (_ bv1 1)))

(check-sat)
(get-model)
