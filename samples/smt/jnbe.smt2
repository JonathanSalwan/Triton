(set-logic QF_AUFBV)

(declare-fun zf () (_ BitVec 1))
(declare-fun cf () (_ BitVec 1))

(assert (= (bvand (bvnot zf) (bvnot cf)) (_ bv1 1)))

(check-sat)
(get-model)
