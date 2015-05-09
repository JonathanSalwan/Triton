(set-logic QF_AUFBV)

(define-fun TRUE () (_ BitVec 1) (_ bv1 1))
(define-fun FALSE () (_ BitVec 1) (_ bv0 1))

(declare-fun zf () (_ BitVec 1))
(declare-fun of () (_ BitVec 1))
(declare-fun sf () (_ BitVec 1))

(assert (= (bvor (bvxor sf of) zf) FALSE))

(check-sat)
(get-model)
