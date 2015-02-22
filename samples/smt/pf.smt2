(set-logic QF_AUFBV)

(declare-fun SymVar_0 () (_ BitVec 64))
(define-fun parity_flag ((x!1 (_ BitVec 8))) (_ BitVec 1)
; x ^= x >> 4;
; v &= 0xf;
; return (0x6996 >> v) & 1;
((_ extract 0 0)
 (bvlshr
    (_ bv27030 16)
    ((_ zero_extend 8)
     (bvand
       (bvxor
         x!1
         (bvlshr x!1 (_ bv4 8)))
       (_ bv15 8))))))

(assert (= (parity_flag ((_ extract 7 0) SymVar_0)) (_ bv0 1)))

(check-sat)
(get-model)

