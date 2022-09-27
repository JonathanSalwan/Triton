(set-logic QF_ABV)

(define-fun ref!1 () (_ BitVec 64) (_ bv4096 64)) ; MOV operation
(define-fun ref!2 () (_ BitVec 64) (_ bv7 64)) ; Program Counter
(define-fun ref!3 () (_ BitVec 64) (_ bv50 64)) ; MOV operation
(define-fun ref!4 () (_ BitVec 64) (_ bv14 64)) ; Program Counter
(declare-fun ref!5 () (Array (_ BitVec 64) (_ BitVec 8)))
(define-fun ref!6 () (Array (_ BitVec 64) (_ BitVec 8)) (store ref!5 (bvadd (bvadd (bvadd ref!1 (bvmul ref!3 (_ bv1 64))) (_ bv0 64)) (_ bv3 64)) ((_ extract 31 24) (_ bv57005 32)))) ; Byte reference - MOV operation

(check-sat)
(get-model)
