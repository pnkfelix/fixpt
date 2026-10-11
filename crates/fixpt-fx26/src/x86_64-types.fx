;;; The types of `x86_64.fx`, and the signature of its module as its
;;; clients use it: a module file of no state, which it loads, and so may
;;; its clients (`TODO.md` §68).

;; What the encoders do: read the encoders, make their bytes (reading the
;; ones they join), and count down.
(define-effect x86-encodes (maxeff (alloc @k) (read @k) (read @globals) spin))
;; An instruction's bytes, in order.
(define-type x86-bytes (listof int @k))
;; The encoders of one to six operands.
(define-type x86-op1 (subr x86-encodes (int) x86-bytes))
(define-type x86-op2 (subr x86-encodes (int int) x86-bytes))
(define-type x86-op3 (subr x86-encodes (int int int) x86-bytes))
(define-type x86-op4 (subr x86-encodes (int int int int) x86-bytes))
(define-type x86-op5 (subr x86-encodes (int int int int int) x86-bytes))
(define-type x86-op6 (subr x86-encodes (int int int int int int) x86-bytes))

;;; ------------------------------------------------------------ signatures

;; What `native-x64.fx` uses of the encoders (`TODO.md` §68).
(define-type x86-64-sig
  (moduleof (val x86-mov x86-op2)
            (val x86-load x86-op3)
            (val x86-load-ix x86-op5)
            (val x86-store x86-op3)
            (val x86-lea x86-op3)
            (val x86-lea-ix x86-op5)
            (val x86-mov-imm x86-op2)
            (val x86-alu x86-op3)
            (val x86-alu-imm x86-op3)
            (val x86-alu-rm x86-op4)
            (val x86-alu-mi x86-op4)
            (val x86-test x86-op2)
            (val x86-test-imm x86-op2)
            (val x86-cmov-m x86-op4)
            (val x86-shift-imm x86-op3)
            (val x86-jmp x86-op1)
            (val x86-jcc x86-op2)
            (val x86-jmp-r x86-op1)
            (val x86-jmp-m x86-op4)
            (val x86-call-m x86-op2)
            (val x86-store8-imm x86-op5)))
