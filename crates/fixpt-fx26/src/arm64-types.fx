;;; The types of `arm64.fx`, its `arm64-module`, and its signature as its
;;; clients use it: a module file of no state, which it loads, and so may
;;; its clients (`TODO.md` §68).

;; What the encoders do: read the encoders, and count down.
(define-effect encodes (maxeff (read @globals) spin))
;; The encoders of two, three and four operands.
(define-type arm-op2 (subr encodes (int int) int))
(define-type arm-op3 (subr encodes (int int int) int))
(define-type arm-op4 (subr encodes (int int int int) int))
;; Instructions, in order.
(define-type arm-code (listof int @k))

;;; ------------------------------------------------------------ signatures

;; What `native.fx` uses of the encoders (`TODO.md` §68).
(define-type arm64-sig
  (moduleof (val arm-ldr-post arm-op3)
            (val arm-str-post arm-op3)
            (val arm-str-pre arm-op3)
            (val arm-ldur arm-op3)
            (val arm-stur arm-op3)
            (val arm-ldr arm-op3)
            (val arm-str arm-op3)
            (val arm-ldr-reg arm-op3)
            (val arm-stp-pre arm-op4)
            (val arm-ldp-post arm-op4)
            (val arm-stp arm-op4)
            (val arm-ldp arm-op4)
            (val arm-add-imm arm-op3)
            (val arm-sub-imm arm-op3)
            (val arm-subs-imm arm-op3)
            (val arm-cmp-imm arm-op2)
            (val arm-add arm-op3)
            (val arm-sub arm-op3)
            (val arm-adds arm-op3)
            (val arm-subs arm-op3)
            (val arm-orr arm-op3)
            (val arm-cmp arm-op2)
            (val arm-mov arm-op2)
            (val arm-and-low arm-op3)
            (val arm-tst-low arm-op2)
            (val arm-ubfx arm-op4)
            (val arm-asr-imm arm-op3)
            (val arm-lsr-imm arm-op3)
            (val arm-strb arm-op2)
            (val arm-csel arm-op4)
            (val arm-movz arm-op3)
            (val arm-mov-imm64 (subr (maxeff (alloc @k) (read @globals) spin) (int int) arm-code))
            (val arm-b (subr (maxeff (read @globals) spin) (int) int))
            (val arm-b-cond arm-op2)
            (val arm-cbz arm-op2)
            (val arm-cbnz arm-op2)
            (val arm-br (subr (maxeff (read @globals) spin) (int) int))
            (val arm-blr (subr (maxeff (read @globals) spin) (int) int))))
