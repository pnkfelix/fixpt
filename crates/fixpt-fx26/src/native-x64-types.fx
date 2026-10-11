;;; The types of `native-x64.fx`, the signature of what it is given of the
;;; x86_64 machine (`native-x64-layout.fx`, generated), and its own as its
;;; clients use it: a module file of no state (`TODO.md` §68).

(define-effect x-assembles (maxeff (read @globals) (read @k) (write @k) (alloc @k)))
;; Writing the assembler's arrays, and looping; reading them to make lists.
(define-effect x-writes (maxeff (read @globals) (read @k) (write @k) spin))
(define-effect x-lists (maxeff (read @globals) (read @k) (alloc @k) spin))
;; The assembler's arrays; the bytes it gives; and those with where each
;; cell's code starts.
(define-type x-ints (arrayof int @k))
(define-type x-bools (arrayof bool @k))
(define-type x-out (listof int @k))
(define-type x-assembled (productof (1 x-out) (2 x-out)))
;; A 32-bit displacement to patch: where it is, and its label; newest first.
(define-type x-fix-list (listof (productof (1 int) (2 int)) @k))
;; Traps raised in the code being emitted, placed after it: label, code,
;; detail; newest first.
(define-type x-stub-list (listof (productof (1 int) (2 int) (3 int)) @k))

;;; ------------------------------------------------------------ signatures

;; What `native-x64.fx` uses of the x86_64 machine's registers, state and
;; traps: `native-layout-sig`'s, but for the heap's base and the fuel, which
;; have no registers here, and with the state's `#f` and `#t`.
(define-type native-x64-layout-sig
  (moduleof (val n-ip int)
            (val n-cur int)
            (val n-dsp int)
            (val n-rsp int)
            (val n-st int)
            (val n-table int)
            (val n-fp int)
            (val n-clo int)
            (val n-w int)
            (val n-x10 int)
            (val n-x11 int)
            (val n-x13 int)
            (val n-x14 int)
            (val n-x15 int)
            (val n-x16 int)
            (val n-st-base int)
            (val n-st-cur int)
            (val n-st-d int)
            (val n-st-dsp int)
            (val n-st-rsp int)
            (val n-st-table int)
            (val n-st-fuel int)
            (val n-st-callout int)
            (val n-st-ds-base int)
            (val n-st-ds-limit int)
            (val n-st-rs-limit int)
            (val n-st-fp int)
            (val n-st-clo int)
            (val n-st-resume int)
            (val n-st-trap int)
            (val n-st-exit int)
            (val n-st-cards int)
            (val n-false int)
            (val n-true int)
            (val n-prompt-mark int)
            (val n-mark-mark int)
            (val n-tag-bloblet int)
            (val n-tag-pair int)
            (val n-tag-trailer int)
            (val n-kind-word int)
            (val n-kind-closure int)
            (val n-closure-word int)
            (val n-closure-free0 int)
            (val n-word-entry int)
            (val n-word-cell0 int)
            (val n-primitives int)
            (val n-trap-type int)
            (val n-trap-overflow int)
            (val n-trap-underflow int)
            (val n-trap-field int)
            (val n-trap-no-routine int)
            (val n-trap-not-a-word int)
            (val n-trap-out-of-fuel int)
            (val n-trap-stack-overflow int)
            (val n-trap-too-deep int)
            (val n-operands (subr pure (int) int))
            (val n-control? (subr pure (int) bool))
            (val n-st-fal int)
            (val n-st-tru int)))

;; What the conductor names of the assembler, for Rust.
(define-type native-x64-sig
  (moduleof (val native-assemble-x64 (subr (maxeff x-assembles spin) (tword) x-assembled))))
