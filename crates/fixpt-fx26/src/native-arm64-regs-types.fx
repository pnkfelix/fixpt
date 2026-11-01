;;; The types of the compiler of register code to arm64 written in FX-26
;;; (`native-arm64-regs.fx` and `native-arm64-regs-ops.fx`), and the
;;; signatures of what it is given of `native.fx`'s assembler and of the
;;; arm64 machine's register code (`native-arm64-regs-layout.fx`,
;;; generated), and its own as its clients use it: a module file of no
;;; state (`TODO.md` §68), as `native-x64-types.fx` is for x86_64.

(define-effect ar-assembles (maxeff (read @globals) (read @k) (write @k) (alloc @k)))
(define-effect ar-lists (maxeff (read @globals) (read @k) (alloc @k) spin))
;; The compile's arrays; the instructions it gives.
(define-type ar-ints (arrayof int @k))
(define-type ar-bools (arrayof bool @k))
(define-type ar-out (listof int @k))
;; Pairs of ints: a next slice's stub and where it goes back to; a poll's
;; resume point's field and its code's label.
(define-type ar-pairs (listof (productof (1 int) (2 int)) @k))
;; Register code's polls that may leave the machine: each one's way out,
;; where it goes on, its code back, the registers it keeps, its resume
;; point's field, the word's field count, and its frame's size (-1 for a
;; leaf, whose link is kept too).
(define-type ar-poll-list
  (listof (productof (1 int) (2 int) (3 int) (4 int) (5 int) (6 int) (7 int)) @k))
;; A register word's machine code: its instructions, where each cell's
;; resume point is (-1 for none), and why it cannot be compiled ("" if it
;; can).
(define-type ar-regs-assembled (productof (1 ar-out) (2 ar-out) (3 string)))

;;; ------------------------------------------------------------ signatures

;; What register code uses of `native.fx`'s assembler: its instructions,
;; labels and traps, and the machine sequences the two share.
(define-type native-arm64-asm-sig
  (moduleof (val n-long (ref bool @k))
            (val n-trap-common (ref int @k))
            (val n-exit-common (ref int @k))
            (val n-here (subr (maxeff (read @globals) (read @k)) () int))
            (val n-e (subr (maxeff ar-assembles spin) (int) unit))
            (val n-es (subr (maxeff ar-assembles spin) (ar-out) unit))
            (val n-label (subr (maxeff ar-assembles spin) () int))
            (val n-bind (subr (maxeff ar-assembles spin) (int) unit))
            (val n-b (subr (maxeff ar-assembles spin) (int) unit))
            (val n-bl (subr (maxeff ar-assembles spin) (int) unit))
            (val n-b-cond (subr (maxeff ar-assembles spin) (int int) unit))
            (val n-cbz (subr (maxeff ar-assembles spin) (int int) unit))
            (val n-cbnz (subr (maxeff ar-assembles spin) (int int) unit))
            (val n-trap-if (subr (maxeff ar-assembles spin) (int int int) unit))
            (val n-flush-stubs (subr (maxeff ar-assembles spin) () unit))
            (val n-label-at (subr (maxeff (read @globals) (read @k)) (int) int))
            (val n-branches-fit? (subr (maxeff (read @globals) (read @k) spin) () bool))
            (val n-finish (subr (maxeff ar-assembles spin) () ar-out))
            (val n-reset (subr (maxeff ar-assembles spin) () unit))
            (val n-field-off (subr pure (int) int))
            (val n-card-mark (subr (maxeff ar-assembles spin) (int int) unit))
            (val n-bump-writes (subr (maxeff ar-assembles spin) () unit))
            (val n-enter-cur (subr (maxeff ar-assembles spin) (int) unit))
            (val n-fp-encode (subr (maxeff ar-assembles spin) (int) unit))
            (val n-fp-decode (subr (maxeff ar-assembles spin) (int) unit))
            (val n-value (subr (maxeff ar-assembles spin) (int int) unit))
            (val n-push-return (subr (maxeff ar-assembles spin) () unit))
            (val n-pass-mark (subr (maxeff ar-assembles spin) (int int) unit))
            (val n-save (subr (maxeff ar-assembles spin) () unit))
            (val n-load (subr (maxeff ar-assembles spin) () unit))
            (val n-ds-limit (subr (maxeff ar-assembles spin) () unit))
            (val n-rs-limit (subr (maxeff ar-assembles spin) () unit))))

;; What `native-arm64-regs.fx` is given of the arm64 machine's register
;; code (`native-arm64-regs-layout.fx`, generated).
(define-type native-arm64-regs-layout-sig
  (moduleof (val a-result int)
            (val a-x12 int)
            (val a-lr int)
            (val a-xzr int)
            (val a-sp int)
            (val a-st-leaf-link int)
            (val a-st-pure int)
            (val a-st-top int)
            (val a-st-alloc-limit int)
            (val a-st-words int)
            (val a-st-regions int)
            (val a-st-reserve int)
            (val a-null int)
            (val a-unspecified int)
            (val a-char0 int)
            (val a-f32-0 int)
            (val a-tag-header int)
            (val a-kind-extension int)
            (val a-region-slots int)
            (val a-regs int)
            (val a-trap-prim int)
            (val a-operands (subr pure (int) int))
            (val a-prim-name (subr pure (int) string))
            (val a-prim-number (subr pure (string) int))
            (val a-never-collects? (subr pure (int) bool))
            (val a-shape-kind (subr pure (string int) int))))

;; What the conductor names of the register code's compiler, for Rust.
(define-type native-arm64-regs-sig
  (moduleof (val native-assemble-arm64-regs
                 (subr (maxeff ar-assembles spin) (tword int int int) ar-regs-assembled))
            (val native-adapter-arm64 (subr (maxeff ar-assembles spin) (int int) ar-out))))

;; What `native-arm64-regs.fx` uses of `native-arm64-regs-ops.fx`: the
;; helpers the two share, register code's fast paths, and what it does
;; inline.
(define-type native-arm64-regs-ops-sig
  (moduleof (val ar-eq int)
            (val ar-ne int)
            (val ar-hs int)
            (val ar-lo int)
            (val ar-vs int)
            (val ar-hi int)
            (val ar-ls int)
            (val ar-ge int)
            (val ar-lt int)
            (val ar-gt int)
            (val ar-reg (subr pure (int) int))
            (val ar-bits (subr pure (tword int) int))
            (val ar-header (subr (maxeff (read @globals) spin) (int int) int))
            (val ar-sub-const (subr (maxeff ar-assembles spin) (int int int) unit))
            (val ar-add-const (subr (maxeff ar-assembles spin) (int int int) unit))
            (val ar-pool (subr (maxeff ar-assembles spin) (int) unit))
            (val ar-cell (subr (maxeff ar-assembles spin) (int int int) unit))
            (val ar-constant (subr (maxeff ar-assembles spin) (int tword int int) unit))
            (val ar-field-of (subr (maxeff ar-assembles spin) (int int int) unit))
            (val ar-slot (subr (maxeff ar-assembles spin) (int int bool) unit))
            (val ar-ip-at (subr (maxeff ar-assembles spin) (int) unit))
            (val ar-push-regs (subr (maxeff ar-assembles spin) (int) unit))
            (val ar-pure-call3 (subr (maxeff ar-assembles spin) (int int int) unit))
            (val ar-pure-call (subr (maxeff ar-assembles spin) (int int) unit))
            (val ar-int-fast (subr (maxeff ar-assembles spin) (string int int) bool))
            (val ar-shape-test (subr (maxeff ar-assembles spin) (int string int) bool))
            (val ar-inline-op (subr (maxeff ar-assembles spin) (string int int int int) unit))
            (val ar-inline-name (subr pure (int int int) string))))
