;;; The signatures of the native convention's compiler to arm64 written in
;;; FX-26 (`native-direct-arm64.fx` and the files beside it), as its
;;; modules use each other: a module file of no state (`TODO.md` §68). The
;;; types they share with x86_64's (`da-assembles`, `da-bytes`, the
;;; representations' `nr-…`) are that compiler's
;;; (`native-direct-x64-types.fx`), which each file includes beside this.

(hide (define direct-types (load-module "fx26:native-direct-x64-types.fx")))
(import direct-types (effect da-assembles da-reads))
(import direct-types (type da-bytes da-ints da-bools da-strings da-pairs da-mark da-on-reg))
(import direct-types (type nr-cells nr-in-out nr-stepped nr-raw-op))
(import direct-types (type dr-int-slow dp-edge dp-poll dx-made))

;;; ------------------------------------------------------------ signatures

;; The assembler and the machine sequences the compiler's files share
;; (`native-direct-arm64-asm.fx`): `direct.rs`'s `Asm`, and its free
;; functions of no procedure. A branch's kind (`Fix`): a condition's number
;; for `b.cond`, `ada-fix-b`, `ada-fix-bl`, or `ada-fix-adr` plus a register
;; for `adr`.
(define-type native-direct-arm64-asm-sig
  (moduleof (val ada-c-eq int)
            (val ada-c-ne int)
            (val ada-c-hs int)
            (val ada-c-lo int)
            (val ada-c-mi int)
            (val ada-c-vs int)
            (val ada-c-vc int)
            (val ada-c-hi int)
            (val ada-c-ls int)
            (val ada-c-ge int)
            (val ada-c-lt int)
            (val ada-c-gt int)
            (val ada-c-le int)
            (val ada-not (subr pure (int) int))
            (val ada-fix-b int)
            (val ada-fix-bl int)
            (val ada-fix-adr int)
            (val ada-bits (subr pure (int) int))
            (val ada-reset (subr da-assembles (int) unit))
            (val ada-here (subr da-reads () int))
            (val ada-e (subr da-assembles (int) unit))
            (val ada-es (subr da-assembles (da-bytes) unit))
            (val ada-word-at (subr da-reads (int) int))
            (val ada-set-word! (subr da-assembles (int int) unit))
            (val ada-label (subr da-assembles () int))
            (val ada-bind (subr da-assembles (int) unit))
            (val ada-label-at (subr da-reads (int) int))
            (val ada-used? (subr da-reads (int) bool))
            (val ada-to (subr da-assembles (int int) unit))
            (val ada-b (subr da-assembles (int) unit))
            (val ada-bl (subr da-assembles (int) unit))
            (val ada-bc (subr da-assembles (int int) unit))
            (val ada-adr (subr da-assembles (int int) unit))
            (val ada-too-far! (subr da-assembles () unit))
            (val ada-finish (subr da-assembles () da-bytes))
            (val ada-mark (subr da-reads () da-mark))
            (val ada-rewind (subr da-assembles (da-mark) unit))
            (val ada-fail (subr da-assembles (string) unit))
            (val ada-err (subr da-reads () string))
            (val ada-ok? (subr da-reads () bool))
            (val ada-co (subr pure (int int int) int))
            (val ada-callout (subr da-assembles (int) int))
            (val ada-callouts (subr da-assembles () da-bytes))
            (val ada-stub (subr da-assembles (int int) unit))
            (val ada-trap (subr da-assembles (int int) unit))
            (val ada-place-stubs (subr da-assembles () unit))
            (val ada-imm (subr da-assembles (int int) unit))
            (val ada-ld (subr da-assembles (int int int) unit))
            (val ada-sto (subr da-assembles (int int int) unit))
            (val ada-mov (subr da-assembles (int int) unit))
            (val ada-push-frame (subr da-assembles (int int) unit))
            (val ada-pop-frame (subr da-assembles (int) unit))
            (val ada-leave (subr da-assembles () unit))
            (val ada-resume (subr da-assembles () unit))
            (val ada-call-out (subr da-assembles (int) unit))
            (val ada-ldr-field (subr da-assembles (int int) unit))
            (val ada-callout-loads-made (subr da-assembles () da-pairs))
            (val ada-callout-field (subr da-assembles (int int) unit))
            (val ada-trap-set (subr da-assembles () unit))
            (val ada-args1 (subr da-assembles (int) da-bytes))
            (val ada-args2 (subr da-assembles (int int) da-bytes))
            (val ada-args3 (subr da-assembles (int int int) da-bytes))
            (val ada-pure-call (subr da-assembles (int da-bytes int) unit))
            (val ada-check-fixnum (subr da-assembles (int int) unit))
            (val ada-card-mark (subr da-assembles (int int int int) unit))
            (val ada-field-off (subr pure (int) int))
            (val ada-header (subr pure (int int int) int))
            (val ada-trailer (subr pure (int) int))
            (val ada-fixnum (subr pure (int) int))
            (val ada-continuation-code (subr da-assembles (int) da-bytes))
            (val ada-targets (subr da-assembles () da-bools))))

;;; ------------------------------------------------------------ raw values

;; Raw values and the operations native code does on them
;; (`native-direct-arm64-raw.fx`): `direct.rs`'s `box_reg` to `wrap_small`
;; and `IntSlow`, step for step, each `adr-` and its Rust name. What makes
;; a call-out numbers it (`ada-callout`); what traps, a stub (`ada-trap`).
;; An `int` operation's slow path is x86_64's `dr-int-slow` (its `y` -1
;; with an immediate). `adr-compare` is `raw_compare`, -1 for none.
(define-type native-direct-arm64-raw-sig
  (moduleof (val adr-box-reg (subr da-assembles (int bool) unit))
            (val adr-unbox-reg (subr da-assembles (int) unit))
            (val adr-unbox-f64 (subr da-assembles (int) unit))
            (val adr-raw-f64-mark int)
            (val adr-take-raw-f64 (subr da-assembles () unit))
            (val adr-raw-return (subr da-assembles () unit))
            (val adr-raw-entry-skip (subr da-assembles (int) int))
            (val adr-box-f64 (subr da-assembles (int) unit))
            (val adr-unbox-to (subr da-assembles (int int) unit))
            (val adr-convert (subr da-assembles (da-bytes int int) unit))
            (val adr-f64-of-int (subr da-assembles (int) unit))
            (val adr-int-of-f64 (subr da-assembles (int) unit))
            (val adr-f64-fast (subr da-assembles (string int) unit))
            (val adr-f32-fast (subr da-assembles (string int) bool))
            (val adr-compare (subr pure (bool string) int))
            (val adr-raw-fast (subr da-assembles (bool string int) unit))
            (val adr-wrap-small (subr da-assembles (bool int) unit))
            (val adr-int-slow (subr da-assembles (dr-int-slow) unit))))

;;; ------------------------------------------------------------ the heap's

;; Flat arrays, suffix refs, bytevectors and shapes in line
;; (`native-direct-arm64-flat.fx`): `direct.rs`'s `flat_count` to
;; `flat_set`, `box_bits` and `shape_fast`, step for step, each `adf-` and
;; its Rust name, its arguments in the Rust order.
(define-type native-direct-arm64-flat-sig
  (moduleof (val adf-flat-count (subr da-assembles (int int) unit))
            (val adf-flat-element (subr da-assembles (int int int) unit))
            (val adf-flat-ref (subr da-assembles (int int) unit))
            (val adf-box-bits (subr da-assembles (int) unit))
            (val adf-suffix-owner (subr da-assembles (int int) unit))
            (val adf-suffix-writable (subr da-assembles (int int) unit))
            (val adf-suffix-store (subr da-assembles (int int bool int) unit))
            (val adf-blobref-index (subr da-assembles (int int int) unit))
            (val adf-flat-variant (subr da-assembles (int int int) unit))
            (val adf-blobref-at (subr da-assembles (int int) unit))
            (val adf-suffix-step (subr da-assembles (int int) unit))
            (val adf-suffix-fits (subr da-assembles (int int) unit))
            (val adf-suffix-length (subr da-assembles (int int) unit))
            (val adf-suffix-index (subr da-assembles (int) unit))
            (val adf-flat-tag (subr da-assembles (int int) unit))
            (val adf-suffix-get (subr da-assembles (int bool int) unit))
            (val adf-suffix-set (subr da-assembles (int int) unit))
            (val adf-bytes-set (subr da-assembles (int int) unit))
            (val adf-flat-set (subr da-assembles (int int bool) unit))
            (val adf-shape-fast (subr da-assembles (string int) bool))))

;;; ------------------------------------------------------------ the procedure

;; What `procedure` places after the code, as x86_64's are (`dp-edge` and
;; the rest, `native-direct-x64-types.fx`).
(define-type adp-edge-list (listof dp-edge @k))
(define-type adp-int-slow-list (listof dr-int-slow @k))
(define-type adp-poll-list (listof dp-poll @k))
(define-type adp-overflow-list (listof (productof (1 int) (2 int) (3 int)) @k))
(define-type adp-cell-slow-list (listof (productof (1 int) (2 int) (3 int)) @k))
(define-type adp-foreign-list (listof (productof (1 int) (2 int) (3 int) (4 bool)) @k))

;; The procedure being compiled, its analysis, its fields and the version
;; being made (`native-direct-arm64-proc.fx`), as its other files use it:
;; x86_64's (`native-direct-x64-proc.fx`), each `adp-` for `dp-`.
(define-type native-direct-arm64-proc-sig
  (moduleof (val adp-errors (ref da-strings @k))
            (val adp-kind (ref da-ints @k))
            (val adp-a (ref da-ints @k))
            (val adp-b (ref da-ints @k))
            (val adp-c (ref da-ints @k))
            (val adp-info-captures (ref int @k))
            (val adp-info (ref int @k))
            (val adp-cells (ref nr-cells @k))
            (val adp-n (ref int @k))
            (val adp-starts (ref da-ints @k))
            (val adp-si-of (subr da-reads (int) int))
            (val adp-ns (subr da-reads () int))
            (val adp-start (subr da-reads (int) int))
            (val adp-fix (subr da-reads (int) int))
            (val adp-fix? (subr da-reads (int) bool))
            (val adp-op (subr da-reads (int) int))
            (val adp-o (subr da-reads (int int) int))
            (val adp-ob (subr da-reads (int int) int))
            (val adp-oid (subr da-reads (int int) int))
            (val adp-ofix? (subr da-reads (int int) bool))
            (val adp-oimm? (subr da-reads (int int) bool))
            (val adp-branch-to (subr da-reads (int) int))
            (val adp-branch? (subr pure (int) bool))
            (val adp-bit? (subr pure (int int) bool))
            (val adp-bit (subr pure (int) int))
            (val adp-decline (subr da-assembles (string) unit))
            (val adp-frame (ref int @k))
            (val adp-calls (ref bool @k))
            (val adp-captures (ref bool @k))
            (val adp-back-to (ref da-bools @k))
            (val adp-target (ref da-bools @k))
            (val adp-framed (ref da-bools @k))
            (val adp-raw (ref da-bools @k))
            (val adp-values (ref int @k))
            (val adp-params (ref int @k))
            (val adp-callees (ref da-ints @k))
            (val adp-slot-off (ref da-ints @k))
            (val adp-unmapped (ref bool @k))
            (val adp-size (ref int @k))
            (val adp-self-slot (ref int @k))
            (val adp-clo-slot (ref int @k))
            (val adp-live-out (ref da-ints @k))
            (val adp-raw-refs (ref da-bools @k))
            (val adp-live (ref da-ints @k))
            (val adp-has-int (ref bool @k))
            (val adp-map-word (subr da-reads (int) int))
            (val adp-fields (ref da-bytes @k))
            (val adp-field (subr da-assembles (int) int))
            (val adp-myself int)
            (val adp-code-of (subr pure (int) int))
            (val adp-const-of (subr pure (int) int))
            (val adp-cell-of (subr pure (int) int))
            (val adp-closure-of (subr pure (int int) int))
            (val adp-callout-of (subr pure (int) int))
            (val adp-labels-g (ref da-ints @k))
            (val adp-labels-f (ref da-ints @k))
            (val adp-fast (ref bool @k))
            (val adp-reps-in (ref da-ints @k))
            (val adp-reps-out (ref da-ints @k))
            (val adp-src (ref int @k))
            (val adp-pending (ref int @k))
            (val adp-bound-cell (ref int @k))
            (val adp-bound-writes (ref int @k))
            (val adp-map-stored? (ref bool @k))
            (val adp-map-stored (ref int @k))
            (val adp-held (ref da-ints @k))
            (val adp-entered (ref da-bools @k))
            (val adp-si (ref int @k))
            (val adp-entry-checked (ref int @k))
            (val adp-resume-at (ref int @k))
            (val adp-uses-resume (ref bool @k))
            (val adp-label (subr da-reads (int) int))
            (val adp-label-g (subr da-reads (int) int))
            (val adp-in (subr da-reads (int) int))
            (val adp-out (subr da-reads (int) int))
            (val adp-edges (ref adp-edge-list @k))
            (val adp-joinable (subr da-reads (int) int))
            (val adp-edge (subr da-assembles (int int) int))
            (val adp-result-live? (subr da-reads (int) bool))
            (val adp-branch-on (subr da-reads (int) int))
            (val adp-int-slows (ref adp-int-slow-list @k))
            (val adp-polls (ref adp-poll-list @k))
            (val adp-overflows (ref adp-overflow-list @k))
            (val adp-cell-slows (ref adp-cell-slow-list @k))
            (val adp-foreign (ref adp-foreign-list @k))
            (val adp-begin (subr da-assembles (string (listof da-bytes @k) da-strings) unit))
            (val adp-analyse (subr da-assembles () unit))))

;; The primitives', control's and call-outs' (`native-direct-arm64-prims.fx`):
;; the instruction at cell `i` (and its `op`, for those of more than one).
(define-type native-direct-arm64-prims-sig
  (moduleof (val adq-control (subr da-assembles (int) unit))
            (val adq-prim12 (subr da-assembles (int int) unit))
            (val adq-prim3 (subr da-assembles (int) unit))
            (val adq-callouts (subr da-assembles (int int) unit))))

;;; ------------------------------------------------------------ the instructions

;; The instructions that are not primitives' or call-outs'
;; (`native-direct-arm64-ops.fx`), each of its cell (and its `op`, for
;; those of more than one); what `RESULT` and REG1…REG8 hold of the frame
;; (`held`), as a version begins and before each instruction.
(define-type native-direct-arm64-ops-sig
  (moduleof (val ado-slot (subr da-reads (int) int))
            (val ado-vargs (subr da-assembles (int) unit))
            (val ado-const (subr da-assembles (int) unit))
            (val ado-global (subr da-assembles (int) unit))
            (val ado-global-guard (subr da-assembles (int) unit))
            (val ado-setglbl (subr da-assembles (int) unit))
            (val ado-lexical (subr da-assembles (int) unit))
            (val ado-reg (subr da-assembles (int) unit))
            (val ado-setreg (subr da-assembles (int) unit))
            (val ado-movereg (subr da-assembles (int) unit))
            (val ado-save (subr da-assembles (int) unit))
            (val ado-pop (subr da-assembles (int) unit))
            (val ado-stack (subr da-assembles (int) unit))
            (val ado-setstk (subr da-assembles (int) unit))
            (val ado-load (subr da-assembles (int) unit))
            (val ado-store (subr da-assembles (int) unit))
            (val ado-op1 (subr da-assembles (int) unit))
            (val ado-op2 (subr da-assembles (int int) unit))
            (val ado-field (subr da-assembles (int) unit))
            (val ado-setfield (subr da-assembles (int) unit))
            (val ado-invoke (subr da-assembles (int int) unit))
            (val ado-invokeself (subr da-assembles (int) unit))
            (val ado-return (subr da-assembles (int) unit))
            (val ado-branch (subr da-assembles (int int) unit))
            (val ado-held-version (subr da-assembles (bool) unit))
            (val ado-held-step (subr da-assembles (int int int) unit))))

;;; ------------------------------------------------------------ the compiler

;; What the conductor names of the compiler, for Rust
;; (`native-direct-arm64.fx`): a procedure's code, as x86_64's
;; `native-compile-x64-proc` gives it (`dx-made`).
(define-type native-direct-arm64-sig
  (moduleof (val native-compile-arm64-proc
                 (subr da-assembles (string (listof da-bytes @k) da-strings) dx-made))))
