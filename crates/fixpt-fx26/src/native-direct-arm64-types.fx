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

;;; ------------------------------------------------------------ signatures

;; Something to do with the assembler, given nothing (`ada-with-labels`).
(define-type ada-thunk (subr da-assembles () unit))

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
            (val ada-continuation-code (subr da-assembles (int) da-bytes))))
