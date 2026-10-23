;;; The signature of `check-logic.fx`, its `check-logic-module`, as its
;;; clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-print.fx`, `check-subtype.fx`,
;; `check-specs.fx`).
;; The types it names, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(import check-types-types (type k-sf k-sfs k-spec k-specs))
(define-type check-logic-sig
  (moduleof (val k-specs=? (subr (maxeff (read @globals) spin) (k-specs k-specs) bool))
            (val k-show-spec
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (k-spec) string))
            (val k-entails?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin) (k-sfs k-sf)
                       bool))
            (val k-spec-within?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-specs k-specs)
                       bool))
            (val k-spec-of (subr (maxeff (read @globals) (read @t) spin) (int) k-specs))
            (val k-spec-delta
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin) (int int)
                       string))))
