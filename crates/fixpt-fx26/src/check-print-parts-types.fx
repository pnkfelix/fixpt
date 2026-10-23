;;; The signature of `check-print-parts.fx`, its `check-print-parts-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-binders.fx`, `check-close.fx`,
;; `check-data.fx`, `check-errors.fx`, `check-expect.fx`, `check-generative.fx`,
;; `check-holds.fx`, `check-infer.fx`, `check-kinds.fx`, `check-letrec.fx`,
;; `check-mask.fx`, `check-module-rules.fx`, `check-modules.fx`,
;; `check-program.fx`, `check-read-descs.fx`, `check-read-helpers.fx`,
;; `check-read.fx`, `check-resolve.fx`, `check-rules.fx`, `check-sub-env.fx`,
;; `check-subst.fx`, `check-subtype.fx`, `check-syntax.fx`, `check-synth.fx`,
;; `check-test-facts.fx`).
;; The types it names, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(import check-types-types (type k-atom k-conv k-eff k-map))
(hide (define check-print-types (load-module "fx26:check-print-types.fx")))
(define-type k-printing (select check-print-types k-printing))
(import check-types-types (type k-region k-size))
(define-type k-size-fact (select check-print-types k-size-fact))
(define-type k-lins (select check-print-types k-lins))
(define-type k-terms (select check-types-types k-terms))
;; The types it names, from the files that define them.
(import check-print-types (type k-atree k-atrees))
(import check-types-types (type k-binders k-ids k-parts k-props))
(hide (define check-env-types (load-module "fx26:check-env-types.fx")))
(define-type k-scope (select check-env-types k-scope))
(define-type k-strings (select check-types-types k-strings))
(define-type check-print-parts-sig
  (moduleof (val k-dvar-string (subr (maxeff (read @globals) (read @t)) (int) string))
            (val k-region-show (subr (maxeff (read @globals) (read @t)) (k-region) string))
            (val k-globals-atom? (subr (read @globals) (k-atom) bool))
            (val k-show-effect (subr (maxeff (read @globals) (read @t)) (k-eff) string))
            (val k-conv-default (ref k-conv @t))
            (val k-show-marks (ref bool @t))
            (val k-show-apart
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (k-strings) k-strings))
            (val k-conv=? (subr (read @globals) (k-conv k-conv) bool))
            (val k-kind-text
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (int) string))
            (val k-kind-word
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (int) string))
            (val k-place? (subr (maxeff (read @globals) (read @t)) (k-region) bool))
            (val k-size-lit (subr (read @globals) (int) k-size))
            (val k-size-as-lit (subr pure (k-size) int))
            (val k-size-plus (subr (read @globals) (k-size int) k-size))
            (val k-size=? (subr (read @globals) (k-size k-size) bool))
            (val k-map-find (subr (maxeff (read @globals) (read @t)) (k-map int) k-map))
            (val k-size-var (subr (read @globals) (int) k-size))
            (val k-size-add-scaled (subr (read @globals) (k-size k-size int) k-size))
            (val k-coef-of (subr (read @globals) (k-terms int) int))
            (val k-size-facts (ref (listof k-size-fact acyclic) @t))
            (val k-size-nonneg? (subr (maxeff (read @globals) (read @t)) (k-size) bool))
            (val k-size-eq? (subr (maxeff (read @globals) (read @t)) (k-size k-size) bool))
            (val k-tail-size (subr (maxeff (read @globals) (read @t)) (k-size) k-size))
            (val k-size-le? (subr (maxeff (read @globals) (read @t)) (k-size k-size) bool))
            (val k-subst-size
                 (subr (maxeff (read @globals) (read @t)) (k-size k-map) k-size))
            (val k-show-size
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (k-size) string))
            (val k-printing-none k-printing)
            (val k-conv-show (subr (maxeff (read @globals) (read @t)) (k-conv) string))
            (val k-atree-of
                 (subr (maxeff (read @globals) (read @t) spin)
                       (k-scope int k-atree)
                       k-atree))
            (val k-abbrev-by
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (k-atrees int)
                       k-strings))
            (val k-show-binders
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (k-binders)
                       k-strings))
            (val k-depth-of (subr (maxeff (read @globals) (read @t)) (k-ids int) int))
            (val k-nlist-end (subr (maxeff (read @globals) (read @t)) (k-region) string))
            (val k-conv-prefix (subr (maxeff (read @globals) (read @t)) (k-conv) string))
            (val k-show-abs
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (k-parts) string))
            (val k-printing-named
                 (subr (maxeff (alloc @t) (read @globals)) (k-printing k-parts) k-printing))
            (val k-part-named
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (k-parts int)
                       k-strings))
            (val k-show-props
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (string k-props)
                       string))
            (val k-unit-terms (subr (read @globals) (k-terms) k-terms))
            (val k-lins-vars (subr (maxeff (alloc @t) (read @globals)) (k-lins k-ids) k-ids))
            (val k-fm-eliminate (subr (maxeff (alloc @t) (read @globals)) (k-lins k-ids) bool))
            (val k-terms-gcd (subr (read @globals) (k-terms int) int))))
