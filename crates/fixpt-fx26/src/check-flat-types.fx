;;; The signature of `check-flat.fx` as `check-read-helpers.fx` uses it, to
;;; give on (`TODO.md` §68, §188): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-dependent.fx`, `check-infer.fx`,
;; `check-kinds.fx`, `check-module-rules.fx`, `check-modules.fx`,
;; `check-rules.fx`).
;; The types it names, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(import check-types-types (type k-binders k-desc k-descs k-ids k-parts))
;; The types it names, from the files that define them.
(define-type k-names (select check-types-types k-names))
(hide (define check-read-types (load-module "fx26:check-read-types.fx")))
(define-type k-params (select check-read-types k-params))
(hide (define check-env-types (load-module "fx26:check-env-types.fx")))
(import check-env-types (type k-scope k-selects))
(define-type k-syns (select check-read-types k-syns))
(hide (define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
(define-type syn (select parser-types syn))
(define-type k-region (select check-types-types k-region))
(define-type k-int-pair (pairof int int @t))
(import check-types-types (type k-te kx k-at k-eff))
;; The checker's knot, `check-rules.fx`'s `k-synth-as`, as given here.
(define-type k-synth-as-knot
  (subr (maxeff (alloc @t) (goto @z) (read @globals) (read @s) (read @t) (write @t) spin)
        (kx int)
        k-te))
(define-type k-size (select check-types-types k-size))
(define-type check-flat-sig
  (moduleof (val k-flat-not-type (subr (maxeff (read @globals) spin) (string) string))
            (val k-flat-var-type? (subr (maxeff (read @globals) (read @t) spin) (int) bool))
            (val k-is-flat? (subr (maxeff (read @globals) (read @t) spin) (int) bool))
            (val k-parse-flat
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       int))
            (val k-flat-code (subr (maxeff (read @globals) spin) (symbol) int))
            (val k-flat-layout
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (int) k-int-pair))
            (val k-flat-field
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (int symbol)
                       (pairof int int @t)))
            (val k-unsized-length
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (int)
                       (listof k-size acyclic)))
            (val k-with-unsized-length
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-size)
                       int))
            (val k-flat-array-parts
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (int)
                       (pairof int int @t)))
            (val k-flat-sum-size
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (int)
                       (pairof int int @t)))
            (val k-flat-view (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin) (k-at k-te) k-te))
            (val k-else-type (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                                   (int k-parts)
                                   int))
            (val k-in-scope-check (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin) (symbol int kx int k-synth-as-knot) k-te))
            (val k-in-scope-parts
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-parts kx int k-synth-as-knot int int int int)
                       k-te))
            (val k-blobref-variant (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin) (int int int int int int int kx int int k-eff) k-te))
            (val k-blobref-parts
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (int)
                       (listof (pairof int int @t) acyclic)))
            (val k-blobref-of
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int int)
                       int))))
