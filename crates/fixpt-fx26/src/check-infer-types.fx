;;; The types of `check-infer.fx`, its `check-infer-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-binders (select check-types-types k-binders))
(define-type k-map (select check-types-types k-map))
(define-type k-solved (ref k-map @t))
;; Binders, and the type under them.
(define-type k-bound-body (productof (1 k-binders) (2 int)))
;; A count of such occurrences, and of parameters sized by `v` alone.
(define-type k-counts (productof (1 int) (2 int)))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-proofs.fx`).
;; The types it names, from the files that define them.
(define check-resolve-types (load-module "fx26:check-resolve-types.fx"))
(define-type k-let-bs (select check-resolve-types k-let-bs))
(define-type k-parts (select check-types-types k-parts))
;; The types it names, from the files that define them.
(define-type k-arms (select check-resolve-types k-arms))
(define check-env-types (load-module "fx26:check-env-types.fx"))
(define-type k-bindings (select check-env-types k-bindings))
(define-type k-eff (select check-types-types k-eff))
(define-type k-ids (select check-types-types k-ids))
(define-type k-names (select check-types-types k-names))
(define-type k-region (select check-types-types k-region))
(define-type k-ty (select check-types-types k-ty))
(define-type kx (select check-types-types kx))
(define-type kxs (select check-types-types kxs))
;; The types it names, from the files that define them.
(define-type k-named (select check-types-types k-named))
(define check-subtype-types (load-module "fx26:check-subtype-types.fx"))
(define-type k-trail (select check-subtype-types k-trail))
(define-type check-infer-sig
  (moduleof (val k-same-labels?
                 (subr (maxeff (read @globals) (read @t)) (k-let-bs k-parts) bool))
            (val k-binders-of
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (int)
                       k-bound-body))
            (val k-default-regions
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-binders k-solved)
                       unit))
            (val k-finitized
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       int))
            (val k-named-since
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-ids k-ids k-ids)
                       k-ids))
            (val k-forget-nats
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-ids int int int)
                       int))
            (val k-inst-shapes
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kxs k-ids int k-binders k-solved (arrayof int @t))
                       unit))
            (val k-result-shape
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int int k-binders k-solved int int)
                       unit))
            (val k-push-ids
                 (subr (maxeff (alloc @t) (read @globals) (read @t)) (k-ids k-ids) k-ids))
            (val k-mentions-any-unknown?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-binders k-solved)
                       bool))
            (val k-mentions-unknown-type?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-binders k-solved)
                       bool))
            (val k-any-unknown-type?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-ids k-binders k-solved)
                       bool))
            (val k-instantiate-against
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int int int int)
                       int))
            (val k-plambda-matches?
                 (subr (maxeff (read @globals) (read @t)) (kx k-ty) bool))
            (val k-variants-not-named
                 (subr (maxeff (alloc @t) (read @globals) (read @t))
                       (k-parts k-arms)
                       k-parts))
            (val k-cannot-take-apart
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (symbol int k-names kx)
                       k-bindings))
            (val k-zip-fields
                 (subr (maxeff (alloc @t) (read @globals) (read @t))
                       (k-names k-parts)
                       k-bindings))
            (val k-beyond
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (k-eff k-eff k-eff)
                       k-eff))
            (val k-reaches-only?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (kx kx k-region)
                       bool))
            (val k-fin-region (subr (read @globals) (k-region) k-region))
            (val k-binding-depth
                 (subr (maxeff (read @globals) (read @t) spin) (symbol) int))
            (val k-certified-has?
                 (subr (maxeff (read @globals) (read @t)) (k-named symbol int) bool))
            (val k-sc-one-arg? (subr (read @t) (kxs) bool))
            (val k-check-bounds
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-binders k-map int int)
                       unit))
            (val k-check-finite-sizes
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-binders k-map int int int)
                       unit))
            (val k-finish
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-binders k-solved int int int)
                       k-map))
            (val k-unify
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int int k-binders k-solved k-trail)
                       unit))
            (val k-list-of-any?
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       bool))
            (val k-upper-bound
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-ids k-ids)
                       int))
            (val k-part-names
                 (subr (maxeff (alloc @t) (read @globals) (read @t))
                       (k-parts)
                       (listof string acyclic)))))
