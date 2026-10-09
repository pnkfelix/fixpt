;;; The signature of `check-expect.fx`, its `check-expect-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type kx (select check-types-types kx))
;; The types it names, from the files that define them.
(define check-env-types (load-module "fx26:check-env-types.fx"))
(define-type k-bindings (select check-env-types k-bindings))
(define check-subtype-types (load-module "fx26:check-subtype-types.fx"))
(define-type k-checking (select check-subtype-types k-checking))
(define-type k-conv (select check-types-types k-conv))
(define-type k-eff (select check-types-types k-eff))
(define-type k-ids (select check-types-types k-ids))
(define check-resolve-types (load-module "fx26:check-resolve-types.fx"))
(define-type k-let-bs (select check-resolve-types k-let-bs))
(define-type k-names (select check-types-types k-names))
(define-type k-saying (select check-subtype-types k-saying))
(define-type k-te (select check-types-types k-te))
(define-type k-typed-params (select check-resolve-types k-typed-params))
;; The types it names, from the files that define them.
(define-type k-binders (select check-types-types k-binders))
(define-type k-descs (select check-types-types k-descs))
(define-type k-map (select check-types-types k-map))
;; The types it names, from the files that define them.
(define-type k-effs (select check-subtype-types k-effs))
(define-type k-letrec-bs (select check-resolve-types k-letrec-bs))
(define-type check-expect-sig
  (moduleof (val k-lambda? (subr (read @globals) (kx) bool))
            (val k-rewriting
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-checking int int k-saying)
                       k-te))
            (val k-conversion
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int int)
                       (listof k-conv acyclic)))
            (val k-convert-at
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx int k-conv)
                       unit))
            (val k-expect
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (kx int int)
                       unit))
            (val k-bind-all
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-bindings)
                       unit))
            (val k-name-nat
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (symbol int)
                       int))
            (val k-bind-named
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-bindings)
                       unit))
            (val k-naming-effect
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin)
                       (symbol int)
                       k-eff))
            (val k-note-let-lambdas
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-let-bs)
                       k-names))
            (val k-generalizable? (subr (maxeff (read @globals) (read @t)) (kx k-eff) bool))
            (val k-param-types
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t))
                       (k-typed-params k-ids int int)
                       k-bindings))
            (val k-binding-types
                 (subr (maxeff (alloc @t) (read @globals) (read @t)) (k-bindings) k-ids))
            (val k-some-untyped?
                 (subr (maxeff (read @globals) (read @t)) (k-typed-params) bool))
            (val k-needs-telling? (subr (maxeff (read @globals) (read @t)) (kx) bool))
            (val k-proj-map
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-binders k-descs int int)
                       k-map))
            (val k-latent-of
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       k-effs))
            (val k-note-letrec
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-letrec-bs bool)
                       unit))
            (val k-bind-letrec
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (k-letrec-bs)
                       unit))
            (val k-letrec-not-lambda (subr (read @globals) (symbol) string))
            (val k-quote-dvar (subr (maxeff (read @globals) (read @t)) (int) string))))
