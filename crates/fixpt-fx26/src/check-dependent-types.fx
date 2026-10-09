;;; The types of `check-dependent.fx`, its `check-dependent-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-env-types (load-module "fx26:check-env-types.fx"))
(define-type k-bindings (select check-env-types k-bindings))
(define-type k-params-given (select check-env-types k-params-given))
(define check-resolve-types (load-module "fx26:check-resolve-types.fx"))
(define-type k-callable (select check-resolve-types k-callable))
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-map (select check-types-types k-map))
;; A module-typed binding's abstract types, from parameter `j`: each as named
;; for the binding, onto `given`; and as `(select $j t)`, onto `back`.
(define-type k-given-back (productof (1 k-params-given) (2 k-map)))
;; What a `lambda`'s parameters were bound to: their types for the
;; procedure's type; and what each earlier one gives its `(select $k t)`s.
(define-type k-dependent (productof (1 k-bindings) (2 k-params-given) (3 k-map)))
;; A dependent procedure's callee, `c` (none or one), for a call with `args`
;; at `a`..`b`: its types given the modules its arguments name.
(define-type k-callables (listof k-callable acyclic))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
;; The types it names, from the files that define them.
(define-type kxs (select check-types-types kxs))
(define-type check-dependent-sig
  (moduleof (val k-instantiate-params
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-params-given)
                       int))
            (val k-bind-params
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-bindings int int)
                       k-dependent))
            (val k-result-back
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-map)
                       int))
            (val k-dependent-callee
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-callables kxs int int)
                       k-callables))))
