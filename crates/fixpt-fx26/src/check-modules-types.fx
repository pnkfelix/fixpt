;;; The types of `check-modules.fx`, its `check-modules-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-effect checks (select check-types-types checks))
(define-type k-ids (select check-types-types k-ids))
(define-type k-map (select check-types-types k-map))
(define-type k-parts (select check-types-types k-parts))
(define-type kxs (select check-types-types kxs))
;; A `define-rec`'s types and expressions, each type read before its
;; expression, as the Rust parser reads them.
(define-type k-rec-read (productof (1 k-ids) (2 kxs)))
;; Run `f`; an error it makes in the file read at `base` (`load-module`)
;; said at `a`..`b`, with where in the file, as the Rust checker says it.
(define-type k-thunk-unit (subr (maxeff checks spin) () unit))
;; Abstract types `abs` renamed for a binding, each `prefix` and its name:
;; the new ones, and what each old one becomes.
(define-type k-renamed (productof (1 k-parts) (2 k-map)))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define check-env-types (load-module "fx26:check-env-types.fx"))
(define-type k-scope (select check-env-types k-scope))
(define-type kx (select check-types-types kx))
(define-type syn (select parser-types syn))
;; The types it names, from the files that define them.
(define-type k-binders (select check-types-types k-binders))
;; The types it names, from the files that define them.
(define check-resolve-types (load-module "fx26:check-resolve-types.fx"))
(define-type k-letrec-bs (select check-resolve-types k-letrec-bs))
;; The types it names, from the files that define them.
(define-type k-bindings (select check-env-types k-bindings))
(define-type k-names (select check-types-types k-names))
(define check-holds-types (load-module "fx26:check-holds-types.fx"))
(define-type k-seen (select check-holds-types k-seen))
(define-type check-modules-sig
  (moduleof (val k-resolve-exp
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (exp)
                       kx))
            (val k-name-module
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (symbol int)
                       int))
            (val k-link-aliases
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (symbol k-scope)
                       unit))
            (val k-select-syn
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int syn)
                       int))
            (val k-push-binders
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t))
                       (k-binders)
                       unit))
            (val k-in-loaded
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-thunk-unit int int int)
                       unit))
            (val k-resolve-selects
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int int int)
                       int))
            (val k-letrec-selected
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-letrec-bs int int)
                       k-letrec-bs))
            (val k-first-mentioned
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int k-ids)
                       int))
            (val k-unescaped
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int k-ids int int)
                       k-ids))
            (val k-check-apps-each
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-ids k-seen int int)
                       unit))
            (val k-resolve-outside
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (int k-names int int)
                       int))
            (val k-binding-names
                 (subr (maxeff (alloc @t) (read @globals) (read @t)) (k-bindings) k-names))))
