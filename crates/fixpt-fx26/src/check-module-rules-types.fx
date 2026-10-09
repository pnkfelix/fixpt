;;; The types of `check-module-rules.fx`, its `check-module-rules-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-effect checks (select check-types-types checks))
(define-type k-eff (select check-types-types k-eff))
(define-type k-ids (select check-types-types k-ids))
(define-type k-parts (select check-types-types k-parts))
(define check-resolve-types (load-module "fx26:check-resolve-types.fx"))
(define-type k-letrec-bs (select check-resolve-types k-letrec-bs))
;; What an error's message `m` is made into.
(define-type k-say (subr (maxeff checks spin) (string) string))
;; What a module's items make, its abstract types, descriptions and values
;; (each newest first), and the effect of making them.
(define-type k-made (productof (1 k-parts) (2 k-parts) (3 k-parts) (4 k-eff)))
;; The bindings of lambdas `ls`, and the types written, resolved.
(define-type k-mod-bound (productof (1 k-letrec-bs) (2 k-ids)))
;; Why each group found so far may not end ("" if it ends), by its first
;; member's name.
(define-type k-ends (listof (productof (1 symbol) (2 string)) acyclic))
;; An effect, and a type.
(define-type k-eff-ty (productof (1 k-eff) (2 int)))
;; The effect of checking each lambda of `bs` against its type, in the
;; scope of every item, with its recursive group (of `gs`, `k-mod-groups`)
;; checked to end, as a `define-rec`'s members are; `ws` why the groups so
;; far may not, `ds` the types written; and the bindings, a `define*`'s at
;; the type found.
(define-type k-mod-checked (productof (1 k-eff) (2 k-letrec-bs)))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
(define-type check-module-rules-sig
  (moduleof (val k-rebind-top
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (symbol int)
                       unit))))
