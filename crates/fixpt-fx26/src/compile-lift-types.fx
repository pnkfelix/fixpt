;;; The types of `compile-lift.fx`, its `compile-lift-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define compile-types (load-module "fx26:compile-types.fx"))
(define-type syms (select compile-types syms))
;; While a `letrec` is planned to be lifted, by member: the names each
;; takes, and the siblings each calls.
(define-type c-added (arrayof syms @k))
(define-type c-calls (arrayof (listof int @k) @k))
;;; ------------------------------------------- the middle phase's plan
;;; Before a top-level form is compiled, `compile-plan.fx` decides each
;;; lambda's captured names and each `letrec`'s lifting
;;; (`docs/research/compiler-middle-phase.md`, step 2), as the Rust
;;; compiler's `cellular/procs.rs`; the stack code reads them here.

;; A lambda as planned: its parameters' names, and the names it captures.
(define-type c-planned (productof (1 syms) (2 syms)))
(define-type c-planneds (listof c-planned @k))
;; The standard operations' words of the form being compiled whose twins
;; are to be made, last first (step 4): each word, operation and arity.
(define-type c-standard-twin (productof (1 tword) (2 string) (3 int)))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-twins.fx`).
;; The types it names, from the files that define them.
(define-type c-params (select compile-types c-params))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
;; The types it names, from the files that define them.
(define-type c-recs (select compile-types c-recs))
(define-type cenv (select compile-types cenv))
(define-type compile-lift-sig
  (moduleof (val c-twin-depth (ref int @k))
            (val c-r-in-plan (ref bool @k))
            (val c-planned-fv
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (c-params exp)
                       (listof syms @k)))
            (val c-standard-twins (ref (listof c-standard-twin @k) @k))
            (val c-bind-lifted
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (c-recs (listof int @k) cenv)
                       cenv))
            (val c-span-key (subr pure (int int) int))
            (val c-lift-added (subr (maxeff (read @globals) (read @k)) (int) syms))
            (val c-lambda-captured
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (c-params exp cenv)
                       syms))))
