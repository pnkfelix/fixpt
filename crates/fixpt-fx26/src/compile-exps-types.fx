;;; The types of `compile-exps.fx`, its `compile-exps-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define compile-types (load-module "fx26:compile-types.fx"))
(define-type c-params (select compile-types c-params))
(define-type c-this (select compile-types c-this))
(define-type cenv (select compile-types cenv))
(define-type syms (select compile-types syms))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
;; A small global procedure a call in register code may inline, guarded
;; (`regcode.fx`'s `r-inline`): its name, word, parameters and body, and
;; the globals as its body saw them.
(define-type c-inline
  (productof (1 symbol) (2 tword) (3 c-params) (4 exp) (5 int)))
(define-type c-inlinables (listof c-inline acyclic))
;; A value a module's item makes: its name, its expression, the item's kind
;; (0 an abstract type's conversion, 2 a definition, 3 a `define-rec`'s
;; member), and whether it is a typed lambda.
(define-type c-mval (productof (1 symbol) (2 exp) (3 int) (4 bool)))
(define-type c-mvals (listof c-mval @k))
;; Each value's name, and its slot, from `d`.
(define-type c-mslots (listof (pairof symbol int @k) @k))
;; Closures to finish: the closure's slot, its free value, and the slot it
;; waits for.
(define-type c-waits (listof (productof (1 int) (2 int) (3 int)) @k))
;; A lambda's word, made by the stack code of the body it is in: where its
;; body starts and ends, its parameters, its own name, the word, and the
;; names it captures.
(define-type c-made (productof (1 int) (2 int) (3 syms) (4 syms) (5 tword) (6 syms)))
;; A lambda's word, and the names its closure captures, in order.
(define-type c-closing (productof (1 tword) (2 syms)))
;; An `rlambda`'s region, in a list; none for a plain lambda.
(define-type c-region (listof exp @k))
;; A procedure being specialized at a lambda: its global's name, cell and
;; word; the parameter's place and name; how many parameters; the lambda's
;; arity, parameters and body, the names its closure captures in order, and
;; the globals it sees.
(define-type c-spec
  (productof (1 symbol) (2 wglobal) (3 tword) (4 int) (5 symbol) (6 int) (7 int)
             (8 c-params) (9 exp) (10 syms) (11 int)))
;; A specialized copy's twin's context: what it is specialized at, its
;; plan's context, and the globals its procedure saw.
(define-type c-copy-twin (productof (1 c-spec) (2 int) (3 int)))
;; A lambda's word whose register code, its twin, is made once its form's
;; words all are (step 4), with what its stack code knew and made: the
;; word, parameters, body, scope, the procedure it is, the definition it
;; is (if one), the words of the lambdas in it, and, a copy's, its context.
(define-type c-twin
  (productof (1 tword) (2 c-params) (3 exp) (4 cenv) (5 (listof c-this @k))
             (6 (listof symbol @k)) (7 (listof c-made @k)) (8 (listof c-copy-twin @k))))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-programs.fx`).
;; The types it names, from the files that define them.
(define-type code (select compile-types code))
(define-type mod-items (select parser-types mod-items))
(define-type patches (select compile-types patches))
;; The types it names, from the files that define them.
(define-type c-lift (select compile-types c-lift))
(define-type c-lifting (select compile-types c-lifting))
(define-type c-recs (select compile-types c-recs))
(define-type compile-exps-sig
  (moduleof (val c-defining (ref (listof symbol @k) @k))
            (val c-word-name (ref (listof string @k) @k))
            (val c-module-members (ref (listof c-inlinables @k) @k))
            (val c-module-values
                 (subr (maxeff (alloc @k) (read @globals)) (mod-items) c-mvals))
            (val c-made-now (ref (listof c-made @k) @k))
            (val c-made-reuse (ref (listof c-made @k) @k))
            (val c-exp
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (exp cenv int code bool)
                       unit))
            (val c-lambda
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (c-params exp cenv int code syms c-region)
                       patches))
            (val c-last-word (ref (listof tword @k) @k))
            (val c-prev-word (ref (listof tword @k) @k))
            (val c-own-now (ref (listof (productof (1 symbol) (2 tword)) @k) @k))
            (val c-spec-now (ref (listof c-spec @k) @k))
            (val c-r-plan-ctx (ref (listof int @k) @k))
            (val c-twins (ref (listof c-twin @k) @k))
            (val c-names-any?
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (exp c-mslots)
                       bool))
            (val c-waits-onto
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (c-waits int patches)
                       c-waits))
            (val c-made-word
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (c-params exp cenv syms)
                       (listof c-closing @k)))
            (val c-fx-name (subr (read @globals) (symbol exp) string))
            (val c-lift
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (c-recs exp int int cenv bool)
                       c-lifting))))
