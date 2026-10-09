;;; The types of `compile-plan.fx`, its `compile-plan-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define compile-exps-types (load-module "fx26:compile-exps-types.fx"))
(define-type c-inline (select compile-exps-types c-inline))
(define compile-types (load-module "fx26:compile-types.fx"))
(define-type c-params (select compile-types c-params))
(define-type syms (select compile-types syms))
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define table-types (load-module "fx26:table-types.fx"))
(define-type table (select table-types table))
;; A global procedure whose parameter (6) is only called, with (7)
;; arguments, or passed as itself to a call of the procedure: a call with a
;; lambda there may run a copy of the procedure made for that lambda, the
;; lambda's body inlined where the parameter is called (`regcode.fx`'s
;; `r-specialize`). Its name, word, parameters, body and globals, as for
;; `c-inline`.
(define-type c-special
  (productof (1 symbol) (2 tword) (3 c-params) (4 exp) (5 int) (6 int) (7 int)))
(define-type c-specializables (listof c-special acyclic))
;; A call of a global, as planned (step 3): the small procedure it may be
;; inlined as, and the procedure it may be specialized as with the lambda
;; argument, each in a list of none or one; by where the call is.
(define-type c-spec-call (productof (1 c-special) (2 exp)))
(define-type c-spec-calls (listof c-spec-call @k))
(define-type c-called (productof (1 (listof c-inline acyclic)) (2 c-spec-calls)))
;; The plan's contexts (3b): the form's own, 0; and each body its calls
;; inline, numbered, planned as register code compiles it there. Each one's
;; calls, by where they are; and the bodies they inline, by name and arity:
;; what an inlined body decides depending on the callee and the path to it,
;; not on the call.
(define-type c-calls-at (table int c-called @k))
(define-type c-inlined-at (listof (productof (1 symbol) (2 int) (3 int)) @k))
;; The form's copies, last first, each with what it is made for (step 4):
;; the procedure, the lambda, the procedure's global, the names the
;; lambda's closure captures, the globals it sees, and the copy's context.
(define-type c-copy-at (productof (1 c-special) (2 exp) (3 wglobal) (4 syms) (5 int) (6 int)))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-programs.fx`).
;; The types it names, from the files that define them.
(define-type c-inlinables (select compile-exps-types c-inlinables))
;; The types it names, from the files that define them.
(define-type exps (select compile-types exps))
;; The types it names, from the files that define them.
(define-type c-spec-copies (select compile-types c-spec-copies))
(define-type compile-plan-sig
  (moduleof (val c-inline-limit int)
            (val c-inlines (ref c-inlinables @k))
            (val c-inlines-of
                 (subr (maxeff (read @globals) (read @k)) (symbol) c-inlinables))
            (val c-note-inline!
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (c-inline)
                       unit))
            (val c-forget-inline!
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (symbol)
                       unit))
            (val c-unrolls
                 (ref (bloblet (fields (subr pure (symbol) int)
                                       (subr pure (symbol symbol) bool)
                                       (arrayof (listof (pairof symbol c-inlinables @k)
                                                        acyclic)
                                                @k)
                                       int)
                               @k)
                      @k))
            (val c-specials (ref c-specializables @k))
            (val c-drop-special
                 (subr (maxeff (alloc @k) (read @globals) (read @k))
                       (c-specializables symbol)
                       c-specializables))
            (val c-inline-room (subr (maxeff (read @globals) spin) (exp int) int))
            (val c-plan-top
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (exp)
                       unit))
            (val c-unrolls-of
                 (subr (maxeff (read @globals) (read @k)) (symbol) c-inlinables))
            (val c-special-limit int)
            (val c-nth (subr (read @globals) (exps int) exp))
            (val c-plan-copy-order (ref (listof c-copy-at @k) @k))
            (val c-make-copies
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       ((listof c-copy-at @k))
                       unit))
            (val c-room (subr (maxeff (read @globals) spin) (exp int bool) int))
            (val c-inlining (ref syms @k))
            (val c-plan-child
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (int symbol int)
                       int))
            (val c-spec-copy-find
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (c-spec-copies tword syms int)
                       c-spec-copies))))
