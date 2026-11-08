;;; The macros' kernel (`macros.rs`, `macros.fx`): the forms a template may
;;; use, with their binding structure, each form's signature of its
;;; operands in Herman's notation (`define` names an abbreviation, `form` a
;;; form, `definition` a definition's form); and the words that are forms'
;;; names, which no macro, binder or variable may be. Data, read by both
;;; front ends' expanders.

(define kernel-forms datum
  (quote
   (
    (define exprs (mu es (union () (expr . es))))
    ;; As named: (union nil (exports (pairof (named x bvar) (named xs formals)) (rib x xs)) …)
    (define formals (mu f (union (export () (rho))
                                 (export (bvar . f) (rho (A var) (D rib)))
                                 (export ((bvar type) . f) (rho (AA var) (D rib))))))
    (define let-bindings (mu b (union (export () (rho))
                                      (export ((bvar expr) . b) (rho (AA var) (D rib))))))
    ;; Herman's let*-cl: each clause's expression in the scope of those
    ;; before; the whole a ribcage, innermost first.
    (define let*-clauses (mu c (union (export () (cage))
                                      (export ((bvar expr) . (import c (rho (AA var))))
                                              (cage (at D) (rho (AA var)))))))
    ;; Each bound to a lambda, as the checkers take one.
    (define letrec-bindings (mu b (union (export () (rho))
                                         (export ((bvar type lambda) . b) (rho (AA var) (D rib))))))
    ;; A `tagcase` arm, `(#:tag x body …)` or `(else x body …)`: `x` in scope in
    ;; the body.
    (define arms (mu a (union ()
                              ((label bvar . (import exprs (rho (ADA var)))) . a)
                              (((literal else) bvar . (import exprs (rho (ADA var)))) . a))))
    (define cond-clauses (mu c (union ()
                                      ((expr . exprs) . c)
                                      (((literal else) . exprs) . c))))
    (define fields (mu p (union () ((label expr) . p))))
    (form lambda (formals . (import exprs (rho (A rib)))))
    (form let (let-bindings . (import exprs (rho (A rib)))))
    (form let* (let*-clauses . (import exprs (cage (at A)))))
    (form letrec ((import letrec-bindings (rho (A rib))) . (import exprs (rho (A rib)))))
    (form if (expr expr expr))
    (form begin exprs)
    (form and exprs)
    (form or exprs)
    (form quote (data))
    (form the (type expr))
    (form sum (label expr))
    (form extract (expr label))
    (form product fields)
    (form tagcase (expr . arms))
    (form cond cond-clauses)
    (form %app (expr . exprs))
    ;; The definitions a template may make, a macro's whose signature says
    ;; `(-> σ defn)`, each exporting what it defines: a value, seeing those
    ;; before it, `(define x T lambda)` and `define*` itself, a `define-rec`
    ;; group the whole group; a `begin`'s, each in the scope of those before
    ;; it. The address `()` is the part the annotation is on.
    (define defns (mu d (union (export () (cage))
                               (export (defn . (import d (cage (at A)))) (cage (at D) (at A))))))
    (definition define (union (export (bvar expr) (rho (A var)))
                              (export (bvar type (import expr (rho (A var)))) (rho (A var)))))
    (definition define* (export (bvar type (import lambda (rho (A var)))) (rho (A var))))
    (definition define-rec (import letrec-bindings (rho (() rib))))
    (definition begin defns))))

;; The kernel's keywords (`top::KEYWORDS`, which a test holds this to); with
;; `#%fx`, `#%toplevel` and `define-syntax`, the names that are reserved.
(define reserved-words datum
  (quote
   (
    lambda plambda proj if letrec let begin define define* define-type define-generative subr ->
    ->* poly ref pairof dletrec void pure maxeff read write alloc goto comefrom region effect type
    prompt prompt-tag composable oneshot mark-key listof cond case else and or let* define-effect
    define-convention define-syscall define-optional-syscall syscall-available? module-parameters
    the bloblet fields frozen arrayof icell await define-rec letrena letreap rlambda quote
    productof sumof product tupleof tuple extract sum tagcase module moduleof with select
    load-module import define-datatype make-bloblet bloblet-ref bloblet-set! bloblet-freeze
    bloblet-byte bloblet-set-byte! bloblet-bytes rmake-bloblet dlambda => blobref-at blobref+
    blobref-owner blobref-offset blobref-get blobref-set! blobref-index blobref-length
    blobref-variant!)))
