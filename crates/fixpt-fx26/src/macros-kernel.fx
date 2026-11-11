;;; The macros' kernel (`macros.rs`, `macros.fx`): the forms a template may
;;; use, with their binding structure, each form's signature of its
;;; operands in Herman's notation (`define` names an abbreviation, `form` a
;;; form, `definition` a definition's form); the words that are forms'
;;; names, which no macro, binder or variable may be; and the words of
;;; descriptions, which a template's descriptions write as they are. Data,
;;; read by both front ends' expanders.

(define kernel-forms datum
  (quote
   (
    (define exprs (mu es (union () (expr . es))))
    ;; As named: (union nil (exports (pairof (named x bvar) (named xs formals)) (rib x xs)) …);
    ;; each parameter in scope in the types of those after it, as the
    ;; checkers bind them (`Checker::synth_lambda_as`'s `(select m t)` of an
    ;; earlier one).
    (define formals (mu f (union (export () (rho))
                                 (export (bvar . (import f (rho (A var)))) (rho (A var) (D rib)))
                                 (export ((bvar type) . (import f (rho (AA var))))
                                         (rho (AA var) (D rib))))))
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
    ;; A `define-rec`'s, each lambda in the scope of its type's `poly`s'
    ;; binders, as a definition's is (`Checker::bind_signature`).
    (define defrec-bindings
      (mu b (union (export () (rho))
                   (export ((bvar type (import lambda (rho (ADA rib)))) . b)
                           (rho (AA var) (D rib))))))
    ;; A description's binders, `((name kind) …)`, a third the binder's place
    ;; or `distinct`; each in the scope of those before it.
    (define dbinders (mu b (union (export () (rho))
                                  (export ((dvar kind) . b) (rho (AA dvar) (D rib)))
                                  (export ((dvar kind type) . b) (rho (AA dvar) (D rib))))))
    (define descs (mu ds (union () (type . ds))))
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
    (form tuple exprs)
    (form tagcase (expr . arms))
    (form cond cond-clauses)
    (form plambda (dbinders . (import exprs (rho (A rib)))))
    (form proj (expr . descs))
    ;; The forms that bind a region (`letregion`, `letfreeze`, the latter
    ;; into a place if `(r p)`) or a place, which is also a value of type
    ;; `(place r)` (`letrena`, `letreap`), in their bodies; a lambda whose
    ;; closure is made in a place.
    (form letregion (dvar . (import exprs (rho (A dvar)))))
    (form letfreeze (union (dvar . (import exprs (rho (A dvar))))
                           ((dvar type) . (import exprs (rho (AA dvar))))))
    (form letrena (dvar . (import exprs (rho (A place)))))
    (form letreap (dvar . (import exprs (rho (A place)))))
    (form rlambda (expr formals . (import exprs (rho (AD rib)))))
    (form %app (expr . exprs))
    ;; A keyword's construction, `(#:tag e …)`, its tag written or a
    ;; pattern variable's (a `label`).
    (form %construct (label . exprs))
    ;; The definitions a template may make, a macro's whose signature says
    ;; `(-> σ defn)`, each exporting what it defines: a value, seeing those
    ;; before it, `(define x T lambda)` and `define*` itself, a `define-rec`
    ;; group the whole group; a `begin`'s, each in the scope of those before
    ;; it. The address `()` is the part the annotation is on. A definition's
    ;; type's `poly`s' binders are in scope in what it is defined as.
    (define defns (mu d (union (export () (cage))
                               (export (defn . (import d (cage (at A)))) (cage (at D) (at A))))))
    (definition define (union (export (bvar expr) (rho (A var)))
                              (export (bvar type (import expr (rho (A var) (AD rib))))
                                      (rho (A var)))))
    (definition define* (export (bvar type (import lambda (rho (A var) (AD rib)))) (rho (A var))))
    (definition define-rec (import defrec-bindings (rho (() rib))))
    ;; A type, its name in scope in itself (types are declared ahead), a
    ;; family's parameters too; an effect.
    (definition define-type
      (union (export (dvar (import type (rho (A dvar)))) (rho (A dvar)))
             (export ((dvar . dbinders) (import type (rho (AA dvar) (DA rib)))) (rho (AA dvar)))))
    (definition define-effect (export (dvar type) (rho (A dvar))))
    (definition begin defns))))

;; The binding structure of the forms `kernel-forms` has not (yet), for a
;; program's walk (`binding-shapes.md`, step 1; `Macros::alpha_renamed`),
;; read by the expander written in Rust alone, for now: a template may not
;; use these. Its notation is the kernel's, and two more: `item`, a
;; module's item (a definition, a string, or an expression run as the module
;; is made), and `(shape A)`, what the module at address `A` gives, which
;; `with` and `include` bind. A `union` of one member is there to start its
;; addresses from where it is.
(define scope-forms datum
  (quote
   (
    (define items (mu d (union (export () (cage)) (export (item . d) (cage (at A) (at D))))))
    ;; `(name body …)`, `(name body)`: the name in scope in the body.
    (define clause (union (bvar . (import exprs (rho (A var))))))
    (define arm1 (union (bvar (import expr (rho (A var))))))
    (define ids (mu i (union () (id . i))))
    (define given-opt (union () (((literal given) . ids))))
    (define dvars (mu d (union (export () (rho)) (export (dvar . d) (rho (A dvar) (D rib))))))
    (define import-names
      (mu n (union (export () (rho))
                   (export (bvar . n) (rho (A var) (D rib)))
                   (export (((literal type) . dvars) . n) (rho (DA rib) (D rib)))
                   (export (((literal effect) . dvars) . n) (rho (DA rib) (D rib))))))
    (define variants (mu v (union (export () (rho))
                                  (export ((bvar . descs) . v) (rho (AA var) (D rib))))))
    (define case-clauses (mu c (union ()
                                      (((data . data) . exprs) . c)
                                      (((literal else) . exprs) . c))))
    (define typecase-arm (union (kind bvar (import expr (rho (AD var)))) (kind expr)))
    ;; A program's `tagcase` arm, `(tag x body …)` or `(tag (x …) body …)`,
    ;; the latter taking the tag's product apart; `else` a tag here.
    (define bvars (mu n (union (export () (rho)) (export (bvar . n) (rho (A var) (D rib))))))
    (define tag-arm (union (label bvar . (import exprs (rho (AD var))))
                           (label bvars . (import exprs (rho (AD rib))))))
    (define tag-arms (mu a (union () (tag-arm . a))))
    (define typecase-arms (mu a (union () (typecase-arm . a))))
    (define select-arm (union ((data . exprs) bvar . (import exprs (rho (AD var))))))
    (define select-arms (mu a (union () (select-arm . a))))
    (form vlambda (union (bvar . (import exprs (rho (A var))))
                         ((bvar type) . (import exprs (rho (AA var))))))
    (form stage (expr type type expr clause clause . given-opt))
    (form session-check (expr type type expr clause clause . given-opt))
    (form reify-effect (type . given-opt))
    (form reify-region (type . given-opt))
    (form reify-type (type . given-opt))
    (form session-commit! (expr expr expr))
    (form syscall-available? (data))
    (form send (expr expr))
    (form receive (expr))
    (form self (expr))
    (form icell-get (expr))
    (form icell-put! (expr expr))
    ;; `(spawn (mailbox message-type place) body …)`: the mailbox and the
    ;; place (a description, and a value of it) in the body, the place in
    ;; the message's type.
    (form spawn (union ((bvar (import type (rho (ADDA place))) dvar)
                        . (import exprs (rho (AA var) (ADDA place))))))
    (form spawn-monitored (union (expr expr (bvar (import type (rho (ADDADD place))) dvar)
                                       . (import exprs (rho (AADD var) (ADDADD place))))))
    (form par (let-bindings . (import exprs (rho (A rib)))))
    (form race exprs)
    (form attempt (expr expr))
    (form attempt-within (expr expr expr expr))
    (form pselect select-arms)
    (form tagcase (expr . tag-arms))
    (form case (expr . case-clauses))
    (form typecase (expr . typecase-arms))
    (form confirm-length (expr expr arm1 expr))
    (form acyclic (expr arm1 expr))
    (form confirm-nat (expr arm1 expr))
    (form convention (type expr))
    (form make-bloblet exprs)
    (form rmake-bloblet exprs)
    (form bloblet-ref exprs)
    (form bloblet-set! exprs)
    (form bloblet-freeze exprs)
    (form bloblet-byte exprs)
    (form bloblet-set-byte! exprs)
    (form bloblet-bytes exprs)
    (form blobref-at exprs)
    (form blobref+ exprs)
    (form blobref-owner exprs)
    (form blobref-offset exprs)
    (form blobref-get exprs)
    (form blobref-set! exprs)
    (form blobref-index exprs)
    (form blobref-length exprs)
    (form blobref-variant! exprs)
    ;; A module's items, each in scope in all of them (values as a
    ;; `letrec*`'s, types as declared ahead).
    (form module (import items (cage (at ()))))
    (form extend (expr (import expr (shape A))))
    (form load-module (data))
    (form load-input (data))
    (form %loaded (data data))
    (form with (expr . (import exprs (shape A))))
    (form %datum (data))
    (form prompt (expr expr expr))
    (definition define-generative
      (union (export (dvar (import type (rho (A dvar)))) (rho (A dvar)))
             (export ((dvar . dbinders) (import type (rho (AA dvar) (DA rib)))) (rho (AA dvar)))))
    (definition define-datatype
      (union (export (dvar . (import variants (rho (A dvar)))) (rho (A dvar) (D rib)))
             (export ((dvar . dbinders) . (import variants (rho (AA dvar) (DA rib))))
                     (rho (AA dvar) (D rib)))))
    (definition define-convention (export (dvar . data) (rho (A dvar))))
    (definition define-syscall (export (bvar data type) (rho (A var))))
    (definition define-optional-syscall (export (bvar data type) (rho (A var))))
    (definition include (union (export (expr) (shape A)) (export (expr data) (shape A))))
    (definition import (export (id . import-names) (rho (D rib))))
    (definition hide items)
    (definition module-parameters (data))
    (definition import-with-syntax (union (export (expr) (shape A)) (export (expr data) (shape A))))
    (definition define-syntax data)
    (definition define-syntax-rec data))))

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
    blobref-variant! vlambda stage session-check session-commit! typecase reify-type reify-effect
    reify-region confirm-length confirm-nat convention extend load-input quasiquote letregion
    letfreeze spawn spawn-monitored send receive self par race attempt attempt-within pselect
    icell-get icell-put! acyclic)))

;; The words of descriptions (`typed-macros.md`, "Decided: a template's free
;; description names, one qualified name each"), which a template's
;; descriptions write as they are, not the top level's: the heads of the
;; forms, each read by its name alone at a list's head (both checkers'
;; `TYPE_FORMS` and `EFFECT_HEADS`, and the parts of forms), and the words
;; read before any name is looked up. Any other name in a template's
;; description is the top level's, or a binder's the template writes.
(define description-heads datum
  (quote
   (
    arrayof narrayof bloblet composable dletrec icell listof mark-key moduleof mu nat nlist
    oneshot pairof place poly productof prompt-tag proves ref select subr sumof tupleof bool oneof
    union anyof allof -> ->* restrict modnames read write alloc goto comefrom await init send
    receive io
    maxeff globals conv fields frozen requires ensures <= + - dlambda acyclic const)))
;; The type forms' heads (`parse.rs`'s `TYPE_FORMS`, which a test holds
;; this to): a template whose head is one makes a description, which is
;; how a signature inferred says so (`macros/infer.rs`'s `makes`).
(define type-forms datum
  (quote
   (
    arrayof narrayof bloblet composable dletrec icell listof mark-key moduleof mu nat nlist
    oneshot pairof place poly productof prompt-tag proves ref select subr sumof tupleof bool oneof
    union anyof allof -> ->* restrict modnames)))
(define description-words datum
  (quote (void pure spin nondet stage heap const acyclic finite cellular native fx distinct)))
