;;; The checker, in FX-26: first-class modules' rules
;;; (`docs/research/first-class-modules.md`, stage M2): `module` and `with`,
;;; module types compared, and what the termination check sees in them. The
;;; Rust checker's `modules.rs`, rule for rule; `check-modules.fx` reads and
;;; names. Part of the checker, `check-types.fx` first.

;;; ------------------------------------------------------------ module

;; What a module's items make, its abstract types, descriptions and values
;; (each newest first), and the effect of making them.
(define-type k-made (productof (1 k-parts) (2 k-parts) (3 k-parts) (4 k-eff)))
(define k-made-of (subr (alloc @t) (k-parts k-parts k-parts k-eff) k-made)
  (lambda (abs ds vs e) (product (1 abs) (2 ds) (3 vs) (4 e))))
;; An abstract type `t`, its representation seen only through its own
;; conversions, which stay inside the module: each the identity, made as a
;; closure is, checked on its representation and bound at `t`.
(define k-module-abs (subr (maxeff checks spin) (k-item int int k-made) k-made)
  (lambda (it a b made)
    (let* ((n (car (extract it 2)))
           (v (extract it 3))
           (rep (k-resolve-selects (car (extract it 4)) a b))
           (t (k-ty-new (ty-var v)))
           (identity (k-new-subr nil (the k-ids (cons rep nil)) rep))
           (fns (extract it 5))
           (up (k-check (car fns) identity))
           (down (k-check (car (cdr fns)) identity)))
      (begin
        (k-bind (k-conversion-name "up-" n) (k-new-subr nil (the k-ids (cons rep nil)) t))
        (k-bind (k-conversion-name "down-" n) (k-new-subr nil (the k-ids (cons t nil)) rep))
        (k-made-of (k-part-onto n v (extract made 1)) (extract made 2) (extract made 3)
                   (extract made 4))))))
;; A value: checked against its type, if it has one, or found; bound, its
;; sizes and abstract types named for it, for the items after it.
(define k-module-val (subr (maxeff checks spin) (k-item int int k-made) k-made)
  (lambda (it a b made)
    (let* ((n (car (extract it 2)))
           (ts (extract it 4))
           (init (car (extract it 5)))
           (r (if (null? ts)
                  (k-synth init)
                  (let ((t (k-resolve-selects (car ts) a b))) (k-te t (k-check init t)))))
           (bound (k-bind n (k-name-nat n (extract r 1)))))
      (k-made-of (extract made 1) (extract made 2) (k-part-onto n (extract r 1) (extract made 3))
                 (k-union (extract made 4) (extract r 2))))))
;; A group's bindings, each type resolved at `a`..`b` in turn.
(define k-group-bindings (subr (maxeff checks spin) (k-names k-ids kxs int int) k-letrec-bs)
  (lambda (ns ts xs a b)
    (if (null? ns)
        nil
        (let* ((t (k-resolve-selects (car ts) a b))
               (rest (k-group-bindings (cdr ns) (cdr ts) (cdr xs) a b)))
          (cons (product (1 (car ns)) (2 t) (3 (car xs))) rest)))))
;; Every one of `bs` a `lambda`, or an error at the first that is not.
(define k-group-lambdas (subr checks (k-letrec-bs) unit)
  (lambda (bs)
    (cond ((null? bs) #u)
          ((k-lambda? (extract (car bs) 3)) (k-group-lambdas (cdr bs)))
          (else (k-fail-at (k-cat3 "`" (symbol->string (extract (car bs) 1))
                                   "`, in a `define-rec`, is a `lambda`")
                           (extract (car bs) 3))))))
(define k-parts-of-group (subr (maxeff (read @globals) (alloc @t)) (k-letrec-bs k-parts) k-parts)
  (lambda (bs ps)
    (if (null? bs)
        ps
        (k-parts-of-group (cdr bs) (k-part-onto (extract (car bs) 1) (extract (car bs) 2) ps)))))
;; `(define-rec (f T e) …)`: every name in scope first, known; then each
;; `lambda` checked against its type, a group whose every run ends needing
;; no `spin`.
(define k-module-group (subr (maxeff checks spin) (k-item int int k-made) k-made)
  (lambda (it a b made)
    (let* ((bs (k-group-bindings (extract it 2) (extract it 4) (extract it 5) a b))
           (rsaved (get k-recursive))
           (bound (k-bind-letrec bs))
           (lambdas (k-group-lambdas bs))
           (noted (k-note-ending bs (k-termination bs)))
           (e (k-check-letrec bs))
           (restored (set k-recursive rsaved)))
      (k-made-of (extract made 1) (extract made 2) (k-parts-of-group bs (extract made 3))
                 (k-union (extract made 4) e)))))
;; Items `items`, each in the scope of those before it.
(define k-module-items (subr (maxeff checks spin) (k-items int int k-made) k-made)
  (lambda (items a b made)
    (if (null? items)
        made
        (let* ((it (car items))
               (k (extract it 1))
               (next (cond
                       ((= k 0) (k-module-abs it a b made))
                       ((= k 1)
                        (let ((t (k-resolve-selects (car (extract it 4)) a b)))
                          (k-made-of (extract made 1)
                                     (k-part-onto (car (extract it 2)) t (extract made 2))
                                     (extract made 3) (extract made 4))))
                       ((= k 2) (k-module-val it a b made))
                       (else (k-module-group it a b made)))))
          (k-module-items (cdr items) a b next)))))
;; Each value's type, `vs`, mentions none of `inner`, the sizes and abstract
;; types named inside the module; or an error at `a`..`b`.
(define k-vals-known (subr (maxeff checks spin) (k-parts k-ids int int) unit)
  (lambda (vs inner a b)
    (if (null? vs)
        #u
        (let ((v (k-first-mentioned (extract (car vs) 2) inner)))
          (if (< v 0)
              (k-vals-known (cdr vs) inner a b)
              (k-fail (k-cat5 "`" (symbol->string (extract (car vs) 1)) "`'s type mentions `"
                              (k-dvar-string v) "`, which is not known outside the module")
                      a b))))))
;; `(module item …)`: each item checked in the scope of those before it;
;; the module's type, its abstract types bound in it.
(define k-synth-module (subr (maxeff checks spin) (kx k-items int int) k-te)
  (lambda (x items a b)
    (let* ((saved (k-mark))
           (named (get k-skolems))
           (made (k-module-items items a b (k-made-of nil nil nil nil)))
           (unbound (k-unbind-to saved))
           (vs (k-parts-reversed (extract made 3) nil))
           ;; A component's module, bound inside, has abstract types no one
           ;; outside can name.
           (known (k-vals-known vs (k-named-since named (get k-skolems) nil) a b))
           (popped (set k-skolems named))
           (abs (k-parts-reversed (extract made 1) nil))
           (t (k-ty-new (ty-module abs (k-parts-reversed (extract made 2) nil) vs))))
      (k-te-masked x t (extract made 4)))))

;;; ------------------------------------------------------------ with

;; The names of parts `ps`.
(define k-comp-names (subr (maxeff (read @globals) (alloc @t)) (k-parts) k-names)
  (lambda (ps) (if (null? ps) nil (cons (extract (car ps) 1) (k-comp-names (cdr ps))))))
;; Each of `ps` bound, the first first.
(define k-bind-parts (subr (maxeff kstate spin) (k-parts) unit)
  (lambda (ps)
    (if (null? ps)
        #u
        (begin (k-bind (extract (car ps) 1) (extract (car ps) 2)) (k-bind-parts (cdr ps))))))
;; `(with m body)`: the body with `m`'s values in scope, by name, at their
;; types for `m`.
(define k-synth-with (subr (maxeff checks spin) (kx symbol kx int int) k-te)
  (lambda (x m body a b)
    (let ((mt (k-lookup m)) (shown (symbol->string m)))
      (if (< mt 0)
          (k-fail (k-cat3 "`" shown "` is not bound") a b)
          (tagcase (k-get mt)
            (ty-module (abs ds vs)
              (let* ((noted (set k-with-vals (cons (product (1 a) (2 b) (3 (k-comp-names vs)))
                                                   (get k-with-vals))))
                     (naming (k-naming-effect m mt))
                     (saved (k-mark))
                     (bound (k-bind-parts vs))
                     (r (k-synth body))
                     (unbound (k-unbind-to saved)))
                (k-te-masked x (extract r 1) (k-union naming (extract r 2)))))
            (else y
              (let ((what (k-show-ty mt)))
                (k-fail (k-cat4 "`with` opens a module, and `" shown "` is a " what) a b))))))))

(define k-module-rule (subr (maxeff checks spin) (kx) k-te)
  (lambda (x)
    (tagcase x
      (x-module (items a b) (k-synth-module x items a b))
      (x-with (m body a b) (k-synth-with x m body a b))
      (else y (k-fail-at "a module" x)))))
(set k-module-rules k-module-rule)

;;; ------------------------------------------------------------ subtyping

;; A module type's abstract types, as binders of kind `type`.
(define k-abs-binders (subr (maxeff (read @globals) (alloc @t)) (k-parts) k-binders)
  (lambda (ps)
    (if (null? ps) nil (cons (product (1 (extract (car ps) 2)) (2 2)) (k-abs-binders (cdr ps))))))
(define k-same-comp-names? (subr kreads (k-parts k-parts) bool)
  (lambda (xs ys)
    (if (null? xs)
        (null? ys)
        (and (not (null? ys))
             (symbol=? (extract (car xs) 1) (extract (car ys) 1))
             (k-same-comp-names? (cdr xs) (cdr ys))))))
;; Components `xs` and `ys`, pairwise of one name, each the same type
;; (`same`) or each `x ≤ y`.
(define k-comps-sub?
  (subr (maxeff kstate spin) (bool k-parts k-parts k-benv k-benv k-strail k-labels) bool)
  (lambda (same xs ys ea eb trail labels)
    (or (null? xs)
        (let ((x (extract (car xs) 2)) (y (extract (car ys) 2)))
          (and (symbol=? (extract (car xs) 1) (extract (car ys) 1))
               (if same (k-inv x y ea eb trail labels) (k-sub x y ea eb trail labels))
               (k-comps-sub? same (cdr xs) (cdr ys) ea eb trail labels))))))
;; Modules of the same components, in order (`first-class-modules.md`, M1):
;; the abstract types paired as binders, as a `poly`'s are; descriptions
;; the same; values covariant.
(define k-sub-modules k-sub-rule
  (lambda (a b ta tb ea eb trail labels)
    (tagcase ta
      (ty-module (aa da va)
        (tagcase tb
          (ty-module (ab db vb)
            (and (k-same-comp-names? aa ab)
                 (= (k-length da) (k-length db))
                 (= (k-length va) (k-length vb))
                 (let* ((es (the k-benvs (cons ea eb)))
                        (ba (k-abs-binders aa))
                        (named (k-name-binders ba (k-abs-binders ab) a b 0 es labels)))
                   (and (k-comps-sub? #t da db (car named) (cdr named) trail labels)
                        (k-comps-sub? #f va vb (car named) (cdr named) trail labels)))))
          (else z #f)))
      (else z #f))))
(set k-sub-module k-sub-modules)

;;; ------------------------------------------------------------ termination

;; `sc` with `ns` hidden: bound, and none of the group's.
(define k-sc-hide-names (subr kstate (k-names k-tscope) k-tscope)
  (lambda (ns sc) (if (null? ns) sc (k-sc-hide-names (cdr ns) (k-sc-bind (car ns) nil sc)))))
;; A module's values made, each as any expression is.
(define k-sc-walk-items (subr (maxeff kstate spin) (k-items k-tscope k-guards) unit)
  (lambda (items sc gs)
    (if (null? items)
        #u
        (let* ((it (car items)) (k (extract it 1)) (ns (extract it 2)))
          (cond ((= k 0)
                 (let ((inner (k-sc-hide-names (k-conversions-onto (car ns) nil) sc)))
                   (k-sc-walk-items (cdr items) inner gs)))
                ((= k 1) (k-sc-walk-items (cdr items) sc gs))
                ((= k 2)
                 (begin (k-sc-walk-list (extract it 5) sc gs)
                        (k-sc-walk-items (cdr items) (k-sc-hide-names ns sc) gs)))
                (else
                 (let ((inner (k-sc-hide-names ns sc)))
                   (begin (k-sc-walk-list (extract it 5) inner gs)
                          (k-sc-walk-items (cdr items) inner gs)))))))))
;; A module's values made, and a `with`'s module named, each as any
;; expression or variable is.
(define k-sc-walk-modular (subr (maxeff kstate spin) (kx k-tscope k-guards) unit)
  (lambda (x sc gs)
    (tagcase x
      (x-module (items a b) (k-sc-walk-items items sc gs))
      (x-with (m body a b)
        (let ((member (k-sc-member sc m)))
          (begin (if (>= member 0) (k-sc-escape member) #u)
                 (k-sc-walk body (k-sc-hide-names (k-with-names a b) sc) gs))))
      (else y #u))))
(set k-sc-walk-module k-sc-walk-modular)
