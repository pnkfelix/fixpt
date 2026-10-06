;;; The compiler written in FX-26: the middle phase's procedure table
;;; (`docs/research/compiler-middle-phase.md`, step 2), as the Rust
;;; compiler's `cellular/procs.rs`. Before a top-level form is compiled,
;;; each lambda it makes and each `letrec`'s lifting are decided by a walk of
;;; their own, with the stack compiler's scoping, arm for arm, in
;;; environments whose places are only their kinds (a slot, a free value, a
;;; sibling not made yet, a loop, a lifted procedure); the decisions are the
;;; compiler's own (`c-lambda-captured`, `c-lift-plan`, `c-loops-only`), and
;;; the stack code reads them (`c-planned-fv`, `c-planned-lift`). Lambdas
;;; only register code compiles are not in it (step 3). After
;;; `compile-exps.fx`.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define compile-plan-module (module
;; The names `ns` bound in slots, onto `e`: only their kind counts.
(define p-slots (subr (maxeff (read @globals) (alloc @k)) (syms cenv) cenv)
  (lambda (ns e) (if (null? ns) e (p-slots (cdr ns) (c-extend (car ns) (at-slot 0) e)))))
(define p-let-names (subr (maxeff (read @globals) (alloc @k)) (c-binds) syms)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 1) (p-let-names (cdr bs))))))
;; Lambda `ps` `body`'s plan noted: its parameters' names, and what it
;; captures.
(define p-note (subr (maxeff c-emits spin) (c-params exp syms) unit)
  (lambda (ps body fv)
    (let ((key (c-span-key (exp-start body) (exp-end body))))
      (table-set! (get c-plan-procs) key
                  (cons (product (1 (c-bind-params ps nil)) (2 fv))
                        (table-ref (get c-plan-procs) key (the c-planneds nil)))))))

(define-rec
  (p-exps (subr (maxeff compiles spin) (exps cenv) unit)
    (lambda (xs e) (if (null? xs) #u (begin (p-exp (car xs) e #f) (p-exps (cdr xs) e)))))
  ;; As `c-exp`: a conversion or a reshaping makes the value as it is, not
  ;; in tail position.
  (p-exp (subr (maxeff compiles spin) (exp cenv bool) unit)
    (lambda (x e tail0)
      (let ((tail (and tail0 (< (c-conversion-at x) 0) (null? (c-reshape-at x)))))
        (tagcase x
          (e-lambda (ps body a b) (p-lambda ps body e (the syms nil)))
          (e-rlambda (r l a b)
            (begin (p-exp r e #f)
                   (tagcase l (e-lambda (ps body la lb) (p-lambda ps body e (the syms nil)))
                     (else y #u))))
          (e-app (f args a b)
            (let ((l (c-applied-let f args)))
              (if (null? l)
                  (begin (p-exps args e)
                         ;; A lifted procedure's name, or a standard one's, is
                         ;; not made as a value.
                         (if (and (< (c-lifted-at f e) 0) (string=? (c-standard-name f e) ""))
                             (p-exp f e #f)
                             #u))
                  (p-let (extract (car l) 1) (extract (car l) 2) e tail))))
          (e-plambda (d body a b) (p-exp body e tail))
          (e-proj (body ds a b) (p-exp body e tail))
          (e-the (d body a b) (p-exp body e tail))
          (e-convention (cnv body a b) (p-exp body e tail))
          (e-letregion (k r i body a b)
            (if (or (= k 0) (= k 3))
                (p-exp body e tail)
                (p-exp body (c-extend r (at-slot 0) e) #f)))
          (e-if (t th el a b) (begin (p-exp t e #f) (p-exp th e tail) (p-exp el e tail)))
          (e-let (bs body a b) (p-let bs body e tail))
          (e-letrec (bs body a b) (p-letrec bs body a b e tail))
          (e-begin (es a b) (p-begin es e tail))
          (e-prompt (t body h a b)
            (begin (p-exp t e #f) (p-exp h e #f)
                   (p-lambda (the c-params nil) body e (the syms nil))))
          (e-bloblet (op i args a b) (p-exps args e))
          (e-product (fs a b) (p-exps (c-bound-exps fs) e))
          (e-extract (p l a b) (p-exp p e #f))
          (e-sum (t v a b) (p-exp v e #f))
          (e-tagcase (s arms els a b) (begin (p-exp s e #f) (p-arms arms els e tail)))
          (e-module (items a b)
            (let ((vs (c-module-values items))) (p-module vs e (c-module-slots vs 0))))
          (e-with (m body a b)
            (let ((ns (c-with-at a b)))
              (if (null? ns) #u (p-exp body (p-slots (car ns) e) tail))))
          (else y #u)))))
  (p-begin (subr (maxeff compiles spin) (exps cenv bool) unit)
    (lambda (es e tail)
      (cond ((null? es) #u)
            ((null? (cdr es)) (p-exp (car es) e tail))
            (else (begin (p-exp (car es) e #f) (p-begin (cdr es) e tail))))))
  (p-let (subr (maxeff compiles spin) (c-binds exp cenv bool) unit)
    (lambda (bs body e tail)
      (begin (p-exps (c-bound-exps bs) e) (p-exp body (p-slots (p-let-names bs) e) tail))))
  (p-arms (subr (maxeff compiles spin) (c-cases c-binds cenv bool) unit)
    (lambda (arms els e tail)
      (if (null? arms)
          (if (null? els)
              #u
              (p-exp (extract (car els) 2) (c-extend (extract (car els) 1) (at-slot 0) e) tail))
          (let ((arm (car arms)))
            (begin
              (p-exp (extract arm 4)
                     (if (extract arm 2)
                         (p-slots (extract arm 3) e)
                         (c-extend (car (extract arm 3)) (at-slot 0) e))
                     tail)
              (p-arms (cdr arms) els e tail))))))
  ;; As `c-letrec-or-lift`: lifted, each member's lambda in what it knows
  ;; (the lifted procedures), taking its added names first; else each
  ;; closure made with its siblings pending.
  (p-letrec (subr (maxeff compiles spin) (c-recs exp int int cenv bool) unit)
    (lambda (bs body a b e tail)
      (let ((plan (c-lift-plan bs body e tail)))
        (begin
          (table-set! (get c-plan-lifts) (c-span-key a b) plan)
          (if (null? plan)
              (begin (p-rec-lambdas bs bs e 0) (p-exp body (c-letrec-slots bs e 0) tail))
              (let ((ks (c-lift-closures bs (car plan) 0)))
                (begin (p-lifted bs (car plan) ks (c-bind-lifted bs ks (c-lifted-entries e)) 0)
                       (p-exp body (c-bind-lifted bs ks e) tail))))))))
  (p-rec-lambdas (subr (maxeff compiles spin) (c-recs c-recs cenv int) unit)
    (lambda (all bs e i)
      (if (null? bs)
          #u
          (begin
            (tagcase (car (c-lambda-of (extract (car bs) 3)))
              (e-lambda (ps body a b)
                (p-lambda ps body (c-letrec-own all e 0 0 i body (c-count-params ps))
                          (the syms (cons (extract (car bs) 1) nil))))
              (e-rlambda (r l a b)
                (tagcase l
                  (e-lambda (ps body la lb)
                    (let ((own (c-letrec-own all e 0 0 i body (c-count-params ps))))
                      (begin (p-exp r own #f)
                             (p-lambda ps body own (the syms (cons (extract (car bs) 1) nil))))))
                  (else y #u)))
              (else y #u))
            (p-rec-lambdas all (cdr bs) e (+ i 1))))))
  (p-lifted (subr (maxeff compiles spin) (c-recs c-added (listof int @k) cenv int) unit)
    (lambda (bs added ks known i)
      (if (null? bs)
          #u
          (begin
            (tagcase (car (c-lambda-of (extract (car bs) 3)))
              (e-lambda (ps lbody la lb)
                (let* ((name (extract (car bs) 1))
                       (own (if (c-loops-only lbody name (c-count-params ps) #t)
                                (the syms (cons name nil))
                                (the syms nil))))
                  (p-lambda (c-added-params (array-ref added i) ps) lbody known own)))
              (else y #u))
            (p-lifted (cdr bs) added (cdr ks) known (+ i 1))))))
  ;; As `c-module-make`: each value made in order, a lambda naming an item
  ;; not made yet capturing it as a `letrec`'s sibling is.
  (p-module (subr (maxeff compiles spin) (c-mvals cenv c-mslots) unit)
    (lambda (vs e later)
      (if (null? vs)
          #u
          (let* ((v (car vs)) (n (extract v 1)) (x (extract v 2)))
            (begin
              (if (and (extract v 4) (c-names-any? x later))
                  (p-module-lambda n x e later)
                  (p-exp x e #f))
              (p-module (cdr vs) (c-extend n (at-slot 0) e) (cdr later)))))))
  (p-module-lambda (subr (maxeff compiles spin) (symbol exp cenv c-mslots) unit)
    (lambda (n x e later)
      (tagcase (car (c-lambda-of x))
        (e-lambda (ps body a b)
          (p-lambda ps body (c-module-own n e later body (c-count-params ps))
                    (the syms (cons n nil))))
        (e-rlambda (r l a b)
          (tagcase l
            (e-lambda (ps body la lb)
              (let ((own (c-module-own n e later body (c-count-params ps))))
                (begin (p-exp r own #f) (p-lambda ps body own (the syms (cons n nil))))))
            (else y #u)))
        (else y #u))))
  ;; As `c-lambda-word-in`: what its closure captures in `e`, noted; then
  ;; its body, in the scope its word has, in tail position.
  (p-lambda (subr (maxeff compiles spin) (c-params exp cenv syms) unit)
    (lambda (ps body e own0)
      (let* ((fv (c-lambda-captured ps body e))
             (own (c-own-of ps own0)))
        (begin
          (p-note ps body fv)
          (p-exp body (c-inner-env fv e (c-param-env ps 0 (c-own-scope own fv e)) 0) #t))))))

;; The plan of top-level form `x`, compiled next, in no scope. The lifted
;; procedures it would make are counted as the compile will make them, and
;; forgotten after. Not in register code, whatever a failed compile left.
(define c-plan-top (subr (maxeff compiles spin) (exp) unit)
  (lambda (x)
    (let ((count (get c-lift-count)))
      (begin (set c-plan-procs (make-table c-int-hash c-int=?))
             (set c-plan-lifts (make-table c-int-hash c-int=?))
             (set c-planning #t)
             (set c-twin-depth 0)
             (p-exp x (the cenv nil) #f)
             (set c-lift-count count)))))
))

(define c-plan-top (with compile-plan-module c-plan-top))
