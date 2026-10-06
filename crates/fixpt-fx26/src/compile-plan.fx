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
;;; ------------------------------------------- what calls may become
;;; The globals a call may be inlined as, or specialized as, as the program
;;; loop (`compile-programs.fx`) notes them; the plan reads them (step 3),
;;; and register code.

;; The most parser-tree nodes a body may have to be inlined
;; (`c-inline-room`).
(define c-inline-limit int 20)

(define c-inlines (ref c-inlinables @k) (new nil))

;; The globals whose bodies are being inlined, which are not again.
(define c-inlining (ref syms @k) (new nil))

;; `xs` without `n`'s.
(define c-drop-inline (subr c-builds (c-inlinables symbol) c-inlinables)
  (lambda (xs n)
    (cond ((null? xs) xs)
          ((symbol=? (extract (car xs) 1) n) (c-drop-inline (cdr xs) n))
          (else (the c-inlinables (cons (car xs) (c-drop-inline (cdr xs) n)))))))

;; The most a procedure's body may have to be specialized at a lambda
;; (`c-inline-room`).
(define c-special-limit int 60)

;; A global procedure whose parameter (6) is only called, with (7)
;; arguments, or passed as itself to a call of the procedure: a call with a
;; lambda there may run a copy of the procedure made for that lambda, the
;; lambda's body inlined where the parameter is called (`regcode.fx`'s
;; `r-specialize`). Its name, word, parameters, body and globals, as for
;; `c-inline`.
(define-type c-special
  (productof (1 symbol) (2 tword) (3 c-params) (4 exp) (5 int) (6 int) (7 int)))

(define-type c-specializables (listof c-special acyclic))

(define c-specials (ref c-specializables @k) (new nil))

;; `xs` without `n`'s.
(define c-drop-special (subr c-builds (c-specializables symbol) c-specializables)
  (lambda (xs n)
    (cond ((null? xs) xs)
          ((symbol=? (extract (car xs) 1) n) (c-drop-special (cdr xs) n))
          (else (the c-specializables (cons (car xs) (c-drop-special (cdr xs) n)))))))

;; A procedure being specialized at a lambda: its global's name, cell and
;; word; the parameter's place and name; how many parameters; the lambda's
;; arity, parameters and body, the names its closure captures in order, and
;; the globals it sees.
(define-type c-spec
  (productof (1 symbol) (2 wglobal) (3 tword) (4 int) (5 symbol) (6 int) (7 int)
             (8 c-params) (9 exp) (10 syms) (11 int)))

(define c-spec-now (ref (listof c-spec @k) @k) (new nil))

;; The `k`th of `es`.
(define c-nth (subr (read @globals) (exps int) exp)
  (lambda (es k) (if (= k 0) (car es) (c-nth (cdr es) (- k 1)))))

;; How many of `n` parser-tree nodes are left once `x`'s are counted, as the
;; Rust compiler's `inline_room` counts them: negative, and counted no
;; further, once they run out, or at a form that makes a closure, which an
;; inlined body would have to capture its slots in.
(define-rec
  (c-inline-room (subr (maxeff (read @globals) spin) (exp int) int)
    (lambda (x n0)
      (let ((n (- n0 1)))
        (if (< n 0)
            n
            (tagcase x
              (e-lambda (ps body a b) -1)
              (e-rlambda (r l a b) -1)
              (e-letrec (bs body a b) -1)
              (e-prompt (t body h a b) -1)
              (e-module (items a b) -1)
              (e-with (m body a b) -1)
              (e-app (f args a b) (c-inline-room-all args (c-inline-room f n)))
              (e-plambda (d body a b) (c-inline-room body n))
              (e-proj (body ds a b) (c-inline-room body n))
              (e-the (d body a b) (c-inline-room body n))
              (e-convention (cnv body a b) (c-inline-room body n))
              (e-letregion (k r i body a b) (c-inline-room body n))
              (e-if (t th el a b) (c-inline-room-if el (c-inline-room-if th (c-inline-room t n))))
              (e-let (bs body a b) (c-inline-room-if body (c-inline-room-let bs n)))
              (e-begin (es a b) (c-inline-room-all es n))
              (e-bloblet (op i args a b) (c-inline-room-all args n))
              (e-product (fs a b) (c-inline-room-let fs n))
              (e-extract (p l a b) (c-inline-room p n))
              (e-sum (t v a b) (c-inline-room v n))
              (e-tagcase (s arms els a b)
                (c-inline-room-else els (c-inline-room-arms arms (c-inline-room s n))))
              (else y n))))))
  ;; `x`'s nodes counted from `n`, unless none are left.
  (c-inline-room-if (subr (maxeff (read @globals) spin) (exp int) int)
    (lambda (x n) (if (< n 0) n (c-inline-room x n))))
  (c-inline-room-all (subr (maxeff (read @globals) spin) (exps int) int)
    (lambda (es n)
      (if (or (null? es) (< n 0)) n (c-inline-room-all (cdr es) (c-inline-room (car es) n)))))
  (c-inline-room-let (subr (maxeff (read @globals) spin) (c-binds int) int)
    (lambda (bs n)
      (if (or (null? bs) (< n 0))
          n
          (c-inline-room-let (cdr bs) (c-inline-room (extract (car bs) 2) n)))))
  (c-inline-room-arms (subr (maxeff (read @globals) spin) (c-cases int) int)
    (lambda (arms n)
      (if (or (null? arms) (< n 0))
          n
          (c-inline-room-arms (cdr arms) (c-inline-room (extract (car arms) 4) n)))))
  (c-inline-room-else (subr (maxeff (read @globals) spin) (c-binds int) int)
    (lambda (els n) (if (or (null? els) (< n 0)) n (c-inline-room (extract (car els) 2) n)))))
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
(define c-plan-calls (ref (table int c-calls-at @k) @k) (new (make-table c-int-hash c-int=?)))
(define c-plan-inlined (ref (table int c-inlined-at @k) @k) (new (make-table c-int-hash c-int=?)))
(define c-plan-contexts (ref int @k) (new 1))
(define c-no-calls (ref c-calls-at @k) (new (make-table c-int-hash c-int=?)))
;; While the plan is made: the context it is in, and the names whose bodies
;; it is inlining on the way there. While register code is made: the
;; contexts of the bodies it is inlining, innermost first (-1 where the
;; plan has none).
(define c-plan-now (ref int @k) (new 0))
(define c-plan-inlining (ref syms @k) (new nil))
(define c-r-plan-ctx (ref (listof int @k) @k) (new nil))
;; Context `c`'s for the body of `n` taking `k` arguments, or -1.
(define c-plan-child (subr c-walks (int symbol int) int)
  (lambda (c n k)
    (letrec ((find (subr c-walks (c-inlined-at) int)
               (lambda (xs)
                 (cond ((null? xs) -1)
                       ((and (symbol=? (extract (car xs) 1) n) (= (extract (car xs) 2) k))
                        (extract (car xs) 3))
                       (else (find (cdr xs)))))))
      (find (table-ref (get c-plan-inlined) c (the c-inlined-at nil))))))
;; Call `a`-`b` noted as planned, in the context the plan is in.
(define p-note-call (subr (maxeff c-emits spin) (int int c-called) unit)
  (lambda (a b called)
    (let ((c (get c-plan-now)))
      (begin
        (if (table-has? (get c-plan-calls) c)
            #u
            (table-set! (get c-plan-calls) c (make-table c-int-hash c-int=?)))
        (table-set! (table-ref (get c-plan-calls) c (get c-no-calls)) (c-span-key a b) called)))))
;; The one of `xs` that `n`, taking `k` arguments, names, if any.
(define p-inline-named (subr (maxeff (read @globals) (alloc @k)) (c-inlinables symbol int)
                            (listof c-inline acyclic))
  (lambda (xs n k)
    (cond ((null? xs) nil)
          ((and (symbol=? (extract (car xs) 1) n) (= (c-count-params (extract (car xs) 3)) k))
           (the (listof c-inline acyclic) (cons (car xs) nil)))
          (else (p-inline-named (cdr xs) n k)))))
(define p-special-named (subr (maxeff (read @globals) (alloc @k)) (c-specializables symbol int)
                             (listof c-special acyclic))
  (lambda (xs n k)
    (cond ((null? xs) nil)
          ((and (symbol=? (extract (car xs) 1) n) (= (c-count-params (extract (car xs) 3)) k))
           (the (listof c-special acyclic) (cons (car xs) nil)))
          (else (p-special-named (cdr xs) n k)))))
;; `sp` and the lambda argument at its parameter, in a list, when that is a
;; lambda small enough to inline, taking as many arguments as it is called
;; with.
(define p-special-lambda (subr (maxeff c-builds spin) (c-special exps) c-spec-calls)
  (lambda (sp args)
    (let ((lam (c-nth args (extract sp 6))))
      (tagcase lam
        (e-lambda (ps body la lb)
          (if (and (= (c-count-params ps) (extract sp 7))
                   (>= (c-inline-room body c-inline-limit) 0))
              (the c-spec-calls (cons (product (1 sp) (2 lam)) nil))
              nil))
        (else y nil)))))
;; Call `a`-`b` as planned, in a list, where call sites are the plan's: in
;; a planned lambda's own register code, or a body inlined in it, outside
;; any copy;
;; a call of no global, planned as neither. None elsewhere, where register
;; code decides.
(define c-planned-call (subr c-builds (int int) (listof c-called @k))
  (lambda (a b)
    (let ((c (if (null? (get c-r-plan-ctx)) 0 (car (get c-r-plan-ctx)))))
      (if (or (not (get c-r-in-plan)) (not (null? (get c-spec-now))) (< c 0))
          nil
          (the (listof c-called @k)
               (cons (table-ref (table-ref (get c-plan-calls) c (get c-no-calls)) (c-span-key a b)
                                (the c-called (product (1 nil) (2 nil))))
                     nil))))))

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
                  (begin (p-call f args a b e)
                         (p-exps args e)
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
  ;; Call `f` `args` at `a`-`b`, in `e`, planned: as the Rust compiler's
  ;; `plan_call`, and register code's `r-inlined` and `r-specialized`; a body
  ;; it inlines planned too, once in each context.
  (p-call (subr (maxeff compiles spin) (exp exps int int cenv) unit)
    (lambda (f args a b e)
      (tagcase f
        (e-var (n fa fb)
          (let ((l (c-where e n)))
            (if (or (null? l) (not (c-global? (car l))))
                #u
                (let* ((k (c-count-exps args))
                       (sp (p-special-named (get c-specials) n k))
                       (spl (if (null? sp) (the c-spec-calls nil) (p-special-lambda (car sp) args)))
                       ;; Not a body being inlined on the way here.
                       (inl (if (c-member? (get c-plan-inlining) n)
                                (the (listof c-inline acyclic) nil)
                                (p-inline-named (get c-inlines) n k))))
                  (begin
                    (p-note-call a b (product (1 inl) (2 spl)))
                    (if (or (null? inl) (>= (c-plan-child (get c-plan-now) n k) 0))
                        #u
                        (p-inlined (car inl) k)))))))
        (else y #u))))
  ;; The body of `i`, taking `k` arguments, planned as `r-inline` compiles
  ;; it: its parameters local, in the globals it saw, its name not inlined in
  ;; it again. (An inlined body makes no closure: `c-inline-room`.)
  (p-inlined (subr (maxeff compiles spin) (c-inline int) unit)
    (lambda (i k)
      (let ((c (get c-plan-contexts)) (outer (get c-plan-now))
            (outer-inlining (get c-plan-inlining)) (outer-genv (get c-genv)))
        (begin
          (set c-plan-contexts (+ c 1))
          (table-set! (get c-plan-inlined) outer
                      (cons (product (1 (extract i 1)) (2 k) (3 c))
                            (table-ref (get c-plan-inlined) outer (the c-inlined-at nil))))
          (set c-plan-now c)
          (set c-plan-inlining (cons (extract i 1) outer-inlining))
          (set c-genv (extract i 5))
          (p-exp (extract i 4) (p-slots (c-bind-params (extract i 3) nil) (the cenv nil)) #f)
          (set c-genv outer-genv)
          (set c-plan-inlining outer-inlining)
          (set c-plan-now outer)))))
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
             (set c-plan-calls (make-table c-int-hash c-int=?))
             (set c-plan-inlined (make-table c-int-hash c-int=?))
             (set c-plan-contexts 1)
             (set c-plan-now 0)
             (set c-plan-inlining nil)
             (set c-r-plan-ctx nil)
             (set c-planning #t)
             (set c-form-made nil)
             (set c-twin-depth 0)
             (p-exp x (the cenv nil) #f)
             (set c-lift-count count)))))
))

(define c-plan-top (with compile-plan-module c-plan-top))
(define c-inline-limit (with compile-plan-module c-inline-limit))
(define c-inlines (with compile-plan-module c-inlines))
(define c-inlining (with compile-plan-module c-inlining))
(define c-drop-inline (with compile-plan-module c-drop-inline))
(define c-special-limit (with compile-plan-module c-special-limit))
(define-type c-special (select compile-plan-module c-special))
(define-type c-specializables (select compile-plan-module c-specializables))
(define c-specials (with compile-plan-module c-specials))
(define c-drop-special (with compile-plan-module c-drop-special))
(define-type c-spec (select compile-plan-module c-spec))
(define c-spec-now (with compile-plan-module c-spec-now))
(define c-nth (with compile-plan-module c-nth))
(define c-inline-room (with compile-plan-module c-inline-room))
(define-type c-spec-call (select compile-plan-module c-spec-call))
(define-type c-spec-calls (select compile-plan-module c-spec-calls))
(define-type c-called (select compile-plan-module c-called))
(define c-planned-call (with compile-plan-module c-planned-call))
(define c-r-plan-ctx (with compile-plan-module c-r-plan-ctx))
(define c-plan-child (with compile-plan-module c-plan-child))
