;;; The compiler written in FX-26: programs. After `compile-inline.fx`.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((compile-programs-types (load-module "fx26:compile-programs-types.fx"))
       (compile-types (load-module "fx26:compile-types.fx"))
       (compile-exps-types (load-module "fx26:compile-exps-types.fx"))
       (compile-state-types (load-module "fx26:compile-state-types.fx"))
       (compile-plan-types (load-module "fx26:compile-plan-types.fx"))
       (regcode-types (load-module "fx26:regcode-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (table-types (load-module "fx26:table-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-env-types (load-module "fx26:check-env-types.fx"))
       (compile-twins-types (load-module "fx26:compile-twins-types.fx"))
       (regcode-exps-types (load-module "fx26:regcode-exps-types.fx"))
       (compile-inline-types (load-module "fx26:compile-inline-types.fx"))
       (regcode-helpers-types (load-module "fx26:regcode-helpers-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((compile (select compile-types compile-sig))
           (compile-exps (select compile-exps-types compile-exps-sig))
           (compile-plan (select compile-plan-types compile-plan-sig))
           (compile-twins (select compile-twins-types compile-twins-sig))
           (regcode-exps (select regcode-exps-types regcode-exps-sig))
           (compile-inline (select compile-inline-types compile-inline-sig))
           (regcode (select regcode-types regcode-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (tables (select table-types tables-sig))
           (regcode-helpers (select regcode-helpers-types regcode-helpers-sig))
           (layout (select layout-types layout-sig))
           (compile-state (select compile-state-types compile-state-sig)))
    (module
(define-type c-kept-globals (select compile-programs-types c-kept-globals))
(define-effect c-lists (select compile-programs-types c-lists))
(define-type c-const-env (select compile-programs-types c-const-env))
(define-type c-mconsts (select compile-programs-types c-mconsts))
(define-type c-members (select compile-programs-types c-members))
(define-type c-module-list (select compile-programs-types c-module-list))
;; The types it uses of the files before it.
(define at-global (with compile-types at-global))
(define-effect c-builds (select compile-types c-builds))
(define-effect c-emits (select compile-types c-emits))
(define-type c-globals-made (select compile-types c-globals-made))
(define c-ok (with compile-types c-ok))
(define-type c-params (select compile-types c-params))
(define-type c-recs (select compile-types c-recs))
(define-effect c-walks (select compile-types c-walks))
(define-type cenv (select compile-types cenv))
(define-type code (select compile-types code))
(define-effect compiles (select compile-types compiles))
(define-type cresult (select compile-types cresult))
(define-type exps (select compile-types exps))
(define-type items (select compile-types items))
(define-type syms (select compile-types syms))
(define-type c-inlinables (select compile-exps-types c-inlinables))
(define-type c-made (select compile-exps-types c-made))
(define-type c-mvals (select compile-exps-types c-mvals))
(define-type c-region (select compile-exps-types c-region))
(define-type c-specializables (select compile-plan-types c-specializables))
(define-type r-const-list (select regcode-types r-const-list))
(define-type r-member-const (select regcode-types r-member-const))
(define rc-bool (with regcode-types rc-bool))
(define rc-char (with regcode-types rc-char))
(define rc-int (with regcode-types rc-int))
(define rc-nil (with regcode-types rc-nil))
(define rc-pair (with regcode-types rc-pair))
(define rc-sym (with regcode-types rc-sym))
(define-type rconst (select regcode-types rconst))
(define-type rconsts (select regcode-types rconsts))
(define e-app (with parser-types e-app))
(define e-bool (with parser-types e-bool))
(define e-char (with parser-types e-char))
(define e-int (with parser-types e-int))
(define e-lambda (with parser-types e-lambda))
(define e-module (with parser-types e-module))
(define e-plambda (with parser-types e-plambda))
(define e-proj (with parser-types e-proj))
(define e-sym (with parser-types e-sym))
(define e-the (with parser-types e-the))
(define e-var (with parser-types e-var))
(define e-with (with parser-types e-with))
(define-type exp (select parser-types exp))
(define t-define (with parser-types t-define))
(define t-define-rec (with parser-types t-define-rec))
(define t-exp (with parser-types t-exp))
(define-type top (select parser-types top))
(define-type entry (select table-types entry))
(define-type k-run (select check-resolve-types k-run))
(define-type k-facts (select check-env-types k-facts))
;; What it uses of the modules it is given.
(define c-assemble (with compile c-assemble))
(define c-frozen-define-at (with compile c-frozen-define-at))
(define c-genv (with compile c-genv))
(define c-genv-count (with compile c-genv-count))
(define c-genv-index (with compile c-genv-index))
(define c-genv-push! (with compile c-genv-push!))
(define c-global-find (with compile c-global-find))
(define c-lambda-of (with compile c-lambda-of))
(define c-lit (with compile c-lit))
(define c-mentions? (with compile c-mentions?))
(define c-op (with compile c-op))
(define c-op1 (with compile c-op1))
(define c-set-facts! (with compile c-set-facts!))
(define c-tag (with compile c-tag))
(define c-this-params (with compile c-this-params))
(define c-where (with compile c-where))
(define c-defining (with compile-state c-defining))
(define c-exp (with compile-exps c-exp))
(define c-lambda (with compile-exps c-lambda))
(define c-made-now (with compile-state c-made-now))
(define c-made-reuse (with compile-state c-made-reuse))
(define c-module-members (with compile-state c-module-members))
(define c-module-values (with compile-state c-module-values))
(define c-word-name (with compile-state c-word-name))
(define c-drop-special (with compile-plan c-drop-special))
(define c-forget-inline! (with compile-plan c-forget-inline!))
(define c-inline-limit (with compile-plan c-inline-limit))
(define c-inline-room (with compile-plan c-inline-room))
(define c-inlines (with compile-plan c-inlines))
(define c-inlines-of (with compile-plan c-inlines-of))
(define c-note-inline! (with compile-plan c-note-inline!))
(define c-plan-top (with compile-plan c-plan-top))
(define c-specials (with compile-plan c-specials))
(define c-unrolls (with compile-plan c-unrolls))
(define c-form-twins (with compile-twins c-form-twins))
(define c-form-writes (with regcode-exps c-form-writes))
(define c-writes (with regcode-exps c-writes))
(define c-wrote! (with regcode-exps c-wrote!))
(define r-inline-named (with regcode-exps r-inline-named))
(define c-last-exp (with compile-inline c-last-exp))
(define c-plain-top (with compile-inline c-plain-top))
(define c-record-inline (with compile-inline c-record-inline))
(define c-resolve-extracts (with compile-inline c-resolve-extracts))
(define c-length-consts (with regcode c-length-consts))
(define r-const-globals (with regcode r-const-globals))
(define r-const-in (with regcode r-const-in))
(define r-const-lists (with regcode r-const-lists))
(define r-member-const (with regcode r-member-const))
(define r-module-consts (with regcode r-module-consts))
(define r-rev-consts (with regcode r-rev-consts))
(define exp-end (with check-resolve exp-end))
(define exp-start (with check-resolve exp-start))
(define make-table (with tables make-table))
(define std-nil-name? (with tables std-nil-name?))
(define symbol-hash (with tables symbol-hash))
(define table-ref (with tables table-ref))
(define table-set! (with tables table-set!))
(define r-const-list? (with regcode-helpers r-const-list?))
(define routine-drop (with layout routine-drop))
(define routine-exit (with layout routine-exit))
(define routine-global! (with layout routine-global!))

(define c-reuse (ref c-kept-globals @k) (new nil))
;; For a driver: a whole program from here, which sees none of the globals
;; made before it, as its checker begins again.
(define compile-forget-globals!
  (subr (maxeff (read (globals c-genv-index c-reuse make-table symbol-hash)) (write @k) (alloc @k))
        () unit)
  (lambda ()
    (begin (set c-genv-index (make-table symbol-hash symbol=?)) (set c-reuse nil))))

;; The global kept for `n`, if any.
(define c-kept (subr (read @globals) (c-kept-globals symbol) (listof wglobal acyclic))
  (lambda (ks n)
    (cond ((null? ks) nil)
          ((symbol=? (car (car ks)) n) (the (listof wglobal acyclic) (cons (cdr (car ks)) nil)))
          (else (c-kept (cdr ks) n)))))

;; `ks` without `n`'s.
(define c-unkeep (subr (read @globals) (c-kept-globals symbol) c-kept-globals)
  (lambda (ks n)
    (cond ((null? ks) ks)
          ((symbol=? (car (car ks)) n) (c-unkeep (cdr ks) n))
          (else (the c-kept-globals (cons (car ks) (c-unkeep (cdr ks) n)))))))

;; The counts of globals the bodies that may yet be inlined (`xs`), or
;; specialized (`ys`), saw when they were written: the limits a lookup of a
;; global may be made at (`c-global-find`) as definitions are made, when no
;; inlining or specialization is under way.
(define c-inline-limits (subr c-builds (c-inlinables) (listof int acyclic))
  (lambda (xs) (if (null? xs) nil (cons (extract (car xs) 5) (c-inline-limits (cdr xs))))))
(define c-special-limits (subr c-builds (c-specializables) (listof int acyclic))
  (lambda (ys) (if (null? ys) nil (cons (extract (car ys) 5) (c-special-limits (cdr ys))))))
;; `xs` before `ys`.
(define c-ints-onto (subr c-builds ((listof int acyclic) (listof int acyclic)) (listof int acyclic))
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (c-ints-onto (cdr xs) ys)))))
(define c-genv-limits (subr c-builds () (listof int acyclic))
  (lambda () (c-ints-onto (c-inline-limits (get c-inlines)) (c-special-limits (get c-specials)))))
;; Whether one of `limits` is past `lo` and no more than `hi`.
(define c-limit-in? (subr c-builds ((listof int acyclic) int int) bool)
  (lambda (limits lo hi)
    (and (not (null? limits))
         (or (and (< lo (car limits)) (<= (car limits) hi)) (c-limit-in? (cdr limits) lo hi)))))
;; Of `es`, a name's globals, newest first, each older than the one made
;; `upper`th: those a lookup at one of `limits` still finds. A lookup at
;; limit L finds the newest made before L, so a global made `i`th is found
;; only by a limit past `i` and no more than the next newer one's: kept,
;; any other would hold its value, and what that reaches, for good.
(define c-genv-needed (subr c-builds (c-globals-made int (listof int acyclic)) c-globals-made)
  (lambda (es upper limits)
    (if (null? es)
        nil
        (let ((i (car (car es))) (rest (c-genv-needed (cdr es) (car (car es)) limits)))
          (if (c-limit-in? limits i upper) (the c-globals-made (cons (car es) rest)) rest)))))
;; `n`'s globals, before its `i`th is made: those no lookup can find let go.
(define c-genv-prune! (subr c-emits (symbol int) unit)
  (lambda (n i)
    (let ((made (table-ref (get c-genv-index) n nil)))
      (table-set! (get c-genv-index) n (c-genv-needed made i (c-genv-limits))))))
;; `n`'s global for a definition of it: the one kept for it, if one was;
;; else a new one, which later uses of `n` refer to.
(define c-push-global (subr c-emits (symbol) wglobal)
  (lambda (n)
    (let ((kept (begin (c-forget-inline! n)
                       (table-set! (get c-unrolls) n nil)
                       (set c-specials (c-drop-special (get c-specials) n))
                       (c-kept (get c-reuse) n))))
      (if (null? kept)
          (let ((g (make-global n)) (i (get c-genv-count)))
            (begin (c-genv-prune! n i)
                   (c-genv-push! n i g)
                   (set c-genv-count (+ i 1))
                   g))
          (begin (set c-reuse (c-unkeep (get c-reuse) n)) (car kept))))))

;; For a driver: `n`'s next definition keeps the global `n` has now, so
;; that every use of `n`, before it and after, sees the new value.
(define compile-keep-global! (subr (maxeff c-emits spin) (symbol) unit)
  (lambda (n)
    (let ((l (c-global-find n -1)))
      (if (null? l)
          #u
          (tagcase (car l)
            (at-global (g) (set c-reuse (the c-kept-globals (cons (cons n g) (get c-reuse)))))
            (else y #u))))))

;; For a driver that computes a definition's value itself (the REPL, in the
;; native convention): `n`'s global from now on, made, for the driver to
;; fill.
(define compile-new-global (subr c-emits (symbol) wglobal)
  (lambda (n) (c-push-global n)))

;; For a driver that makes a global's value native code (the REPL, in the
;; native convention): `n`'s global, in a list, if it is one.
(define compile-global-cell (subr c-walks (symbol) (listof wglobal @k))
  (lambda (n)
    (let ((l (c-global-find n -1)))
      (if (null? l)
          nil
          (tagcase (car l)
            (at-global (g) (cons g nil))
            (else y nil))))))

;; A literal, under ascriptions, in a list: what a module's member may be
;; to be folded (`TODO.md` §42).
(define c-literal-of (subr c-lists (exp) rconsts)
  (lambda (x)
    (tagcase x
      (e-int (n a b) (the rconsts (cons (rc-int n) nil)))
      (e-bool (v a b) (the rconsts (cons (rc-bool v) nil)))
      (e-char (v a b) (the rconsts (cons (rc-char v) nil)))
      (e-the (d body a b) (c-literal-of body))
      (e-plambda (d body a b) (c-literal-of body))
      (e-proj (body ds a b) (c-literal-of body))
      (else y nil))))
;; Module `m`'s member `f`'s literal, in a list; none if it has none: by
;; the global `m` names, whose module's members were noted.
(define c-member-const (subr (maxeff compiles spin) (symbol symbol) rconsts)
  (lambda (m f)
    (let ((l (c-where (the cenv nil) m)))
      (if (null? l)
          nil
          (tagcase (car l)
            (at-global (g) (r-member-const g f))
            (else y nil))))))
;; The constant a top-level definition's expression is, in a list: a
;; literal; a constant global; a re-export of a module's literal member. As
;; the Rust compiler's `const_of`.
(define c-const-of (subr (maxeff compiles spin) (exp) rconsts)
  (lambda (x)
    (let ((lit (c-literal-of x)))
      (cond
        ((not (null? lit)) lit)
        ;; A list nothing writes, of literals: made once, here.
        ((c-frozen-define-at (exp-start x) (exp-end x)) (c-const-list x))
        (else
          (tagcase x
            (e-var (n a b)
              (let ((l (c-where (the cenv nil) n)))
                (if (null? l)
                    nil
                    (tagcase (car l)
                      (at-global (g) (r-const-in (get r-const-globals) g))
                      (else y nil)))))
            (e-with (m body a b)
              (tagcase body (e-var (f fa fb) (c-member-const m f)) (else y nil)))
            (else y nil)))))))
;; The list `x` makes, in a list, if it is one of literals (integers,
;; booleans, characters, symbols): `nil`, `(list e …)`, `(cons e l)`, a
;; global that is such a list, or a call of a small procedure noted to be
;; inlined (`c-inlines`) whose body makes one from its arguments. As the
;; Rust compiler's `const_list`.
(define c-const-list (subr (maxeff compiles spin) (exp) rconsts)
  (lambda (x)
    (let ((v (c-const-value x (the c-const-env nil) 0)))
      (if (and (not (null? v)) (tagcase (car v) (rc-pair (a d) #t) (rc-nil () #t) (else y #f)))
          v
          nil))))
(define c-const-in (subr c-lists (c-const-env symbol) rconsts)
  (lambda (e n)
    (cond ((null? e) nil)
          ((symbol=? (car (car e)) n) (the rconsts (cons (cdr (car e)) nil)))
          (else (c-const-in (cdr e) n)))))
;; What `x` is, as constant data, where its names are `env`'s: as the Rust
;; compiler's `const_value`, at most 16 calls deep.
(define c-const-value (subr (maxeff compiles spin) (exp c-const-env int) rconsts)
  (lambda (x env depth)
    (let ((lit (c-literal-of x)))
      (if (not (null? lit))
          lit
          (tagcase x
            (e-sym (s a b) (the rconsts (cons (rc-sym s) nil)))
            (e-the (d body a b) (c-const-value body env depth))
            (e-plambda (d body a b) (c-const-value body env depth))
            (e-proj (body ds a b) (c-const-value body env depth))
            (e-var (n a b)
              (let ((k (c-const-in env n)))
                (if (not (null? k))
                    k
                    (let ((l (c-where (the cenv nil) n)))
                      (if (null? l)
                          (if (std-nil-name? (symbol->string n))
                              (the rconsts (cons (rc-nil) nil))
                              nil)
                          (tagcase (car l)
                            (at-global (g) (r-const-in (get r-const-globals) g))
                            (else y nil)))))))
            (e-app (f args a b)
              (tagcase f
                (e-var (fname fa fb)
                  (let ((vs (c-const-values args env depth nil)))
                    (cond ((not (null? (c-const-in env fname))) nil)
                          ((null? vs) nil)
                          ((null? (c-where (the cenv nil) fname)) (c-const-standard fname (car vs)))
                          (else (c-const-call fname (car vs) depth)))))
                (else y nil)))
            (else y nil))))))
;; Each of `es`' constants, in order, in a list; none if one is not one.
(define c-const-values
  (subr (maxeff compiles spin) (exps c-const-env int rconsts) (listof rconsts @k))
  (lambda (es env depth acc)
    (if (null? es)
        (the (listof rconsts @k) (cons (r-rev-consts acc nil) nil))
        (let ((v (c-const-value (car es) env depth)))
          (if (null? v) nil (c-const-values (cdr es) env depth (cons (car v) acc)))))))
;; `list` or `cons` of constants `vs`.
(define c-const-standard (subr (maxeff compiles spin) (symbol rconsts) rconsts)
  (lambda (f vs)
    (cond ((string=? (symbol->string f) "list") (the rconsts (cons (c-const-list-of vs) nil)))
          ((and (string=? (symbol->string f) "cons") (= (c-length-consts vs) 2))
           (tagcase (car (cdr vs))
             (rc-pair (x d) (the rconsts (cons (rc-pair (car vs) (car (cdr vs))) nil)))
             (rc-nil () (the rconsts (cons (rc-pair (car vs) (car (cdr vs))) nil)))
             (else y nil)))
          (else nil))))
(define c-const-list-of (subr (maxeff compiles spin) (rconsts) rconst)
  (lambda (vs) (if (null? vs) (rc-nil) (rc-pair (car vs) (c-const-list-of (cdr vs))))))
;; A call of a small procedure noted to be inlined, on constants `vs`: its
;; body, its parameters the arguments, in the globals it saw.
(define c-const-call (subr (maxeff compiles spin) (symbol rconsts int) rconsts)
  (lambda (f vs depth)
    (let ((i (r-inline-named (c-inlines-of f) f (c-length-consts vs) (get c-genv))))
      (if (or (null? i) (>= depth 16))
          nil
          (let* ((outer (get c-genv))
                 (inner (c-const-bind (extract (car i) 3) vs))
                 (set-genv (set c-genv (extract (car i) 5)))
                 (v (c-const-value (extract (car i) 4) inner (+ depth 1))))
            (begin (set c-genv outer) v))))))
(define c-const-bind (subr (maxeff compiles spin) (c-params rconsts) c-const-env)
  (lambda (ps vs)
    (if (or (null? ps) (null? vs))
        nil
        (the c-const-env
          (cons (cons (extract (car ps) 1) (car vs)) (c-const-bind (cdr ps) (cdr vs)))))))
;; `cs` without global `g`'s.
(define c-consts-without (subr c-lists (r-const-list wglobal) r-const-list)
  (lambda (cs g)
    (cond ((null? cs) cs)
          ((wglobal=? (car (car cs)) g) (c-consts-without (cdr cs) g))
          (else (the r-const-list (cons (car cs) (c-consts-without (cdr cs) g)))))))
(define c-note-const-list! (subr (maxeff compiles spin) (wglobal rconst) unit)
  (lambda (g c)
    (let ((n (wglobal-name g)))
      (table-set! (get r-const-lists) n
                  (the r-const-list (cons (cons g c) (table-ref (get r-const-lists) n nil)))))))
(define c-forget-const-list! (subr (maxeff compiles spin) (wglobal) unit)
  (lambda (g)
    (let ((n (wglobal-name g)))
      (table-set! (get r-const-lists) n
                  (c-consts-without (table-ref (get r-const-lists) n nil) g)))))
(define c-modules-consts-without (subr c-lists (c-mconsts wglobal) c-mconsts)
  (lambda (ms g)
    (cond ((null? ms) ms)
          ((wglobal=? (car (car ms)) g) (c-modules-consts-without (cdr ms) g))
          (else (the c-mconsts (cons (car ms) (c-modules-consts-without (cdr ms) g)))))))
;; A module's values' literals, in order.
(define c-mvals-literal (subr c-lists (c-mvals) c-members)
  (lambda (vs)
    (if (null? vs)
        nil
        (let ((lit (c-literal-of (extract (car vs) 2))) (rest (c-mvals-literal (cdr vs))))
          (if (null? lit)
              rest
              (the c-members (cons (cons (extract (car vs) 1) (car lit)) rest)))))))
;; After a top-level definition of `x` set global `g`: whether `g` is a
;; constant now, and, if `x` is a module, its literal members. As the Rust
;; compiler's `note_constant`.
(define c-note-constant! (subr (maxeff compiles spin) (wglobal exp) unit)
  (lambda (g x)
    (let ((k (c-const-of x)))
      (begin
        (set r-const-globals (c-consts-without (get r-const-globals) g))
        (c-forget-const-list! g)
        (if (null? k)
            #u
            (begin
              (if (r-const-list? (car k)) (c-note-const-list! g (car k)) #u)
              (set r-const-globals
                   (the r-const-list (cons (cons g (car k)) (get r-const-globals))))))
        (set r-module-consts (c-modules-consts-without (get r-module-consts) g))
        (tagcase x
          (e-module (items a b)
            (set r-module-consts
                 (cons (cons g (c-mvals-literal (c-module-values items))) (get r-module-consts))))
          (else y #u))))))
(define c-note-constants! (subr (maxeff compiles spin) (c-recs (listof wglobal @k)) unit)
  (lambda (bs gs)
    (if (or (null? bs) (null? gs))
        #u
        (begin (c-note-constant! (car gs) (extract (car bs) 3))
               (c-note-constants! (cdr bs) (cdr gs))))))
(define c-rec-globals (subr c-emits (c-recs) (listof wglobal @k))
  (lambda (bs)
    (if (null? bs)
        nil
        (let ((g (c-push-global (extract (car bs) 1)))) (cons g (c-rec-globals (cdr bs)))))))

;; The next lambda's word named for global `n`.
(define c-name-word! (subr c-emits (symbol) unit)
  (lambda (n) (set c-word-name (the (listof string @k) (cons (symbol->string n) nil)))))
;; The next lambda's word named for global `n`, when `x`, its definition, is
;; a lambda, rather than for where its body starts: so that a profile, a
;; disassembly or a fault says which procedure. As the Rust compiler's
;; `name_word_for`.
(define c-name-for! (subr c-emits (symbol exp) unit)
  (lambda (n x)
    (let ((l (c-lambda-of x)))
      (if (null? l)
          #u
          (tagcase (car l)
            (e-lambda (ps body a b) (c-name-word! n))
            (else y #u))))))
(define c-rec-fill (subr (maxeff compiles spin) (c-recs (listof wglobal @k) code) unit)
  (lambda (bs gs c)
    (if (null? bs)
        #u
        (begin (c-name-for! (extract (car bs) 1) (extract (car bs) 3))
               (c-plan-top (extract (car bs) 3))
               (c-exp (extract (car bs) 3) (the cenv nil) 0 c #f)
               (c-form-twins)
               (c-op1 c routine-global! (wcell-global (car gs)))
               (c-wrote! (car gs))
               (c-rec-fill (cdr bs) (cdr gs) c)))))

;; The lambda of `ps` and `body` that top-level definition `n` is, made at
;; the top level, and noted to be inlined or specialized.
(define c-define-lambda (subr (maxeff compiles spin) (symbol c-params exp code) unit)
  (lambda (n ps body c)
    (begin (set c-defining (the (listof symbol @k) (cons n nil)))
           (c-name-word! n)
           (c-lambda ps body (the cenv nil) 0 c (the syms nil) (the c-region nil))
           (c-form-twins)
           (set c-defining (the (listof symbol @k) nil))
           (c-record-inline n ps body))))

(define c-modules (ref c-module-list @k) (new nil))
(define c-modules-without (subr c-builds (c-module-list symbol) c-module-list)
  (lambda (ms m)
    (cond ((null? ms) ms)
          ((symbol=? (extract (car ms) 1) m) (c-modules-without (cdr ms) m))
          (else (the c-module-list (cons (car ms) (c-modules-without (cdr ms) m)))))))
;; Whether `x` is a `module` form.
(define c-module? (subr (read @globals) (exp) bool)
  (lambda (x) (tagcase x (e-module (items a b) #t) (else y #f))))
;; After `(define m (module …))` is compiled: its members noted, kept by `m`.
(define c-keep-module! (subr c-emits (symbol) unit)
  (lambda (m)
    (let ((ms (get c-module-members)))
      (begin (set c-module-members nil)
             (if (null? ms)
                 #u
                 (let ((entry (product (1 m) (2 (car ms)))))
                   (set c-modules (the c-module-list (cons entry (get c-modules))))))))))
;; The members `m`, a top-level module, has noted, or none.
(define c-members-of (subr c-builds (c-module-list symbol) c-inlinables)
  (lambda (ms m)
    (cond ((null? ms) nil)
          ((symbol=? (extract (car ms) 1) m) (extract (car ms) 2))
          (else (c-members-of (cdr ms) m)))))
;; `n`, a re-export of member `f` of `ms`: inlined where called as `f` is,
;; if small, not calling itself and not staying cellular.
(define c-alias-inline! (subr (maxeff c-emits spin) (symbol symbol c-inlinables) unit)
  (lambda (n f ms)
    (cond ((null? ms) #u)
          ((symbol=? (extract (car ms) 1) f)
           (let* ((it (car ms)) (body (c-resolve-extracts (extract it 4))))
             (if (and (not (c-mentions? body 'stay-cellular))
                      (>= (c-inline-room body c-inline-limit) 0)
                      (not (c-mentions? body f)))
                 (let ((alias (product (1 n) (2 (extract it 2)) (3 (extract it 3)) (4 body)
                                       (5 (extract it 5)))))
                   (c-note-inline! alias))
                 #u)))
          (else (c-alias-inline! n f (cdr ms))))))
;; `(define n (with m f))`, `m` a top-level module whose member `f` is a
;; lambda naming no other member: `n` inlined where called, as the Rust
;; compiler's `reexport_inline`.
(define c-reexport-inline! (subr (maxeff c-emits spin) (symbol exp) unit)
  (lambda (n x)
    (tagcase x
      (e-with (m body a b)
        (tagcase body
          (e-var (f fa fb) (c-alias-inline! n f (c-members-of (get c-modules) m)))
          (else y #u)))
      (else y #u))))
;; Each form in turn; the last expression's value is left on the stack.
(define c-tops (subr (maxeff compiles spin) ((listof top acyclic) code bool) bool)
  (lambda (ts c has-value)
    (if (null? ts)
        has-value
        (tagcase (c-plain-top (car ts))
          (t-define (n ty x a b)
            (begin
              (if has-value (c-op c routine-drop) #u)
              ;; A module defined again no longer says what its re-exports are.
              (set c-modules (c-modules-without (get c-modules) n))
              ;; The global it writes, if one its body can name: one kept.
              (set c-form-writes
                   (let ((k (c-kept (get c-reuse) n)))
                     (if (null? k) nil (the (listof wglobal @k) (cons (car k) nil)))))
              (if (or (null? ty) (null? (c-lambda-of x)))
                  (begin (c-plan-top x)
                         (if (c-module? x)
                             (set c-module-members (the (listof c-inlinables @k) (list nil)))
                             #u)
                         (c-exp x (the cenv nil) 0 c #f)
                         (c-form-twins)
                         (if (c-module? x) (c-keep-module! n) #u)
                         ;; After its global, which forgets what `n` was.
                         (let ((g (c-push-global n)))
                           (begin (c-reexport-inline! n x)
                                  (c-note-constant! g x)
                                  (c-op1 c routine-global! (wcell-global g))
                                  (c-wrote! g))))
                  ;; A lambda: its global first, so that it can call itself,
                  ;; through the global, as any use of it does
                  ;; (`docs/fx26.md`, "Redefinition").
                  (let ((g (c-push-global n)))
                    (begin (set c-form-writes (cons g nil))
                           (c-note-constant! g x)
                           (c-plan-top x)
                           (tagcase (car (c-lambda-of x))
                             (e-lambda (ps body la lb) (c-define-lambda n ps body c))
                             (else y (begin (c-exp x (the cenv nil) 0 c #f) (c-form-twins))))
                           (c-op1 c routine-global! (wcell-global g))
                           (c-wrote! g))))
              (c-tops (cdr ts) c #f)))
          ;; Every name's global first; then each lambda, which runs nothing.
          (t-define-rec (bs a b)
            (begin
              (if has-value (c-op c routine-drop) #u)
              (let ((gs (c-rec-globals bs)))
                (begin (set c-form-writes gs) (c-note-constants! bs gs) (c-rec-fill bs gs c)))
              (c-tops (cdr ts) c #f)))
          (t-exp (x)
            (begin (if has-value (c-op c routine-drop) #u)
                   (set c-form-writes nil)
                   (set c-last-exp (the (listof exp @k) (cons x nil)))
                   (c-plan-top x)
                   (c-exp x (the cenv nil) 0 c #f)
                   (c-form-twins)
                   (c-tops (cdr ts) c #t)))
          (else y (c-tops (cdr ts) c has-value))))))

;; Each of `bs`' names' next definition keeps the global it has.
(define c-keep-rec-names (subr (maxeff c-emits spin) (c-recs) unit)
  (lambda (bs)
    (if (null? bs)
        #u
        (begin (compile-keep-global! (extract (car bs) 1)) (c-keep-rec-names (cdr bs))))))

;; Before a run that assigns its names' globals (`checked-tops`): each
;; name's next definition keeps the global it has.
(define c-keep-names (subr (maxeff c-emits spin) (top) unit)
  (lambda (t)
    (tagcase t
      (t-define (n ty x a b) (compile-keep-global! n))
      (t-define-rec (bs a b) (c-keep-rec-names bs))
      (else y #u))))

;; What a checked program runs (`checked-tops`), each in turn: whether the
;; last was an expression, whose value stays.
(define c-runs (subr (maxeff compiles spin) ((listof k-run acyclic) code bool) bool)
  (lambda (rs c has-value)
    (if (null? rs)
        has-value
        (let* ((r (car rs)) (tops (the (listof top acyclic) (cons (extract r 1) nil))))
          (begin (if (extract r 2) (c-keep-names (extract r 1)) #u)
                 (c-runs (cdr rs) c (c-tops tops c has-value)))))))

;; A program's one word, which runs it and leaves the value of its last
;; expression (unit, if it has none): what `forms` compiles onto the code
;; it is given, saying whether the last form was an expression; `facts`,
;; what checking found.
(define c-program
  (subr (maxeff compiles (comefrom @y) spin) ((subr (maxeff compiles spin) (code) bool) k-facts)
        cresult)
  (lambda (forms facts)
    (prompt c-tag
      (let ((c (the code (new nil))))
        (begin
          (c-set-facts! facts)
          ;; Constants are a program's own, as the Rust compiler's are
          ;; (`TODO.md` §42; at the REPL, none yet).
          (set r-const-globals nil)
          (set r-const-lists (make-table symbol-hash symbol=?))
          (set r-module-consts nil)
          ;; So are the counts of writes the guards expect.
          (set c-writes (make-table symbol-hash symbol=?))
          (set c-form-writes nil)
          (set c-this-params -1)
          ;; The lambdas made so far are the last program's: let them go.
          (set c-made-now (the (listof c-made @k) nil))
          (set c-made-reuse (the (listof c-made @k) nil))
          (if (forms c) #u (c-lit c (wcell-unit)))
          (c-op c routine-exit)
          (c-ok (c-assemble c (string->symbol "program")))))
      (lambda (r) r))))

;; The entry point for a program the checker written in FX-26 checked: what
;; it runs (`checked-tops`, under redefinition), and what checking found.
(define compile-checked
  (subr (maxeff compiles (comefrom @y) spin) ((listof k-run acyclic) k-facts) cresult)
  (lambda (runs facts) (c-program (lambda (c) (c-runs runs c #f)) facts)))

;; The entry point: a checked program's trees, and what checking found.
(define compile-program
  (subr (maxeff compiles (comefrom @y) spin) ((listof top acyclic) k-facts) cresult)
  (lambda (tops facts) (c-program (lambda (c) (c-tops tops c #f)) facts))))))
