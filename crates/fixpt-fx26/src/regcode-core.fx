;;; Register code, in FX-26: the expressions' compiler proper, one
;;; recursive group, modules and a leaf's tail calls included. After
;;; `regcode-modules.fx`. Over the size limit by the user's decision
;;; (2026-10-06, `crates/fixpt-tidy/fx-size-debt.txt`), to be revisited.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((regcode-types (load-module "fx26:regcode-types.fx"))
       (compile-types (load-module "fx26:compile-types.fx"))
       (compile-exps-types (load-module "fx26:compile-exps-types.fx"))
       (compile-plan-types (load-module "fx26:compile-plan-types.fx"))
       (regcode-exps-types (load-module "fx26:regcode-exps-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (regcode-helpers-types (load-module "fx26:regcode-helpers-types.fx"))
       (regcode-modules-types (load-module "fx26:regcode-modules-types.fx"))
       (compile-lift-types (load-module "fx26:compile-lift-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((regcode (select regcode-types regcode-sig))
           (compile (select compile-types compile-sig))
           (compile-lift (select compile-lift-types compile-lift-sig))
           (compile-exps (select compile-exps-types compile-exps-sig))
           (compile-plan (select compile-plan-types compile-plan-sig))
           (regcode-exps (select regcode-exps-types regcode-exps-sig))
           (layout (select layout-types layout-sig))
           (regcode-helpers (select regcode-helpers-types regcode-helpers-sig))
           (regcode-modules (select regcode-modules-types regcode-modules-sig)))
    (module

;; The types it uses of the files before it.
(define a-as-is (with regcode-types a-as-is))
(define a-e (with regcode-types a-e))
(define a-lexical (with regcode-types a-lexical))
(define a-name (with regcode-types a-name))
(define a-slot (with regcode-types a-slot))
(define a-thunk (with regcode-types a-thunk))
(define a-v (with regcode-types a-v))
(define-type bools (select regcode-types bools))
(define r-branch (with regcode-types r-branch))
(define r-brancht (with regcode-types r-brancht))
(define r-label (with regcode-types r-label))
(define-type rarg (select regcode-types rarg))
(define-type rargs (select regcode-types rargs))
(define-effect rcompiles (select regcode-types rcompiles))
(define-type renv (select regcode-types renv))
(define-type rgen (select regcode-types rgen))
(define-type rints (select regcode-types rints))
(define rl-const (with regcode-types rl-const))
(define rl-free (with regcode-types rl-free))
(define rl-join (with regcode-types rl-join))
(define rl-reg (with regcode-types rl-reg))
(define rl-slot (with regcode-types rl-slot))
(define-type rlate (select regcode-types rlate))
(define-type rleaf (select regcode-types rleaf))
(define-type rloc (select regcode-types rloc))
(define-type rlocs (select regcode-types rlocs))
(define-type rmoves (select regcode-types rmoves))
(define s-apply (with regcode-types s-apply))
(define s-cellular (with regcode-types s-cellular))
(define s-field (with regcode-types s-field))
(define s-identity (with regcode-types s-identity))
(define s-list (with regcode-types s-list))
(define s-none (with regcode-types s-none))
(define s-op1 (with regcode-types s-op1))
(define s-op2 (with regcode-types s-op2))
(define s-op2imm (with regcode-types s-op2imm))
(define s-prim (with regcode-types s-prim))
(define s-pure (with regcode-types s-pure))
(define s-set (with regcode-types s-set))
(define s-special (with regcode-types s-special))
(define-type wcells (select regcode-types wcells))
(define-type cenv (select compile-types cenv))
(define-type exps (select compile-types exps))
(define-type items (select compile-types items))
(define-type patches (select compile-types patches))
(define-type syms (select compile-types syms))
(define-type c-inline (select compile-exps-types c-inline))
(define-type c-mslots (select compile-exps-types c-mslots))
(define-type c-mvals (select compile-exps-types c-mvals))
(define-type c-waits (select compile-exps-types c-waits))
(define-type c-special (select compile-plan-types c-special))
(define-type rplaces (select regcode-exps-types rplaces))
(define-type rscope (select regcode-exps-types rscope))
(define e-app (with parser-types e-app))
(define e-begin (with parser-types e-begin))
(define e-bloblet (with parser-types e-bloblet))
(define e-bool (with parser-types e-bool))
(define e-char (with parser-types e-char))
(define e-convention (with parser-types e-convention))
(define e-extract (with parser-types e-extract))
(define e-float (with parser-types e-float))
(define e-if (with parser-types e-if))
(define e-int (with parser-types e-int))
(define e-lambda (with parser-types e-lambda))
(define e-let (with parser-types e-let))
(define e-letrec (with parser-types e-letrec))
(define e-letregion (with parser-types e-letregion))
(define e-module (with parser-types e-module))
(define e-plambda (with parser-types e-plambda))
(define e-product (with parser-types e-product))
(define e-proj (with parser-types e-proj))
(define e-prompt (with parser-types e-prompt))
(define e-rlambda (with parser-types e-rlambda))
(define e-str (with parser-types e-str))
(define e-sum (with parser-types e-sum))
(define e-sym (with parser-types e-sym))
(define e-tagcase (with parser-types e-tagcase))
(define e-the (with parser-types e-the))
(define e-unit (with parser-types e-unit))
(define e-var (with parser-types e-var))
(define e-with (with parser-types e-with))
(define-type exp (select parser-types exp))
(define-type mod-items (select parser-types mod-items))
(define-type exp-arms (select check-resolve-types exp-arms))
(define-type exp-let-bs (select check-resolve-types exp-let-bs))
(define-type exp-letrec-bs (select check-resolve-types exp-letrec-bs))
(define-type exp-params (select check-subst-types exp-params))
(define-type k-ids (select check-types-types k-ids))
(define-type maybe-exp (select regcode-helpers-types maybe-exp))
(define-type roperands (select regcode-helpers-types roperands))
(define-type rsplits (select regcode-helpers-types rsplits))
(define-type r-scopes (select regcode-modules-types r-scopes))
;; What it uses of the modules it is given.
(define r-add-name? (with regcode r-add-name?))
(define r-adds? (with regcode r-adds?))
(define r-arg-simple-here? (with regcode r-arg-simple-here?))
(define r-bind (with regcode r-bind))
(define r-bind-lifted (with regcode r-bind-lifted))
(define r-const-cell (with regcode r-const-cell))
(define r-const-false? (with regcode r-const-false?))
(define r-count-args (with regcode r-count-args))
(define r-decline (with regcode r-decline))
(define r-done (with regcode r-done))
(define r-emit (with regcode r-emit))
(define r-exp-args (with regcode r-exp-args))
(define r-holds? (with regcode r-holds?))
(define r-known (with regcode r-known))
(define r-last-hard (with regcode r-last-hard))
(define r-leaf-late (with regcode r-leaf-late))
(define r-leaf-move (with regcode r-leaf-move))
(define r-leave (with regcode r-leave))
(define r-lifted (with regcode r-lifted))
(define r-lifted-at (with regcode r-lifted-at))
(define r-local (with regcode r-local))
(define r-moves-cycle? (with regcode r-moves-cycle?))
(define r-moves-snoc (with regcode r-moves-snoc))
(define r-name (with regcode r-name))
(define r-new-label (with regcode r-new-label))
(define r-nth-arg (with regcode r-nth-arg))
(define r-nth-int (with regcode r-nth-int))
(define r-op0 (with regcode r-op0))
(define r-op1 (with regcode r-op1))
(define r-op2 (with regcode r-op2))
(define r-opn (with regcode r-opn))
(define r-opnn (with regcode r-opnn))
(define r-par-moves (with regcode r-par-moves))
(define r-plain-var-loc (with regcode r-plain-var-loc))
(define r-reg (with regcode r-reg))
(define r-reg-of (with regcode r-reg-of))
(define r-rleaf (with regcode r-rleaf))
(define r-self-known? (with regcode r-self-known?))
(define r-simple? (with regcode r-simple?))
(define r-slot (with regcode r-slot))
(define r-standard (with regcode r-standard))
(define r-standard-name (with regcode r-standard-name))
(define r-var-loc (with regcode r-var-loc))
(define r-where (with regcode r-where))
(define r-written? (with regcode r-written?))
(define c-applied-let (with compile c-applied-let))
(define c-apply-shares-at (with compile c-apply-shares-at))
(define c-conversion-at (with compile c-conversion-at))
(define c-count-exps (with compile c-count-exps))
(define c-count-params (with compile c-count-params))
(define c-field-at (with compile c-field-at))
(define c-genv (with compile c-genv))
(define c-lambda-of (with compile c-lambda-of))
(define c-length (with compile c-length))
(define c-reshape-at (with compile c-reshape-at))
(define c-with-at (with compile c-with-at))
(define c-with-places-at (with compile c-with-places-at))
(define c-bind-lifted (with compile-lift c-bind-lifted))
(define c-made-word (with compile-exps c-made-word))
(define c-module-values (with compile-exps c-module-values))
(define c-names-any? (with compile-exps c-names-any?))
(define c-r-plan-ctx (with compile-exps c-r-plan-ctx))
(define c-spec-now (with compile-exps c-spec-now))
(define c-waits-onto (with compile-exps c-waits-onto))
(define c-inlining (with compile-plan c-inlining))
(define c-plan-child (with compile-plan c-plan-child))
(define c-length-locs (with regcode-exps c-length-locs))
(define r-all? (with regcode-exps r-all?))
(define r-append-arg (with regcode-exps r-append-arg))
(define r-assume (with regcode-exps r-assume))
(define r-assuming (with regcode-exps r-assuming))
(define r-bind-all (with regcode-exps r-bind-all))
(define r-bind-places (with regcode-exps r-bind-places))
(define r-const-into (with regcode-exps r-const-into))
(define r-drop-bools (with regcode-exps r-drop-bools))
(define r-field-args (with regcode-exps r-field-args))
(define r-free-args (with regcode-exps r-free-args))
(define r-get (with regcode-exps r-get))
(define r-guard (with regcode-exps r-guard))
(define r-in-regs (with regcode-exps r-in-regs))
(define r-invoke (with regcode-exps r-invoke))
(define r-join-flags (with regcode-exps r-join-flags))
(define r-join-of (with regcode-exps r-join-of))
(define r-join-places (with regcode-exps r-join-places))
(define r-jump-moves (with regcode-exps r-jump-moves))
(define r-keep (with regcode-exps r-keep))
(define r-keep-in-reg (with regcode-exps r-keep-in-reg))
(define r-keep-in-slot (with regcode-exps r-keep-in-slot))
(define r-let-inits (with regcode-exps r-let-inits))
(define r-letrec-env-j (with regcode-exps r-letrec-env-j))
(define r-letrec-patch (with regcode-exps r-letrec-patch))
(define r-letrec-slots-j (with regcode-exps r-letrec-slots-j))
(define r-letrec-te-j (with regcode-exps r-letrec-te-j))
(define r-lexical-into (with regcode-exps r-lexical-into))
(define r-local-all (with regcode-exps r-local-all))
(define r-local-names (with regcode-exps r-local-names))
(define r-local-params (with regcode-exps r-local-params))
(define r-loop-move (with regcode-exps r-loop-move))
(define r-looped (with regcode-exps r-looped))
(define r-members (with regcode-exps r-members))
(define r-own-now (with regcode-exps r-own-now))
(define r-own-self (with regcode-exps r-own-self))
(define r-place-value (with regcode-exps r-place-value))
(define r-reverse-env (with regcode-exps r-reverse-env))
(define r-self-moves (with regcode-exps r-self-moves))
(define r-sibling-env (with regcode-exps r-sibling-env))
(define r-slot-args-of (with regcode-exps r-slot-args-of))
(define r-spec-at (with regcode-exps r-spec-at))
(define r-spec-free (with regcode-exps r-spec-free))
(define r-spec-param? (with regcode-exps r-spec-param?))
(define r-spec-self? (with regcode-exps r-spec-self?))
(define r-spec-start (with regcode-exps r-spec-start))
(define r-special-of (with regcode-exps r-special-of))
(define cellular-closure-free0 (with layout cellular-closure-free0))
(define register-regs (with layout register-regs))
(define rop-cellular (with layout rop-cellular))
(define rop-const (with layout rop-const))
(define rop-field (with layout rop-field))
(define rop-global (with layout rop-global))
(define rop-invoke (with layout rop-invoke))
(define rop-invokeself (with layout rop-invokeself))
(define rop-lambda (with layout rop-lambda))
(define rop-load (with layout rop-load))
(define rop-movereg (with layout rop-movereg))
(define rop-op1 (with layout rop-op1))
(define rop-op2 (with layout rop-op2))
(define rop-prim (with layout rop-prim))
(define rop-prim1 (with layout rop-prim1))
(define rop-prim2 (with layout rop-prim2))
(define rop-prim2imm (with layout rop-prim2imm))
(define rop-reg (with layout rop-reg))
(define rop-return (with layout rop-return))
(define rop-setfield (with layout rop-setfield))
(define rop-setreg (with layout rop-setreg))
(define rop-setstk (with layout rop-setstk))
(define rop-stack (with layout rop-stack))
(define rop-tailinvoke (with layout rop-tailinvoke))
(define routine-cons (with layout routine-cons))
(define routine-eq (with layout routine-eq))
(define routine-field-ref (with layout routine-field-ref))
(define routine-int-add (with layout routine-int-add))
(define routine-int-eq (with layout routine-int-eq))
(define routine-prompt (with layout routine-prompt))
(define routine-withmark-tail (with layout routine-withmark-tail))
(define r-add-imm (with regcode-helpers r-add-imm))
(define r-args-2 (with regcode-helpers r-args-2))
(define r-args-3 (with regcode-helpers r-args-3))
(define r-collects-here? (with regcode-helpers r-collects-here?))
(define r-const-value (with regcode-helpers r-const-value))
(define r-deeper? (with regcode-helpers r-deeper?))
(define r-free-into-regs (with regcode-helpers r-free-into-regs))
(define r-free-operand? (with regcode-helpers r-free-operand?))
(define r-fx-value (with regcode-helpers r-fx-value))
(define r-guards-for (with regcode-helpers r-guards-for))
(define r-identity-arg (with regcode-helpers r-identity-arg))
(define r-imm-operand (with regcode-helpers r-imm-operand))
(define r-index-field (with regcode-helpers r-index-field))
(define r-inline-or-unroll (with regcode-helpers r-inline-or-unroll))
(define r-just-exp (with regcode-helpers r-just-exp))
(define r-knowing (with regcode-helpers r-knowing))
(define r-known-arg (with regcode-helpers r-known-arg))
(define r-known-cell (with regcode-helpers r-known-cell))
(define r-known-slow (with regcode-helpers r-known-slow))
(define r-lifted-call-args (with regcode-helpers r-lifted-call-args))
(define r-lifted-closure (with regcode-helpers r-lifted-closure))
(define r-literal? (with regcode-helpers r-literal?))
(define r-make-array-ops (with regcode-helpers r-make-array-ops))
(define r-negate (with regcode-helpers r-negate))
(define r-op2imm (with regcode-helpers r-op2imm))
(define r-reg-operand (with regcode-helpers r-reg-operand))
(define r-restore (with regcode-helpers r-restore))
(define r-spec-body-collects? (with regcode-helpers r-spec-body-collects?))
(define r-spec-of (with regcode-helpers r-spec-of))
(define r-spec-word (with regcode-helpers r-spec-word))
(define r-split-app (with regcode-helpers r-split-app))
(define r-unit (with regcode-helpers r-unit))
(define r-unknowing (with regcode-helpers r-unknowing))
(define r-var-value (with regcode-helpers r-var-value))
(define r-args-reversed (with regcode-modules r-args-reversed))
(define r-give-waiting (with regcode-modules r-give-waiting))
(define r-module-own (with regcode-modules r-module-own))
(define r-module-slots (with regcode-modules r-module-slots))
(define r-reshape-fields (with regcode-modules r-reshape-fields))
(define r-slots-oldest (with regcode-modules r-slots-oldest))
(define r-with-fields (with regcode-modules r-with-fields))

(define-rec
  ;; `x`'s value into RESULT; in tail position, returned. A procedure
  ;; converted to a convention is made, then given to `%fx26-convert` with
  ;; what it is converted to.
  (r-exp (subr rcompiles (rgen exp renv cenv bool) unit)
    (lambda (g x env te tail)
      (let ((k (c-conversion-at x)) (r (c-reshape-at x)))
        (cond ((>= k 0)
               (begin
                 (r-prim g "%fx26-convert" (r-args-2 (a-as-is x) (a-v (wcell-int k))) env te)
                 (r-done g tail)))
              ((not (null? r)) (r-reshape g x (car r) env te tail))
              (else (r-exp-as-is g x env te tail))))))
  ;; `x`'s value into RESULT; in tail position, returned.
  (r-exp-as-is (subr rcompiles (rgen exp renv cenv bool) unit)
    (lambda (g x env te tail)
      (let ((k (r-known env x)))
        (if (not (null? k))
            (r-const-value g (r-const-cell (car k)) tail)
      (tagcase x
        (e-var (n a b) (begin (r-var-value g (r-where env n) n tail) (r-done g tail)))
        (e-int (n a b) (r-const-value g (wcell-int n) tail))
        (e-bool (v a b) (r-const-value g (wcell-bool v) tail))
        (e-char (v a b) (r-const-value g (wcell-char v) tail))
        (e-str (s a b) (r-const-value g (wcell-string s) tail))
        (e-float (x a b) (r-const-value g (wcell-f64 x) tail))
        (e-sym (s a b) (r-const-value g (wcell-symbol s) tail))
        (e-unit (a b) (r-const-value g (wcell-unit) tail))
        (e-plambda (d body a b) (r-exp g body env te tail))
        (e-proj (body ds a b) (r-exp g body env te tail))
        (e-the (d body a b) (r-exp g body env te tail))
        (e-convention (cnv body a b) (r-exp g body env te tail))
        (e-letregion (k r i body a b)
          (if (or (= k 0) (= k 3)) (r-exp g body env te tail) (r-letregion g k r body env te tail)))
        (e-if (t th el a b)
          (if (not (null? (r-known env t)))
              ;; A test known: the arm it takes, alone.
              (r-exp g (if (r-const-false? (car (r-known env t))) el th) env te tail)
          (let ((no (r-new-label g)) (end (r-new-label g)))
            (begin
              (r-branch-on g t #f no env te)
              (r-exp g th (r-knowing env t #t) te tail)
              (if tail #u (r-emit g (r-branch #f end)))
              (r-emit g (r-label no))
              (r-exp g el (r-knowing env t #f) te tail)
              (r-emit g (r-label end))))))
        (e-begin (es a b)
          (if (null? es) (r-const-value g (wcell-unit) tail) (r-begin g es env te tail)))
        (e-let (bs body a b) (r-let g bs body env te tail))
        (e-extract (p l a b)
          (let ((i (c-field-at a b)))
            (if (< i 0)
                (r-decline)
                (begin (r-exp g p env te #f) (r-opn g rop-field (+ i 2)) (r-done g tail)))))
        (e-lambda (ps body a b)
          (begin (r-lambda g ps body env te (the syms nil) (the maybe-exp nil) tail)
                 (r-done g tail)))
        (e-rlambda (r l a b)
          (tagcase l
            (e-lambda (ps body la lb)
              (begin (r-lambda g ps body env te (the syms nil) (r-just-exp r) #f) (r-done g tail)))
            (else y (r-decline))))
        (e-sum (t v a b)
          (begin
            (r-make-frozen g 36 (r-args-2 (a-v (wcell-symbol t)) (a-e v)) env te)
            (r-done g tail)))
        (e-product (fs a b)
          (begin
            (r-make-frozen g 37 (r-field-args fs) env te)
            (r-done g tail)))
        (e-bloblet (op i args a b)
          (begin (r-bloblet g (symbol->string op) i args env te) (r-done g tail)))
        (e-prompt (t body h a b)
          (let ((ops (r-args-3 (a-e t) (a-e h) (a-thunk body))))
            (begin
              (r-call-out g rop-cellular routine-prompt ops env te)
              (r-done g tail))))
        (e-tagcase (s arms els a b) (r-tagcase g s arms els env te tail))
        (e-letrec (bs body a b)
          (let ((ks (r-lifted a b)))
            (cond ((not (null? ks))
                   ;; Lifted as its stack code lifted it (`c-lift`).
                   (let ((inner (r-bind-lifted bs (car ks) env)))
                     (r-exp g body inner (c-bind-lifted bs (car ks) te) tail)))
                  ;; A leaf makes no closure; join points it may have.
                  ((and (extract g leaf) (not (r-all? (r-join-flags bs body tail)))) (r-decline))
                  (else (r-letrec g bs body env te tail)))))
        ;; A lambda applied at once: a `let` (`c-applied-let`).
        (e-app (f args a b)
          (let ((l (c-applied-let f args)))
            (if (null? l)
                (r-app g f args a b env te tail)
                (r-let g (extract (car l) 1) (extract (car l) 2) env te tail))))
        ;; `regcode-modules.fx`'s.
        (e-module (items a b) (r-module-or-with g x env te tail))
        (e-with (m body a b) (r-module-or-with g x env te tail)))))))
  ;; The region's name bound, as a `let`'s, to a region entered (never in a
  ;; leaf), and left with the body's value, which is so not in tail
  ;; position.
  (r-letregion (subr rcompiles (rgen int symbol exp renv cenv bool) unit)
    (lambda (g k r body env te tail)
      (if (extract g leaf)
          (r-decline)
          (let ((regs (get (extract g nreg))) (slots (get (extract g nslot))))
            (begin
              (r-prim g (if (= k 1) "%region-enter" "%reap-enter") (the rargs nil) env te)
              (let ((h (r-keep-in-slot g)))
                (begin
                  (r-exp g body (r-bind r (rl-slot h) env) (r-local te r) #f)
                  (let ((v (r-keep-in-slot g)))
                    (begin
                      (r-prim g "%region-exit" (r-args-2 (a-slot h) (a-slot v)) env te)
                      (r-done g tail)))))
              (r-restore g regs slots))))))
  ;; A frozen value made, of layout `tag`: `args` its fields.
  (r-make-frozen (subr rcompiles (rgen int rargs renv cenv) unit)
    (lambda (g tag args env te)
      (r-prim g "%make-frozen" (the rargs (cons (a-v (wcell-int tag)) args)) env te)))
  ;; Code that goes to `label` if `x` is `when` (true: anything but #f), and
  ;; on if not: a test as jumps. `and` and `or` (`if`s, as the parser makes
  ;; them), `not` and constants make no boolean, and are tested no more than
  ;; once.
  (r-branch-on (subr rcompiles (rgen exp bool int renv cenv) unit)
  (lambda (g x when label env te)
    (tagcase x
      (e-the (d body a b) (r-branch-on g body when label env te))
      (e-app (f args a b)
        (if (and (string=? (r-standard-name env f) "not") (= (c-count-exps args) 1))
            (r-branch-on g (car args) (not when) label env te)
            (r-branch-plain g x when label env te)))
      (e-if (t th el a b)
        (let ((tc (r-known env th)) (ec (r-known env el)))
          (cond
            ;; `(if a K e)`: where `a` holds, `K` decides.
            ((and (not (null? tc)) (r-holds? tc when))
             (begin (r-branch-on g t #t label env te) (r-branch-on g el when label env te)))
            ((not (null? tc)) (r-branch-past g t #t el when label env te))
            ;; `(if a t K)`: `and`'s shape.
            ((and (not (null? ec)) (r-holds? ec when))
             (begin (r-branch-on g t #f label env te) (r-branch-on g th when label env te)))
            ((not (null? ec)) (r-branch-past g t #f th when label env te))
            (else
             (let ((no (r-new-label g)) (end (r-new-label g)))
               (begin (r-branch-on g t #f no env te) (r-branch-on g th when label env te)
                      (r-emit g (r-branch #f end)) (r-emit g (r-label no))
                      (r-branch-on g el when label env te) (r-emit g (r-label end))))))))
      (else y (r-branch-plain g x when label env te)))))
  ;; Where test `t` is `sense`, on past the test of `x`, which goes to
  ;; `label` if `x` is `when`; else that test.
  (r-branch-past (subr rcompiles (rgen exp bool exp bool int renv cenv) unit)
    (lambda (g t sense x when label env te)
      (let ((skip (r-new-label g)))
        (begin (r-branch-on g t sense skip env te)
               (r-branch-on g x when label env te)
               (r-emit g (r-label skip))))))
  ;; The same for a test that is not `not` or an `if`: a constant decided
  ;; now, anything else made and branched on.
  (r-branch-plain (subr rcompiles (rgen exp bool int renv cenv) unit)
  (lambda (g x when label env te)
    (let ((k (r-known env x)))
      (if (not (null? k))
          (if (r-holds? k when) (r-emit g (r-branch #f label)) #u)
          (let ((jump (if when (r-brancht label) (r-branch #t label))))
            (begin (r-exp g x env te #f) (r-emit g jump)))))))
  (r-begin (subr rcompiles (rgen exps renv cenv bool) unit)
    (lambda (g es env te tail)
      (if (null? (cdr es))
          (r-exp g (car es) env te tail)
          (begin (r-exp g (car es) env te #f) (r-begin g (cdr es) env te tail)))))
  ;; Where `x`'s value is: a constant, as itself; anything else made, in
  ;; the scope outside, and kept, in a register if `reg`, else a frame slot.
  (r-value-loc (subr rcompiles (rgen exp renv cenv bool) rloc)
    (lambda (g x env te reg)
      (let ((k (r-known env x)))
        (if (null? k) (begin (r-exp g x env te #f) (r-keep g reg)) (rl-const (car k))))))
  ;; Each binding's value made, in the scope outside, and put where it
  ;; lives: a register in a leaf, else a frame slot. In order.
  (r-let-bind (subr rcompiles (rgen exp-let-bs renv cenv bools) renv)
    (lambda (g bs env te flags)
      (if (null? bs)
          nil
          (let ((l (r-value-loc g (extract (car bs) 2) env te (car flags))))
            (cons (cons (extract (car bs) 1) l) (r-let-bind g (cdr bs) env te (cdr flags)))))))
  (r-bloblet (subr rcompiles (rgen string int exps renv cenv) unit)
    (lambda (g op i args env te)
      (let ((all (r-exp-args args)))
        (case op (("bloblet-ref")
                  (begin (r-exp g (car args) env te #f) (r-opn g rop-field (+ i 2))))
                 (("make-bloblet") (r-prim g "%make-bloblet" all env te))
                 (("rmake-bloblet") (r-prim g "%region-make-bloblet" all env te))
                 (("bloblet-set!")
                  (let* ((field (a-v (wcell-int (+ i 2))))
                         (ops (r-args-3 (a-e (car args)) field (a-e (car (cdr args))))))
                    (begin (r-prim g "%bloblet-set!" ops env te) (r-unit g))))
                 (("bloblet-byte") (r-prim g "%bloblet-byte" all env te))
                 (("bloblet-set-byte!")
                  (begin (r-prim g "%bloblet-set-byte!" all env te) (r-unit g)))
                 (("bloblet-bytes") (r-prim g "%bloblet-bytes" all env te))
                 (else (r-decline))))))
  ;;; ---------------------------------------------------------- applications
  (r-app (subr rcompiles (rgen exp exps int int renv cenv bool) unit)
    (lambda (g f args a b env te tail)
      (let ((n (c-count-exps args)))
        (cond ((not (null? (r-join-of env f))) (r-jump g (car (r-join-of env f)) args env te tail))
              ((and tail (r-self-known? g f n te)) (r-loop g args env te))
              ;; In a procedure specialized at a lambda: the lambda called,
              ;; or the procedure calling itself.
              ((and (r-spec-param? env f) (= n (extract (car (get c-spec-now)) 7)))
               (r-spec-lambda g args env te tail))
              ((r-spec-self? env f args)
               (let* ((sp (car (get c-spec-now))) (cell (extract sp 2)))
                 (r-self-guarded g cell (get r-spec-start) f args env te tail)))
              ;; A top-level procedure calling itself through its global, its
              ;; own name not an inlined body's, which may name an older global.
              ((not (null? (r-own-self env f args)))
               (let ((o (car (get r-own-now))) (cell (car (r-own-self env f args))))
                 (r-self-guarded g cell (extract o 4) f args env te tail)))
              (else
               (let ((name (r-standard-name env f)))
                 (if (string=? name "")
                     (r-call g f args a b env te tail)
                     (cond ((and tail (and (string=? name "with-mark") (= n 3)))
                            (r-withmark-tail g args env te))
                           ((and (string=? name "apply") (= n 2))
                            (r-apply g args env te tail (not (c-apply-shares-at a b))))
                           ((not (null? (r-identity-arg env name args)))
                            (r-exp g (car (r-identity-arg env name args)) env te tail))
                           (else (begin (r-standard-app g name args env te tail)
                                        (r-done g tail)))))))))))
  (r-standard-app (subr rcompiles (rgen string exps renv cenv bool) unit)
    (lambda (g name args env te tail)
      (tagcase (r-standard name (c-count-exps args))
        (s-op2 (r swap negate)
          ;; Operands trade places only where one is a variable or a
          ;; constant, which neither has an effect nor sees one (only a
          ;; definition writes a global); else they run as written. A
          ;; constant goes second, an immediate, where the operation does
          ;; not care which.
          (let* ((x (car args)) (y (car (cdr args)))
                 ;; A chain of `+`, and `-` of constants, with one operand not
                 ;; a constant, deeper than here: that one, and then the
                 ;; constants' sum at once. Integers are exact, so the order
                 ;; they are added in cannot matter.
                 (split (if (and (r-add-name? name) (or (r-adds? env x) (r-adds? env y)))
                            (r-split-app env name args)
                            (the rsplits nil)))
                 (core (if (null? split) (the maybe-exp nil) (extract (car split) 1)))
                 ;; (Asked only where it can matter, and a literal first:
                 ;; what is known is looked up, and that costs.)
                 (literal (r-literal? x))
                 (commutes (or (= r routine-int-add) (or (= r routine-eq) (= r routine-int-eq))))
                 (free-x (and swap (r-free-operand? env x)))
                 (free-y (and swap (and (not free-x) (r-free-operand? env y)))))
            (begin
              (cond ((r-deeper? core x y)
                     (begin (r-exp g (car core) env te #f) (r-add-imm g (extract (car split) 2))))
                    ((and swap (and (not free-x) (not free-y))) (r-binary-swapped g r x y env te))
                    ((or swap (and commutes (and literal (null? (r-known env y)))))
                     (r-binary g r y x env te))
                    (else (r-binary g r x y env te)))
              (if negate (r-negate g) #u))))
        (s-op1 (r) (begin (r-exp g (car args) env te #f) (r-opn g rop-op1 r)))
        (s-op2imm (r v) (begin (r-exp g (car args) env te #f) (r-op2imm g r v)))
        (s-field (k) (begin (r-exp g (car args) env te #f) (r-opn g rop-field k)))
        (s-prim (p) (r-call-out g rop-prim p (r-exp-args args) env te))
        (s-pure (p)
          (if (null? (cdr args))
              (begin (r-exp g (car args) env te #f) (r-opn g rop-prim1 p))
              (r-pure2 g p (car args) (car (cdr args)) env te)))
        ;; (A mark in tail position is `r-withmark-tail`'s.)
        (s-cellular (r) (r-call-out g rop-cellular r (r-exp-args args) env te))
        (s-identity () (r-exp g (car args) env te #f))
        (s-set ()
          (let ((k (extract (r-operands g (car args) (car (cdr args)) env te #f) 2)))
            (if (null? k)
                (r-decline)
                (begin (r-opnn g rop-setfield 2 (car k)) (r-unit g)))))
        (s-special (what) (r-special g what args env te))
        ;; (`r-apply`'s, which `r-app` calls.)
        (s-apply () (r-decline))
        (s-list () (r-list g args env te))
        (s-none () (r-decline)))))
  ;; In tail position a mark replaces this frame's, as stack code's
  ;; `withmark-tail` does: the arguments made, the frame left, and the
  ;; call-out, which calls the thunk as a tail call.
  (r-withmark-tail (subr rcompiles (rgen exps renv cenv) unit)
    (lambda (g args env te)
      (begin
        (r-exp-args-into g args env te)
        (r-leave g)
        (r-opnn g rop-cellular routine-withmark-tail 3)
      ;; Never reached (the call-out goes on in the thunk): register code
      ;; ends each path so.
      (r-op0 g rop-return))))
  ;; `(apply f xs)`: `f` a `vsubr`, a closure of `%vlambda`'s over the
  ;; procedure of one list, free value 0; that procedure, called with `xs`.
  ;; `f` and `xs` in order; `f`'s procedure kept in a slot while `xs` moves
  ;; to REG1.
  (r-apply (subr rcompiles (rgen exps renv cenv bool bool) unit)
    (lambda (g args env te tail copy)
      (if (extract g leaf)
          (r-decline)
          (let ((regs (get (extract g nreg))) (slots (get (extract g nslot))))
            (begin
              (r-exp-args-into g args env te)
              (let ((s (r-slot g)))
                (begin (r-opn g rop-reg 1) (r-opn g rop-field cellular-closure-free0)
                       (r-opn g rop-setstk s) (r-opn g rop-reg 2) (r-opn g rop-setreg 1)
                       ;; Copied, unless the checker found it at `acyclic`.
                       (if copy
                           (begin (r-opnn g rop-prim (runtime-primitive "%fx26-list-copy") 1)
                                  (r-opn g rop-setreg 1))
                           #u)
                       (r-opn g rop-stack s) (r-invoke g 1 tail)))
              (r-restore g regs slots))))))
  ;; A call: the arguments into REG1…REGn, the procedure in RESULT.
  (r-call (subr rcompiles (rgen exp exps int int renv cenv bool) unit)
    (lambda (g f args a b env te tail)
      (let ((n (c-count-exps args)))
        (cond ;; An inlined call: in a fast version, no call, so in a leaf too.
              ((not (null? (r-inline-or-unroll a b env f args n)))
               (if (and (not (get r-assuming)) (extract g leaf))
                   (r-decline)
                   (let ((i (car (r-inline-or-unroll a b env f args n))))
                     (r-inline g (car i) (cdr i) f args env te tail))))
              ((extract g leaf)
               (if (and tail
                        (and (< n register-regs)
                             (and (null? (r-special-of a b env f args)) (< (r-lifted-at env f) 0))))
                   (r-leaf-tail-call g f args env te)
                   (r-decline)))
              ((not (null? (r-special-of a b env f args)))
               (let ((i (car (r-special-of a b env f args))))
                 (r-specialize g (extract i 1) (extract i 2) (extract i 3) args env te tail)))
              ;; A lifted procedure's call: the names it would have captured,
              ;; then the arguments, into REG1…REGn; its closure, a constant.
              ((>= (r-lifted-at env f) 0)
               (let ((all (r-lifted-call-args env f args)))
                 (begin
                   (r-args g all env te (the maybe-exp nil))
                   (r-op1 g rop-const (r-lifted-closure (r-lifted-at env f)))
                   (r-invoke g (r-count-args all) tail))))
              ;; A call of the procedure itself, not in tail position: by its
              ;; own entry, with no closure fetched.
              ((and (not tail) (r-self-known? g f n te))
               (begin (r-exp-args-into g args env te) (r-opn g rop-invokeself n)))
              (else
               (begin
                 (r-args g (r-exp-args args) env te (r-just-exp f))
                 (r-invoke g n tail)))))))
  ;; The expressions `args` as a call's arguments, into REG1…REGn
  ;; (`r-args`), with no procedure.
  (r-exp-args-into (subr rcompiles (rgen exps renv cenv) unit)
    (lambda (g args env te) (r-args g (r-exp-args args) env te (the maybe-exp nil))))
  ;; A call of a small global procedure, inlined: the arguments made and
  ;; kept (one that is a variable in the frame or the closure is used where
  ;; it is); then, if the global still holds a closure of the word the body
  ;; was compiled to, the body, in a scope of its own where the parameters
  ;; are the arguments and the globals those it saw; else the call. A
  ;; redefinition makes a new closure, of a new word: the call.
  (r-inline (subr rcompiles (rgen c-inline wglobal exp exps renv cenv bool) unit)
    (lambda (g i cell f args env te tail)
      (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
             (bound (r-inline-args g (extract i 3) args env te))
             (call (r-new-label g)) (end (r-new-label g))
             (outer-genv (get c-genv)) (outer-inlining (get c-inlining))
             (n (c-count-exps args))
             (outer-ctx (get c-r-plan-ctx))
             ;; The procedure running is not known in the body.
             (h (r-unknowing g)))
        (let ((assumed (not (r-guards-for g cell f call))))
          (begin
            (set c-genv (extract i 5))
            (set c-inlining (cons (extract i 1) outer-inlining))
            ;; Its plan's, along the path here (3b).
            (set c-r-plan-ctx
                 (cons (c-plan-child (if (null? outer-ctx) 0 (car outer-ctx)) (extract i 1) n)
                       outer-ctx))
            (r-exp h (extract i 4) (extract bound 1) (extract bound 2) tail)
            (set c-r-plan-ctx outer-ctx)
            (set c-inlining outer-inlining)
            (set c-genv outer-genv)
            (if assumed
                #u
                (begin
                  (if tail #u (r-emit g (r-branch #f end)))
                  (r-emit g (r-label call))
                  (r-args g (extract bound 3) env te (r-just-exp f))
                  (r-invoke g n tail)
                  (r-emit g (r-label end))))
            (r-restore g regs slots))))))
  ;; Each parameter bound to its argument, in order: where the body finds
  ;; them, as the body's cellular scope has them, and as the call's
  ;; arguments.
  (r-inline-args
    (subr rcompiles (rgen exp-params exps renv cenv) (productof (1 renv) (2 cenv) (3 rargs)))
    (lambda (g ps args env te)
      (if (or (null? ps) (null? args))
          (product (1 (the renv nil)) (2 (the cenv nil)) (3 (the rargs nil)))
          (let* ((p (extract (car ps) 1)) (a (car args))
                 (k (r-known-arg env a))
                 (l (if (null? k) (r-var-loc env a) (the rlocs (cons (rl-const (car k)) nil))))
                 (kept (if (null? l)
                           (the rlocs nil)
                           (tagcase (car l)
                             (rl-slot (s) l)
                             (rl-free (j) l)
                             (rl-const (c) l)
                             ;; In a fast version, where no call comes after
                             ;; to clobber it.
                             (rl-reg (r) (if (get r-assuming) l (the rlocs nil)))
                             (else y (the rlocs nil)))))
                 (here (if (null? kept)
                           (begin (r-exp g a env te #f) (r-keep g (extract g leaf)))
                           (car kept)))
                 (arg (cond ((not (null? k)) (r-known-slow a (car k)))
                            ((null? kept) (tagcase here (rl-slot (s) (a-slot s)) (else y (a-e a))))
                            (else (a-e a))))
                 (rest (r-inline-args g (cdr ps) (cdr args) env te)))
            (product (1 (r-bind p here (extract rest 1)))
                     (2 (r-local (extract rest 2) p))
                     (3 (the rargs (cons arg (extract rest 3)))))))))
  ;; A call of a global procedure with a lambda at a parameter it only
  ;; calls: a copy of the procedure made for the lambda (`c-spec`), whose
  ;; closure is made first; then the arguments, the lambda's closure among
  ;; them; then, if the global still holds a closure of the word the copy
  ;; was made from, the copy called, else the global.
  (r-specialize (subr rcompiles (rgen c-special wglobal exp exps renv cenv bool) unit)
    (lambda (g sp cell lam args env te tail)
      (tagcase lam
        (e-lambda (lps lbody la lb)
          ;; Made with the form's words, as the plan says (`c-make-copy`).
          (let ((found (r-spec-word sp (r-spec-of sp cell lps lbody te) lbody)))
            (if (null? found)
                (r-decline)
                (r-specialized-call g sp cell (extract (car found) 4) args env te tail))))
        (else y (r-decline)))))
  ;; The same, with the copy's word `copy`.
  (r-specialized-call (subr rcompiles (rgen c-special wglobal tword exps renv cenv bool) unit)
    (lambda (g sp cell copy args env te tail)
      (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
             (s (r-slot g))
             (n (c-count-exps args)))
        (begin
          (r-op2 g rop-lambda (wcell-word copy) (wcell-int 0))
          (r-opn g rop-setstk s)
          (r-exp-args-into g args env te)
          (let* ((call (r-new-label g)) (end (r-new-label g)))
            (if (r-assume cell)
                (begin (r-opn g rop-stack s) (r-invoke g n tail))
                (begin
                  (r-guard g cell call)
                  (r-opn g rop-stack s)
                  (r-invoke g n tail)
                  (if tail #u (r-emit g (r-branch #f end)))
                  (r-emit g (r-label call))
                  (r-op1 g rop-global (wcell-global cell))
                  (r-invoke g n tail)
                  (r-emit g (r-label end)))))
          (r-restore g regs slots)))))
  ;; In a procedure specialized at a lambda, a call of the parameter the
  ;; lambda is: the lambda's body, its parameters bound to the arguments and
  ;; the values its closure captured to those fields of the parameter's
  ;; value, where the globals are those it saw.
  (r-spec-lambda (subr rcompiles (rgen exps renv cenv bool) unit)
    (lambda (g args env te tail)
      (let* ((sp (car (get c-spec-now))) (at (car (get r-spec-at))) (captured (extract sp 10))
             (regs (get (extract g nreg))) (slots (get (extract g nslot)))
             ;; The body as it is compiled: in the globals the lambda saw.
             (body-collects (r-spec-body-collects? g sp tail))
             (flags (r-in-regs g args (c-length captured) te body-collects))
             (bound (r-spec-args g (extract sp 8) args env te flags))
             (free-flags (r-drop-bools flags (c-count-exps args)))
             (all (r-spec-free g at captured 0 (extract bound 1) (extract bound 2) free-flags))
             (outer (get c-genv)) (outer-ctx (get c-r-plan-ctx)))
        (begin
          (set c-genv (extract sp 11))
          ;; Its plan's: the context after its copy's (3b).
          (set c-r-plan-ctx
               (cons (if (or (null? outer-ctx) (< (car outer-ctx) 0)) -1 (+ (car outer-ctx) 1))
                     outer-ctx))
          (r-exp g (extract sp 9) (extract all 1) (extract all 2) tail)
          (set c-r-plan-ctx outer-ctx)
          (set c-genv outer)
          (r-restore g regs slots)))))
  ;; Each of the lambda's parameters bound to its argument, made and kept,
  ;; in order.
  (r-spec-args (subr rcompiles (rgen exp-params exps renv cenv bools) rscope)
    (lambda (g ps args env te flags)
      (if (or (null? ps) (null? args))
          (product (1 (the renv nil)) (2 (the cenv nil)))
          (let* ((p (extract (car ps) 1))
                 (l (r-value-loc g (car args) env te (car flags)))
                 (rest (r-spec-args g (cdr ps) (cdr args) env te (cdr flags))))
            (product (1 (r-bind p l (extract rest 1))) (2 (r-local (extract rest 2) p)))))))
  ;; A procedure calling itself through its global `cell` (a top-level
  ;; definition's, or, in a copy specialized at a lambda, with the parameter
  ;; passed as itself): the arguments made; then, if the global has not
  ;; been written since (it holds its own closure, or the one the copy was
  ;; made from), this procedure again, by its own entry, or in tail
  ;; position a loop back to `start`; else the global.
  (r-self-guarded (subr rcompiles (rgen wglobal int exp exps renv cenv bool) unit)
    (lambda (g cell start f args env te tail)
      (let ((n (c-count-exps args)))
        ;; In a fast version, a call in tail position is a loop, in a leaf too.
        (if (and (extract g leaf) (or (not (and tail (get r-assuming))) (> n register-regs)))
            (r-decline)
            (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
                   (call (r-new-label g)) (end (r-new-label g)))
              (begin
                (if tail
                    (let* ((made (r-self-temps g args env te)) (assumed (r-assume cell)))
                      (begin
                        (if assumed #u (r-guard g cell call))
                        (r-self-moves g made 0)
                        (r-emit g (r-branch #f start))
                        (if assumed
                            (set r-looped #t)
                            (begin
                              (r-emit g (r-label call))
                              (r-args g (r-slot-args-of made) env te (r-just-exp f))
                              (r-invoke g n #t)))))
                    (begin
                      (r-exp-args-into g args env te)
                      (if (r-assume cell)
                          (r-opn g rop-invokeself n)
                          (begin
                            (r-guard g cell call)
                            (r-opn g rop-invokeself n)
                            (r-emit g (r-branch #f end))
                            (r-emit g (r-label call))
                            (r-op1 g rop-global (wcell-global cell))
                            (r-opn g rop-invoke n)
                            (r-emit g (r-label end))))))
                (r-restore g regs slots)))))))
  ;; Each argument kept, in a register in a leaf, else a frame slot, in
  ;; order: where each is.
  (r-self-temps (subr rcompiles (rgen exps renv cenv) rlocs)
    (lambda (g args env te)
      (if (null? args)
          nil
          (let* ((l (begin (r-exp g (car args) env te #f) (r-keep g (extract g leaf))))
                 (rest (r-self-temps g (cdr args) env te)))
            (cons l rest)))))
  ;; RESULT := r(a, b), `a` evaluated first; a constant `b` an immediate.
  (r-binary (subr rcompiles (rgen int exp exp renv cenv) unit)
    (lambda (g r a b env te)
      (let ((o (r-operands g a b env te #t)))
        (cond ((not (null? (extract o 1))) (r-op2imm g r (car (extract o 1))))
              ((not (null? (extract o 2))) (r-opnn g rop-op2 r (car (extract o 2))))
              (else (r-decline))))))
  ;; RESULT := primitive p (one that never collects) of `a` and `b`, as
  ;; `r-binary`, by `prim2` or `prim2imm`.
  (r-pure2 (subr rcompiles (rgen int exp exp renv cenv) unit)
    (lambda (g p a b env te)
      (let ((o (r-operands g a b env te #t)))
        (cond ((not (null? (extract o 1))) (r-op2 g rop-prim2imm (wcell-int p) (car (extract o 1))))
              ((not (null? (extract o 2))) (r-opnn g rop-prim2 p (car (extract o 2))))
              (else (r-decline))))))
  ;; RESULT := r(y, x), `x` evaluated first, as written: for an operation
  ;; whose operands trade places, where they may not run in the other
  ;; order. `x` is kept in a register, or the frame if `y` calls.
  (r-binary-swapped (subr rcompiles (rgen int exp exp renv cenv) unit)
    (lambda (g r x y env te)
      (let ((regs (get (extract g nreg))) (slots (get (extract g nslot))))
        (begin
          (r-exp g x env te #f)
          (let* ((collects (r-collects-here? g y te #f))
                 (k (r-reg g)))
            (begin
              (if collects
                  (let ((s (r-slot g)))
                    (begin (r-opn g rop-setstk s) (r-exp g y env te #f) (r-opnn g rop-load k s)))
                  (begin (r-opn g rop-setreg k) (r-exp g y env te #f)))
              (r-opnn g rop-op2 r k)))
          (r-restore g regs slots)))))
  ;; `a` into RESULT and `b` into a register, `a` evaluated first; or, if
  ;; `imm` and `b` is a constant, `b` as an immediate. The register is free
  ;; again after: use it at once.
  (r-operands (subr rcompiles (rgen exp exp renv cenv bool) roperands)
    (lambda (g a b env te imm)
      (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
             (v (if imm (r-known-cell env b) (the wcells nil)))
             (bl (r-var-loc env b))
             (breg (if (null? bl) -1 (tagcase (car bl) (rl-reg (k) k) (else z -1))))
             (out
              (cond
                ((not (null? v)) (begin (r-exp g a env te #f) (r-imm-operand v)))
                ((>= breg 0) (begin (r-exp g a env te #f) (r-reg-operand breg)))
                ;; `b` first (`a` has no effect, and sees none), made before
                ;; its register is taken: a chain of operations nested in
                ;; their second operands then needs one register, not one a
                ;; level.
                ((r-simple? a)
                 (let ((k (if (r-simple? b)
                              (let ((k (r-reg g))) (begin (r-into g b k env te) k))
                              (begin (r-exp g b env te #f) (r-keep-in-reg g)))))
                   (begin (r-exp g a env te #f) (r-reg-operand k))))
                (else
                 (begin
                   (r-exp g a env te #f)
                   (let* ((kept (r-keep g (not (r-collects-here? g b te #f))))
                          (k (r-reg g)))
                     (begin
                       (r-into g b k env te)
                       (r-get g kept)
                       (r-reg-operand k))))))))
        (begin (r-restore g regs slots) out))))
  ;; `x`'s value into REGk: straight from a register or the frame when it is
  ;; a variable there, else by way of RESULT.
  (r-into (subr rcompiles (rgen exp int renv cenv) unit)
    (lambda (g x k env te)
      (let ((l (r-plain-var-loc env x)))
        (if (null? l)
            (begin (r-exp g x env te #f) (r-opn g rop-setreg k))
            (tagcase (car l)
              (rl-slot (s) (r-opnn g rop-load k s))
              (rl-reg (r) (if (= r k) #u (r-opnn g rop-movereg r k)))
              (else y (begin (r-exp g x env te #f) (r-opn g rop-setreg k))))))))
  ;; The arguments into REG1…REGn, in order, and then `f`, if a call's (one
  ;; or none), into RESULT. Not in a leaf: an argument that is not simple is
  ;; kept in the frame until all are made; a simple one is made last. Past
  ;; `register-regs` (Larceny's convention), REG1…REG7 hold the first seven
  ;; and REG8 a list of the rest, made after every argument, by `cons`,
  ;; which may collect: so then an argument in a register is kept first,
  ;; like one that is not simple.
  (r-args (subr rcompiles (rgen rargs renv cenv maybe-exp) unit)
    (lambda (g args env te f)
      (if (extract g leaf)
          (r-decline)
          (let* ((n (r-count-args args))
                 (many (> n register-regs))
                 (slots (get (extract g nslot)))
                 (hard-f (and (not (null? f)) (not (r-simple? (car f)))))
                 ;; The last argument that is not simple goes straight to its
                 ;; register, when the procedure is simple too.
                 (direct (if (or many hard-f) -1 (r-last-hard args 0 -1)))
                 (kept (r-args-hard g args 0 direct env te many))
                 (fun (if hard-f (begin (r-exp g (car f) env te #f) (r-keep-in-slot g)) -1)))
            (begin
              (if many
                  (begin
                    (r-op1 g rop-const (wcell-nil))
                    (r-args-list g args kept (- n 1) (- register-regs 1) env te)
                    (let ((s (r-slot g)))
                      (begin
                        (r-opn g rop-setstk s)
                        (r-args-into g args kept 0 (- register-regs 1) env te)
                        (r-opnn g rop-load register-regs s))))
                  (r-args-into g args kept 0 n env te))
              (cond ((>= fun 0) (r-opn g rop-stack fun))
                    ((not (null? f)) (r-exp g (car f) env te #f))
                    (else #u))
              (set (extract g nslot) slots))))))
  ;; For each argument: -1 if simple, made later; -2 if made into its
  ;; register now; else the frame slot it is kept in.
  (r-args-hard (subr rcompiles (rgen rargs int int renv cenv bool) (listof int @k))
    (lambda (g args i direct env te many)
      (if (null? args)
          nil
          (if (r-arg-simple-here? (car args) env many)
              (cons -1 (r-args-hard g (cdr args) (+ i 1) direct env te many))
              (begin
                (tagcase (car args)
                  (a-e (x) (r-exp g x env te #f))
                  (a-as-is (x) (r-exp-as-is g x env te #f))
                  (a-thunk (body) (r-thunk g body env te))
                  (a-name (n) (r-name g n env))
                  (else y #u))
                (let ((k (if (= i direct)
                             (begin (r-opn g rop-setreg (+ i 1)) -2)
                             (r-keep-in-slot g))))
                  (cons k (r-args-hard g (cdr args) (+ i 1) direct env te many))))))))
  ;; A procedure of no arguments whose body is `body`: its closure into
  ;; RESULT.
  (r-thunk (subr rcompiles (rgen exp renv cenv) unit)
    (lambda (g body env te)
      (begin (r-lambda g (the exp-params nil) body env te (the syms nil) (the maybe-exp nil) #f)
             #u)))
  ;; The arguments from the `i`th, short of the `stop`th, each into its
  ;; register.
  (r-args-into (subr rcompiles (rgen rargs (listof int @k) int int renv cenv) unit)
    (lambda (g args kept i stop env te)
      (if (or (null? args) (= i stop))
          #u
          (begin
            (r-arg-into g (car args) (car kept) (+ i 1) env te)
            (r-args-into g (cdr args) (cdr kept) (+ i 1) stop env te)))))
  ;; Argument `a` into REGk: from the frame slot it was kept in, if it was
  ;; (-2: in its register already), else made there.
  (r-arg-into (subr rcompiles (rgen rarg int int renv cenv) unit)
    (lambda (g a kept k env te)
      (cond ((= kept -2) #u)
            ((>= kept 0) (r-opnn g rop-load k kept))
            (else
             (tagcase a
               (a-e (x) (r-into g x k env te))
               (a-v (v) (r-const-into g v k))
               (a-slot (s) (r-opnn g rop-load k s))
               (a-lexical (j) (r-lexical-into g j k))
               (a-thunk (b) #u)
               (a-as-is (x) #u)
               (a-name (n)
                 (let ((l (r-where env n)))
                   (if (null? l)
                       (r-decline)
                       (tagcase (car l)
                         (rl-slot (s) (r-opnn g rop-load k s))
                         (rl-reg (r) (if (= r k) #u (r-opnn g rop-movereg r k)))
                         (rl-free (j) (r-lexical-into g j k))
                         (rl-const (c) (r-const-into g (r-const-cell c) k))
                         (else y (r-decline)))))))))))
  ;; The list of the arguments from the `i`th down to the eighth, onto the
  ;; list in RESULT, by `cons`.
  (r-args-list (subr rcompiles (rgen rargs (listof int @k) int int renv cenv) unit)
    (lambda (g args kept i from env te)
      (if (< i from)
          #u
          (begin
            (r-opn g rop-setreg 2)
            (r-arg-into g (r-nth-arg args i) (r-nth-int kept i) 1 env te)
            (r-opnn g rop-cellular routine-cons 2)
            (r-args-list g args kept (- i 1) from env te)))))
  ;; `(list x …)`: every argument that is not simple, or is in a register,
  ;; made and kept first, in order, as for a list past `register-regs`; then
  ;; the pairs made from the last, onto `nil`.
  (r-list (subr rcompiles (rgen exps renv cenv) unit)
    (lambda (g args env te)
      (if (extract g leaf)
          (r-decline)
          (let* ((slots (get (extract g nslot))) (as (r-exp-args args))
                 (kept (r-args-hard g as 0 -1 env te #t)))
            (begin
              (r-op1 g rop-const (wcell-nil))
              (r-args-list g as kept (- (r-count-args as) 1) 0 env te)
              (set (extract g nslot) slots))))))
  ;; A call-out, `prim p n` or `cellular r n`, on `args` in REG1…REGn.
  (r-call-out (subr rcompiles (rgen int int rargs renv cenv) unit)
    (lambda (g how what args env te)
      (begin (r-args g args env te (the maybe-exp nil)) (r-opnn g how what (r-count-args args)))))
  (r-prim (subr rcompiles (rgen string rargs renv cenv) unit)
    (lambda (g name args env te)
      (let ((p (runtime-primitive name)))
        (if (< p 0) (r-decline) (r-call-out g rop-prim p args env te)))))
  ;; A closure of a lambda into RESULT, its free values into REG1…REGn first;
  ;; `own` as for `c-lambda-word`. With a `region` (an `rlambda`'s, one or
  ;; none), the closure is made there, by `%region-closure h fv … w`. What it
  ;; gives: for each sibling not made yet (a `letrec`'s), the free value's
  ;; index and the sibling's frame slot.
  ;; A leaf makes a closure only as its value, in tail position (`tail`): its
  ;; call-out, where the free space has no room, may collect, and then
  ;; nothing but the closure is used after. The lambda's word is one the
  ;; stack code made (`c-made-word`); register code makes none.
  (r-lambda (subr rcompiles (rgen exp-params exp renv cenv syms maybe-exp bool) patches)
    (lambda (g ps body env te own region tail)
      (if (and (extract g leaf) (not (and tail (null? region))))
          (begin (r-decline) (the patches nil))
          (let ((m (c-made-word ps body te own)))
            (if (null? m)
                (begin (r-decline) (the patches nil))
                (r-lambda-made g (car m) env te region))))))
  ;; The closure of word and free values `made`.
  (r-lambda-made (subr rcompiles (rgen (productof (1 tword) (2 syms)) renv cenv maybe-exp) patches)
    (lambda (g made env te region)
      (let* ((w (extract made 1))
             (fv (extract made 2))
             (n (c-length fv)))
        (if (null? region)
            ;; Past `register-regs`, the rest a list, as a call's
            ;; arguments are (`r-args`).
            (if (> n register-regs)
                (let ((pa (r-free-args fv env 0)))
                  (begin (r-args g (extract pa 1) env te (the maybe-exp nil))
                         (r-op2 g rop-lambda (wcell-word w) (wcell-int n))
                         (extract pa 2)))
                (let ((patches (r-free-into-regs g fv env)))
                  (begin (r-op2 g rop-lambda (wcell-word w) (wcell-int n)) patches)))
            (let* ((pa (r-free-args fv env 0))
                   (ops (r-append-arg (extract pa 1) (a-v (wcell-word w)))))
              (begin
                (r-prim g "%region-closure" (the rargs (cons (a-e (car region)) ops)) env te)
                (extract pa 2)))))))
  ;; Arrays, and the tag and key makers: as the stack compiler does them.
  (r-special (subr rcompiles (rgen string exps renv cenv) unit)
    (lambda (g what args env te)
      (case what
        (("array-ref")
         (begin
           (r-exp-args-into g args env te)
           (r-index-field g)
           (r-opnn g rop-cellular routine-field-ref 2)))
        (("array-set!")
         (let ((p (runtime-primitive "%bloblet-set!")))
           (begin
             (r-exp-args-into g args env te)
             (r-index-field g)
             (r-opnn g rop-prim p 3)
             (r-unit g))))
        (("array-length")
         (begin (r-prim g "%bloblet-fields" (r-exp-args args) env te)
                (r-add-imm g -1)))
        (("make-array") (r-prim g "%make-bloblet-filled" (r-make-array-ops args) env te))
        (("make-box")
         (r-prim g "%make-box" (the rargs (cons (a-v (wcell-unit)) nil)) env te))
        ;; The runtime's, which refuses a pair not to be written; then
        ;; unit.
        (("set-car!" "set-cdr!")
         (begin (r-prim g what (r-exp-args args) env te) (r-unit g)))
        (else (r-decline)))))
  ;; `tagcase`: the scrutinee kept; each arm's tag compared, the last's not
  ;; when there is no `else` (a checked program covers every tag); the value,
  ;; or its product's members, bound.
  (r-tagcase (subr rcompiles (rgen exp exp-arms exp-let-bs renv cenv bool) unit)
    (lambda (g s arms els env te tail)
      (let ((regs (get (extract g nreg))) (slots (get (extract g nslot))))
        (begin
          (r-exp g s env te #f)
          (let* ((sc (r-place-value g)) (end (r-new-label g)))
            (begin
              (r-arms g arms (null? els) sc end env te tail)
              (if (null? els)
                  #u
                  (let ((n (extract (car els) 1)))
                    (r-exp g (extract (car els) 2) (r-bind n sc env) (r-local te n) tail)))
              (r-emit g (r-label end))))
          (r-restore g regs slots)))))
  (r-arms (subr rcompiles (rgen exp-arms bool rloc int renv cenv bool) unit)
    (lambda (g arms no-else sc end env te tail)
      (if (null? arms)
          #u
          (let* ((arm (car arms)) (last (and no-else (null? (cdr arms)))) (next (r-new-label g))
                 (regs (get (extract g nreg))) (slots (get (extract g nslot))))
            (begin
              (if last
                  #u
                  (begin (r-get g sc) (r-opn g rop-field 2)
                         (r-op2imm g routine-eq (wcell-symbol (extract arm 1)))
                         (r-emit g (r-branch #t next))))
              (let* ((bound (if (extract arm 2)
                                (r-members g sc (extract arm 3) 0 (the renv nil))
                                (begin (r-get g sc) (r-opn g rop-field 3)
                                       (r-bind (car (extract arm 3)) (r-place-value g) nil))))
                     (in-order (r-reverse-env bound nil)))
                (r-exp g (extract arm 4) (r-bind-all in-order env) (r-local-all in-order te) tail))
              (r-restore g regs slots)
              (if tail #u (r-emit g (r-branch #f end)))
              (r-emit g (r-label next))
              (r-arms g (cdr arms) no-else sc end env te tail))))))
  ;; A tail call of the procedure itself: the new arguments made, then put
  ;; where the parameters are, and back to the start.
  (r-loop (subr rcompiles (rgen exps renv cenv) unit)
    (lambda (g args env te)
      (let* ((regs (get (extract g nreg)))
             (slots (get (extract g nslot)))
             (made (r-loop-make g args env te)))
        (begin
          (r-loop-move g made 0)
          (r-emit g (r-branch #f (extract g start)))
          (r-restore g regs slots)))))
  (r-loop-make (subr rcompiles (rgen exps renv cenv) (listof int @k))
    (lambda (g args env te)
      (if (null? args)
          nil
          (begin
            (r-exp g (car args) env te #f)
            (let ((m (if (extract g leaf) (r-keep-in-reg g) (r-keep-in-slot g))))
              (cons m (r-loop-make g (cdr args) env te)))))))
  ;; `letrec`: each closure made into its slot, a placeholder for a sibling
  ;; not made yet; then each placeholder patched.
  (r-letrec (subr rcompiles (rgen exp-letrec-bs exp renv cenv bool) unit)
    (lambda (g bs body env te tail)
      (let* ((slots (get (extract g nslot))) (regs (get (extract g nreg)))
             (joins (r-join-flags bs body tail))
             ;; A slot for each closure (a join point is none).
             (at (r-letrec-slots-j g joins))
             (patches (r-letrec-make g bs bs at 0 env te joins))
             (te2 (r-letrec-te-j bs joins te))
             ;; Each join point's parameters' places, and its label.
             (places (begin (r-letrec-patch g patches at) (r-join-places g bs joins te2)))
             (env2 (r-letrec-env-j bs at places env)))
        (begin
          (r-exp g body env2 te2 tail)
          (r-join-bodies g bs places env2 te2 tail)
          (r-restore g regs slots)))))
  ;; A `let`: each value made, in the scope outside, and kept in a register
  ;; where no call comes before the body is done with it (else the frame).
  (r-let (subr rcompiles (rgen exp-let-bs exp renv cenv bool) unit)
  (lambda (g bs body env te tail)
    (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
           (body-collects (r-collects-here? g body (r-local-names te bs) tail))
           (flags (r-in-regs g (r-let-inits bs) 0 te body-collects)))
      (let ((bound (r-let-bind g bs env te flags)))
        (begin
          (r-exp g body (r-bind-all bound env) (r-local-all bound te) tail)
          (r-restore g regs slots))))))
  ;; A join point's call: each argument made and kept (a register in a
  ;; leaf, else a frame slot), then each into its parameter's place, and a
  ;; jump.
  (r-jump (subr rcompiles (rgen rloc exps renv cenv bool) unit)
    (lambda (g j args env te tail)
      (tagcase j
        (rl-join (params label)
          (if (or (not tail) (not (= (c-count-exps args) (c-length-locs params))))
              (r-decline)
              (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
                     ;; Each kept in a register where no later argument calls.
                     (made (r-jump-args g args env te (r-in-regs g args 0 te #f))))
                (begin
                  (r-jump-moves g made params)
                  (r-emit g (r-branch #f label))
                  (r-restore g regs slots)))))
        (else y (r-decline)))))
  (r-jump-args (subr rcompiles (rgen exps renv cenv bools) rlocs)
    (lambda (g args env te flags)
      (if (null? args)
          nil
          (let* ((l (begin (r-exp g (car args) env te #f) (r-keep g (car flags))))
                 (rest (r-jump-args g (cdr args) env te (cdr flags))))
            (cons l rest)))))
  ;; Each join point's body, after the `letrec`'s, which ends every path
  ;; itself: where its calls go.
  (r-join-bodies (subr rcompiles (rgen exp-letrec-bs rplaces renv cenv bool) unit)
    (lambda (g bs places env te tail)
      (if (null? bs)
          #u
          (begin
            (if (null? (car places))
                #u
                (tagcase (car (c-lambda-of (extract (car bs) 3)))
                  (e-lambda (ps lbody la lb)
                    (let ((p (car (car places))))
                      (begin
                        (r-emit g (r-label (cdr p)))
                        (let ((inner (r-bind-places env ps (car p))))
                          (r-exp g lbody inner (r-local-params te ps) tail)))))
                  (else y (r-decline))))
            (r-join-bodies g (cdr bs) (cdr places) env te tail)))))
  (r-letrec-make
    (subr rcompiles (rgen exp-letrec-bs exp-letrec-bs rints int renv cenv bools)
          (listof patches @k))
    (lambda (g all bs at i env te joins)
      (cond
        ((null? bs) nil)
        ;; A join point is no closure.
        ((car joins)
         (cons (the patches nil) (r-letrec-make g all (cdr bs) at (+ i 1) env te (cdr joins))))
        (else
          (let* ((lam (c-lambda-of (extract (car bs) 3)))
                 (name (extract (car bs) 1))
                 (p (tagcase (car lam)
                      (e-lambda (ps lbody a b)
                        (r-letrec-one g all at i name ps lbody (the maybe-exp nil) env te))
                      (e-rlambda (r l a b)
                        (tagcase l
                          (e-lambda (ps lbody la lb)
                            (r-letrec-one g all at i name ps lbody (r-just-exp r) env te))
                          (else y (begin (r-decline) (the patches nil)))))
                      (else y (begin (r-decline) (the patches nil))))))
            (begin
              (r-opn g rop-setstk (r-nth-int at i))
              (cons p (r-letrec-make g all (cdr bs) at (+ i 1) env te (cdr joins)))))))))
  (r-letrec-one
    (subr rcompiles (rgen exp-letrec-bs rints int symbol exp-params exp maybe-exp renv cenv)
          patches)
    (lambda (g all at i name ps lbody region env te)
      (let* ((n (c-count-params ps))
             (own (r-sibling-env all at i 0 lbody n env te))
             ;; The closure's own name, as it knows itself.
             (self (the syms (cons name nil))))
        (r-lambda g ps lbody (extract own 1) (extract own 2) self region #f))))
  ;;; ------------------------------------------------------------- modules
  ;;; (`docs/research/first-class-modules.md`, stage M3), as the Rust
  ;;; compiler's `r_module` and `r_with` make them; their helpers in
  ;;; `regcode-modules.fx`.
  ;; Item `n`'s lambda `x`, naming items of `later` not made yet: those
  ;; captured as a `letrec`'s siblings are, to be given once made.
  (r-module-closure (subr rcompiles (rgen symbol exp r-scopes c-mslots) patches)
    (lambda (g n x sc later)
      (let ((self (the syms (cons n nil))))
        (tagcase (car (c-lambda-of x))
          (e-lambda (ps lbody a b)
            (let ((own (r-module-own n sc later lbody (c-count-params ps))))
              (r-lambda g ps lbody (car own) (cdr own) self (the maybe-exp nil) #f)))
          (e-rlambda (r l a b)
            (tagcase l
              (e-lambda (ps lbody la lb)
                (let ((own (r-module-own n sc later lbody (c-count-params ps))))
                  (r-lambda g ps lbody (car own) (cdr own) self (r-just-exp r) #f)))
              (else y (begin (r-decline) (the patches nil)))))
          (else y (begin (r-decline) (the patches nil)))))))
  ;; Values `vs` made in their slots, `later`, in order, as a `letrec*`'s
  ;; (`DONE.md` §37): a typed lambda naming an item not made yet captures it
  ;; once it is made; `ws` the closures waiting, `vals` the values' slots so
  ;; far (newest first): all of them.
  (r-module-make (subr rcompiles (rgen c-mvals r-scopes c-mslots c-waits rints) rints)
    (lambda (g vs sc later ws vals)
      (if (null? vs)
          vals
          (let* ((v (car vs)) (n (extract v 1)) (x (extract v 2)) (s (cdr (car later)))
                 (ps (if (and (extract v 4) (c-names-any? x later))
                         (r-module-closure g n x sc later)
                         (begin (r-exp g x (car sc) (cdr sc) #f) (the patches nil))))
                 (kept (r-opn g rop-setstk s))
                 (inner (the r-scopes (cons (r-bind n (rl-slot s) (car sc)) (r-local (cdr sc) n))))
                 (waits (c-waits-onto ws s ps))
                 (given (r-give-waiting g waits s)))
            (r-module-make g (cdr vs) inner (cdr later) waits
                           (if (= (extract v 3) 0) vals (the rints (cons s vals))))))))
  ;; A module: its items made in frame slots in order, as its stack code
  ;; makes them; then the product of its values. Declined in a leaf.
  (r-module (subr rcompiles (rgen mod-items renv cenv bool) unit)
    (lambda (g items env te tail)
      (if (extract g leaf)
          (r-decline)
          (let* ((slots (get (extract g nslot)))
                 (vs (c-module-values items))
                 (later (r-module-slots g vs))
                 (vals (r-module-make g vs (the r-scopes (cons env te)) later nil nil)))
            (begin (r-make-frozen g 37 (r-slots-oldest vals nil) env te)
                   (set (extract g nslot) slots)
                   (r-done g tail))))))
  ;; `with`: the module's values the body names, by position, each kept as
  ;; a `let`'s value is (in a leaf, in a register), or folded in a fast
  ;; version (`r-with-fields`); then the body. As the Rust compiler's `r_with`.
  (r-with (subr rcompiles (rgen symbol exp int int renv cenv bool) unit)
    (lambda (g m body a b env te tail)
      (let ((ns (c-with-at a b)) (ps (c-with-places-at a b)))
        (if (or (null? ns) (null? ps))
            (r-fx-value g m body tail)
            (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
                   (sc (r-with-fields g m env (car ns) (car ps) (the r-scopes (cons env te)))))
              (begin (r-exp g body (car sc) (cdr sc) tail) (r-restore g regs slots)))))))
  (r-module-or-with (subr rcompiles (rgen exp renv cenv bool) unit)
    (lambda (g x env te tail)
      (tagcase x
        (e-module (items a b) (r-module g items env te tail))
        (e-with (m body a b) (r-with g m body a b env te tail))
        (else y (r-decline)))))
  (r-reshape (subr rcompiles (rgen exp k-ids renv cenv bool) unit)
    (lambda (g x at env te tail)
      (if (extract g leaf)
          (r-decline)
          (let* ((slots (get (extract g nslot)))
                 (m (begin (r-exp-as-is g x env te #f) (r-keep-in-slot g)))
                 (args (r-reshape-fields g m at nil)))
            (begin (r-make-frozen g 37 (r-args-reversed args nil) env te)
                   (set (extract g nslot) slots)
                   (r-done g tail))))))
  ;;; ------------------------------------------------- a leaf's tail call
  ;; A call in tail position in a leaf, which has no frame, as the Rust
  ;; compiler's `r_leaf_tail_call`: the arguments sorted (`r-leaf-args`);
  ;; the procedure into RESULT now if nothing after the moves uses RESULT,
  ;; else kept in a register; the moves; the simple arguments; the call.
  ;; Its own registers are above REG1…REGn.
  (r-leaf-tail-call (subr rcompiles (rgen exp exps renv cenv) unit)
    (lambda (g f args env te)
      (let* ((nreg (extract g nreg))
             (regs (get nreg))
             ;; Registers of its own above the arguments' as well as the leaf's.
             (above (set nreg (max regs (c-count-exps args))))
             (made (r-leaf-args g args env te 1))
             (late (extract made late))
             (quiet (and (null? late) (not (r-moves-cycle? (extract made moves)))))
             (fr (r-reg-of (r-plain-var-loc env f)))
             (written (and (> fr 0) (r-written? fr (extract made moves) late)))
             ;; Where the procedure is after the moves: a register; 0, to
             ;; be fetched; -1, in RESULT.
             (at (cond ((and (> fr 0) (not written)) fr)
                       ((and written quiet) (begin (r-opn g rop-reg fr) -1))
                       (written (r-reg g))
                       ((r-simple? f) 0)
                       (else (begin (r-exp g f env te #f) (if quiet -1 (r-keep-in-reg g))))))
             (moves (if (and written (not quiet))
                        (r-moves-snoc (extract made moves) fr at)
                        (extract made moves))))
        (begin
          (r-par-moves g moves)
          (r-late-into g late env te)
          (cond ((> at 0) (r-opn g rop-reg at)) ((= at 0) (r-exp g f env te #f)) (else #u))
          (r-opn g rop-tailinvoke (c-count-exps args))
          (set nreg regs)))))
  ;; A leaf's tail call's arguments from REGk: one in a register moved from
  ;; there; a simple one left for after the moves; any other made now, in
  ;; order, into a register of its own, and moved from there.
  (r-leaf-args (subr rcompiles (rgen exps renv cenv int) rleaf)
    (lambda (g args env te k)
      (if (null? args)
          (r-rleaf (the rmoves nil) (the rlate nil))
          (let* ((a (car args)) (r (r-reg-of (r-plain-var-loc env a))))
            (cond ((> r 0)
                   (let ((rest (r-leaf-args g (cdr args) env te (+ k 1))))
                     (if (= r k) rest (r-leaf-move rest r k))))
                  ((r-simple? a) (r-leaf-late (r-leaf-args g (cdr args) env te (+ k 1)) k a))
                  (else
                   (let ((t (begin (r-exp g a env te #f) (r-keep-in-reg g))))
                     (r-leaf-move (r-leaf-args g (cdr args) env te (+ k 1)) t k))))))))
  ;; Each simple argument of `late` into its register.
  (r-late-into (subr rcompiles (rgen rlate renv cenv) unit)
    (lambda (g late env te)
      (if (null? late)
          #u
          (let ((one (car late)))
            (begin (r-into g (cdr one) (car one) env te) (r-late-into g (cdr late) env te))))))))))
