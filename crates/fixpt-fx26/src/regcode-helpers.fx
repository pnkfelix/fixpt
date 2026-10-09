;;; Register code, in FX-26: helpers of the compiler proper,
;;; `regcode-core.fx`. `regcode.fx` first (PLAN.md 13h′).

;;; ------------------------------------------- helpers of the compiler proper

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((regcode-helpers-types (load-module "fx26:regcode-helpers-types.fx"))
       (regcode-types (load-module "fx26:regcode-types.fx"))
       (compile-types (load-module "fx26:compile-types.fx"))
       (compile-exps-types (load-module "fx26:compile-exps-types.fx"))
       (compile-state-types (load-module "fx26:compile-state-types.fx"))
       (compile-plan-types (load-module "fx26:compile-plan-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-subst-types (load-module "fx26:check-subst-types.fx"))
       (regcode-exps-types (load-module "fx26:regcode-exps-types.fx"))
       (regcode-places-types (load-module "fx26:regcode-places-types.fx"))
       (compile-lift-types (load-module "fx26:compile-lift-types.fx"))
       (check-resolve-types (load-module "fx26:check-resolve-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx"))
       (table-types (load-module "fx26:table-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((regcode (select regcode-types regcode-sig))
           (compile (select compile-types compile-sig))
           (compile-exps (select compile-exps-types compile-exps-sig))
           (compile-plan (select compile-plan-types compile-plan-sig))
           (compile-lift (select compile-lift-types compile-lift-sig))
           (check-resolve (select check-resolve-types check-resolve-sig))
           (regcode-exps (select regcode-exps-types regcode-exps-sig))
           (layout (select layout-types layout-sig))
           (tables (select table-types tables-sig))
           (regcode-places (select regcode-places-types regcode-places-sig))
           (compile-state (select compile-state-types compile-state-sig)))
    (module
(define-type maybe-exp (select regcode-helpers-types maybe-exp))
(define-type r-unroll-known (select regcode-helpers-types r-unroll-known))
(define-type r-wglobals (select regcode-helpers-types r-wglobals))
(define-type r-unroll-found (select regcode-helpers-types r-unroll-found))
(define-type r-unroll-hook (select regcode-helpers-types r-unroll-hook))
(define-type r-unroll-globals (select regcode-helpers-types r-unroll-globals))
(define-type rsplit (select regcode-helpers-types rsplit))
(define-type rsplits (select regcode-helpers-types rsplits))
(define-type rmade (select regcode-helpers-types rmade))
(define-type roperands (select regcode-helpers-types roperands))
;; The types it uses of the files before it.
(define a-e (with regcode-types a-e))
(define a-v (with regcode-types a-v))
(define-effect emits (select regcode-types emits))
(define-type rarg (select regcode-types rarg))
(define-type rargs (select regcode-types rargs))
(define-effect rbuilds (select regcode-types rbuilds))
(define rc-int (with regcode-types rc-int))
(define rc-nil (with regcode-types rc-nil))
(define rc-pair (with regcode-types rc-pair))
(define-effect rcompiles (select regcode-types rcompiles))
(define-type rconst (select regcode-types rconst))
(define-type rconsts (select regcode-types rconsts))
(define-type renv (select regcode-types renv))
(define-type rgen (select regcode-types rgen))
(define rl-free (with regcode-types rl-free))
(define rl-global (with regcode-types rl-global))
(define rl-reg (with regcode-types rl-reg))
(define rl-slot (with regcode-types rl-slot))
(define rl-test (with regcode-types rl-test))
(define-type rlocs (select regcode-types rlocs))
(define-effect rreads (select regcode-types rreads))
(define-effect rscans (select regcode-types rscans))
(define-type rthis (select regcode-types rthis))
(define-type wcells (select regcode-types wcells))
(define-type c-spec-copies (select compile-types c-spec-copies))
(define-type cenv (select compile-types cenv))
(define-type exps (select compile-types exps))
(define-type items (select compile-types items))
(define-type patches (select compile-types patches))
(define-type syms (select compile-types syms))
(define-type c-lift (select compile-types c-lift))
(define-type c-inline (select compile-exps-types c-inline))
(define-type c-spec (select compile-exps-types c-spec))
(define-type c-special (select compile-plan-types c-special))
(define e-app (with parser-types e-app))
(define e-bool (with parser-types e-bool))
(define e-char (with parser-types e-char))
(define e-int (with parser-types e-int))
(define e-var (with parser-types e-var))
(define-type exp (select parser-types exp))
(define-type exp-params (select check-subst-types exp-params))
(define-type rinline (select regcode-exps-types rinline))
;; What it uses of the modules it is given.
(define r-add-name? (with regcode r-add-name?))
(define r-bind (with regcode r-bind))
(define r-const-cell (with regcode r-const-cell))
(define r-const-in (with regcode r-const-in))
(define r-const-lists (with regcode r-const-lists))
(define r-const-small (with regcode r-const-small))
(define r-decline (with regcode r-decline))
(define r-done (with regcode r-done))
(define r-exp-args (with regcode r-exp-args))
(define r-known (with regcode r-known))
(define r-lifted-at (with regcode r-lifted-at))
(define r-name-args (with regcode r-name-args))
(define r-op1 (with regcode r-op1))
(define r-op2 (with regcode r-op2))
(define r-opn (with regcode r-opn))
(define r-par-moves (with regcode r-par-moves))
(define r-reg-moves (with regcode r-reg-moves))
(define r-same-exp? (with regcode r-same-exp?))
(define r-simple? (with regcode r-simple?))
(define r-small? (with regcode r-small?))
(define r-standard-name (with regcode r-standard-name))
(define r-test-desc (with regcode r-test-desc))
(define r-where (with regcode r-where))
(define c-count-exps (with compile c-count-exps))
(define c-count-params (with compile c-count-params))
(define c-genv (with compile c-genv))
(define c-genv-now (with compile c-genv-now))
(define c-lifts (with compile c-lifts))
(define c-member? (with compile c-member?))
(define c-spec-made (with compile c-spec-made))
(define c-summary-at (with compile c-summary-at))
(define c-fx-name (with compile-state c-fx-name))
(define c-lift (with compile-exps c-lift))
(define c-inlining (with compile-plan c-inlining))
(define c-spec-copy-find (with compile-plan c-spec-copy-find))
(define c-unrolls-of (with compile-plan c-unrolls-of))
(define c-lambda-captured (with compile-lift c-lambda-captured))
(define c-lift-added (with compile-lift c-lift-added))
(define c-span-key (with compile-lift c-span-key))
(define exp-end (with check-resolve exp-end))
(define exp-start (with check-resolve exp-start))
(define r-assume (with regcode-exps r-assume))
(define r-collects (with regcode-exps r-collects))
(define r-free-regs (with regcode-places r-free-regs))
(define r-guard (with regcode-exps r-guard))
(define r-inline-named (with regcode-exps r-inline-named))
(define r-inline-of (with regcode-exps r-inline-of))
(define r-local-params (with regcode-exps r-local-params))
(define r-local-syms (with regcode-exps r-local-syms))
(define r-nth-param (with regcode-exps r-nth-param))
(define r-standard-value (with regcode-exps r-standard-value))
(define rop-const (with layout rop-const))
(define rop-global (with layout rop-global))
(define rop-lexical (with layout rop-lexical))
(define rop-op2imm (with layout rop-op2imm))
(define rop-reg (with layout rop-reg))
(define rop-setreg (with layout rop-setreg))
(define rop-stack (with layout rop-stack))
(define routine-eq (with layout routine-eq))
(define routine-int-add (with layout routine-int-add))
(define routine-int-sub (with layout routine-int-sub))
(define std-nil-name? (with tables std-nil-name?))
(define table-ref (with tables table-ref))

(define r-unroll-hooks (ref (listof r-unroll-hook @k) @k) (new nil))
;; The procedure `f` names, if one of `c-unrolls`, with its global, called
;; on `args` with at least one constant list (a constant, or a global that
;; is one), not unrolled 16 deep here, and its body writing no global: in a
;; list, the call's hook noted. As the Rust compiler's `r_unrolled`.
(define r-unrolled (subr (maxeff emits spin) (renv exp exps) (listof rinline @k))
  (lambda (env f args)
    (tagcase f
      (e-var (n a b)
        (let ((l (r-where env n)))
          (if (null? l)
              nil
              (tagcase (car l)
                (rl-global (cell)
                  (let ((i (r-inline-named (c-unrolls-of n) n (c-count-exps args) (get c-genv))))
                    (if (or (null? i) (>= (r-count-name (get c-inlining) n 0) 16))
                        nil
                        (r-unroll-noted f n cell (car i) (r-unroll-knowns env args)))))
                (else y nil)))))
      (else y nil))))
(define r-count-name (subr rscans (syms symbol int) int)
  (lambda (ns n k)
    (if (null? ns) k (r-count-name (cdr ns) n (if (symbol=? (car ns) n) (+ k 1) k)))))
;; The hook of a call of `i` (`n`'s, in `cell`) that unrolls, noted: its
;; guards, the procedure's global unless within its own unrolling, then
;; each global a list was read from.
(define r-unroll-noted
  (subr (maxeff emits spin) (exp symbol wglobal c-inline r-unroll-found) (listof rinline @k))
  (lambda (f n cell i ks)
    (let ((body (extract i 4)))
      (if (or (not (extract ks 3)) (>= (c-summary-at (exp-start body) (exp-end body)) 3))
          nil
          (let* ((own (if (c-member? (get c-inlining) n)
                          (the r-wglobals nil)
                          (the r-wglobals (cons cell nil))))
                 (h (product (1 f) (2 (extract ks 1)) (3 (r-wglobals-append own (extract ks 2)))))
                 (rest (get r-unroll-hooks))
                 (same (and (not (null? rest)) (r-same-exp? (extract (car rest) 1) f)))
                 (under (if same (cdr rest) rest)))
            (begin (set r-unroll-hooks (cons h under))
                   (the (listof rinline @k) (cons (cons i cell) nil))))))))
(define r-wglobals-append (subr rbuilds (r-wglobals r-wglobals) r-wglobals)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (r-wglobals-append (cdr xs) ys)))))
;; Each of `args` that is a global holding a constant list, with it, and
;; those globals, in order; and whether any argument is a constant list.
(define r-unroll-knowns (subr (maxeff emits spin) (renv exps) r-unroll-found)
  (lambda (env args)
    (if (null? args)
        (product (1 (the r-unroll-known nil)) (2 (the r-wglobals nil)) (3 #f))
        (let* ((a (car args)) (rest (r-unroll-knowns env (cdr args)))
               (k (r-known env a))
               (g (if (null? k) (r-unroll-global env a) (the r-unroll-globals nil)))
               (c (cond ((not (null? k)) k)
                        ((null? g) (the rconsts nil))
                        (else (the rconsts (cons (cdr (car g)) nil))))))
          (cond ((or (null? c) (not (r-const-list? (car c)))) rest)
                ((null? g) (product (1 (extract rest 1)) (2 (extract rest 2)) (3 #t)))
                (else (product (1 (the r-unroll-known (cons (cons a (car c)) (extract rest 1))))
                               (2 (the r-wglobals (cons (car (car g)) (extract rest 2))))
                               (3 #t))))))))
(define r-unroll-global (subr rbuilds (renv exp) r-unroll-globals)
  (lambda (env a)
    (tagcase a
      (e-var (n x y)
        (let ((l (r-where env n)))
          (if (null? l)
              nil
              (tagcase (car l)
                (rl-global (g)
                  (let ((c (r-const-in (table-ref (get r-const-lists) (wglobal-name g) nil) g)))
                    (if (null? c) nil (the r-unroll-globals (cons (cons g (car c)) nil)))))
                (else z nil)))))
      (else z nil))))
(define r-const-list? (subr pure (rconst) bool)
  (lambda (c) (tagcase c (rc-pair (a d) #t) (rc-nil () #t) (else y #f))))
;; An inlined call's argument `a` as a constant: the unrolled call's, if it
;; is one of its globals' lists; else what `r-known` says. And as the
;; call's argument, where a guard fails: a global's read again, as the
;; guard fails where it was written since; else the constant.
(define r-known-slow (subr rbuilds (exp rconst) rarg)
  (lambda (a k)
    (let ((h (get r-unroll-hooks)))
      (if (or (null? h) (null? (r-unroll-known-of (extract (car h) 2) a)))
          (a-v (r-const-cell k))
          (a-e a)))))
(define r-known-arg (subr rbuilds (renv exp) rconsts)
  (lambda (env a)
    (let* ((h (get r-unroll-hooks))
           (k (if (null? h) (the rconsts nil) (r-unroll-known-of (extract (car h) 2) a))))
      (if (null? k) (r-known env a) k))))
(define r-unroll-known-of (subr rbuilds (r-unroll-known exp) rconsts)
  (lambda (ks a)
    (cond ((null? ks) nil)
          ((r-same-exp? (car (car ks)) a) (the rconsts (cons (cdr (car ks)) nil)))
          (else (r-unroll-known-of (cdr ks) a)))))
;; An inlined call of `f`'s guards, each to `call` unless assumed: on its
;; global `cell`, or, for a call unrolled, its hook's (taken off); whether
;; any was made.
(define r-guards-for (subr (maxeff emits spin) (rgen wglobal exp int) bool)
  (lambda (g cell f call)
    (let* ((h (get r-unroll-hooks))
           (mine (and (not (null? h)) (r-same-exp? (extract (car h) 1) f)))
           (cells (if mine (extract (car h) 3) (the r-wglobals (cons cell nil)))))
      (begin (if mine (set r-unroll-hooks (cdr h)) #u)
             (r-guard-all g cells call #f)))))
(define r-guard-all (subr (maxeff emits spin) (rgen r-wglobals int bool) bool)
  (lambda (g cs call any)
    (cond ((null? cs) any)
          ((r-assume (car cs)) (r-guard-all g (cdr cs) call any))
          (else (begin (r-guard g (car cs) call) (r-guard-all g (cdr cs) call #t))))))
;; The operand an identity leaves, `x` of `x + 0`, `0 + x`, `x - 0`, `x * 1`
;; or `1 * x`, in a list, if `name` applied to `args` is one. As the Rust
;; compiler's `r_identity_arg`.
(define r-identity-arg (subr rbuilds (renv string exps) (listof exp @k))
  (lambda (env name args)
    (if (or (not (= (c-count-exps args) 2))
            (not (or (string=? name "+") (or (string=? name "-") (string=? name "*")))))
        nil
        (let* ((x (car args)) (y (car (cdr args)))
               (a (r-known env x)) (b (r-known env y))
               (is (lambda ((c rconsts) (n int))
                     (and (not (null? c)) (tagcase (car c) (rc-int (k) (= k n)) (else z #f))))))
          (cond ((and (string=? name "+") (is b 0)) (cons x nil))
                ((and (string=? name "+") (is a 0)) (cons y nil))
                ((and (string=? name "-") (is b 0)) (cons x nil))
                ((and (string=? name "*") (is b 1)) (cons x nil))
                ((and (string=? name "*") (is a 1)) (cons y nil))
                (else nil))))))
;; A call of lifted procedure `f`'s arguments: the names it would have
;; captured, then `args` (`r-call`).
(define r-lifted-call-args (subr rbuilds (renv exp exps) rargs)
  (lambda (env f args) (r-name-args (c-lift-added (r-lifted-at env f)) (r-exp-args args))))
;; `env` in an arm of an `if` on `t`, where it is `v`: the test decided, if
;; it is a comparison of places and constants (`r-known-test`), bound to no
;; name a program can write. As the Rust compiler's `RLoc::Test`.
(define r-knowing (subr rbuilds (renv exp bool) renv)
  (lambda (env t v)
    (let ((d (r-test-desc env t)))
      (if (null? d) env (r-bind '%if (rl-test (car (car d)) (cdr (car d)) v) env)))))
(define-rec
  ;; `x` as `core + k`: `core` the one operand of a chain of `+`, and of `-`
  ;; of constants, that is not a constant (none if all are), and `k` the
  ;; constants' sum, under 2^30 in size; else `x` itself and 0.
  (r-split (subr rbuilds (renv exp) rsplit)
    (lambda (env x)
      (let* ((c (r-known env x))
             (small (if (null? c) (the (listof int @k) nil) (r-const-small (car c)))))
        (if (not (null? small))
            (product (1 (the (listof exp @k) nil)) (2 (car small)))
            (let ((s (tagcase x
                       (e-app (f args a b) (r-split-app env (r-standard-name env f) args))
                       (else y (the rsplits nil)))))
              (if (null? s) (product (1 (the (listof exp @k) (cons x nil))) (2 0)) (car s)))))))
  ;; The same for standard operation `name` applied to `args`, if it is
  ;; such a chain.
  (r-split-app (subr rbuilds (renv string exps) rsplits)
    (lambda (env name args)
      (if (or (not (= (c-count-exps args) 2)) (not (r-add-name? name)))
          (the rsplits nil)
          (let* ((sa (r-split env (car args))) (sb (r-split env (car (cdr args))))
                 (pa (extract sa 1)) (pb (extract sb 1))
                 (plus (string=? name "+"))
                 (k (if plus (+ (extract sa 2) (extract sb 2)) (- (extract sa 2) (extract sb 2)))))
            (cond ((and plus (and (not (null? pa)) (not (null? pb)))) nil)
                  ((and (not plus) (not (null? pb))) nil)
                  ((not (r-small? k)) nil)
                  (else (the rsplits (cons (product (1 (if (null? pa) pb pa)) (2 k)) nil)))))))))
;; A call's inlining: unrolled, if `r-unrolled` says so; else as planned.
(define r-inline-or-unroll
  (subr (maxeff emits spin) (int int renv exp exps int) (listof rinline @k))
  (lambda (a b env f args n)
    (let ((u (r-unrolled env f args))) (if (null? u) (r-inline-of a b env f n) u))))
(define r-just-exp (subr (alloc @k) (exp) maybe-exp)
  (lambda (x) (the maybe-exp (cons x nil))))
;; A call-out's operands: `a` and `b`, or `a`, `b` and `c`.
(define r-args-2 (subr (alloc @k) (rarg rarg) rargs)
  ;; cons-chain: in `@k`, which goes when the compile does
  (lambda (a b) (the rargs (cons a (cons b nil)))))
(define r-args-3 (subr (alloc @k) (rarg rarg rarg) rargs)
  ;; cons-chain: in `@k`, as `r-args-2`'s
  (lambda (a b c) (the rargs (cons a (cons b (cons c nil))))))

;; `make-array`'s call-out's operands: the tag, 0; the length; the fill.
(define r-make-array-ops (subr (maxeff (read @globals) (alloc @k)) (exps) rargs)
  (lambda (args) (r-args-3 (a-v (wcell-int 0)) (a-e (car args)) (a-e (car (cdr args))))))
;; Constant `w` into RESULT; in tail position, returned.
(define r-const-value (subr emits (rgen wcell bool) unit)
  (lambda (g w tail) (begin (r-op1 g rop-const w) (r-done g tail))))
;; Unit into RESULT.
(define r-unit (subr emits (rgen) unit)
  (lambda (g) (r-op1 g rop-const (wcell-unit))))
;; RESULT := r(RESULT, v), `v` an immediate.
(define r-op2imm (subr emits (rgen int wcell) unit)
  (lambda (g r v) (r-op2 g rop-op2imm (wcell-int r) v)))
;; `k` added to RESULT, as an immediate; nothing, if 0.
(define r-add-imm (subr emits (rgen int) unit)
  (lambda (g k)
    (cond ((> k 0) (r-op2imm g routine-int-add (wcell-int k)))
          ((< k 0) (r-op2imm g routine-int-sub (wcell-int (- 0 k))))
          (else #u))))
;; RESULT negated: whether it is #f.
(define r-negate (subr emits (rgen) unit)
  (lambda (g) (r-op2imm g routine-eq (wcell-bool #f))))
;; An array's index, in REG2, made its field's: past the bloblet's first
;; two.
(define r-index-field (subr emits (rgen) unit)
  (lambda (g) (begin (r-opn g rop-reg 2) (r-add-imm g 2) (r-opn g rop-setreg 2))))
;; The registers and frame slots taken since there were `regs` and `slots`,
;; free again.
(define r-restore (subr (maxeff (read @k) (write @k)) (rgen int int) unit)
  (lambda (g regs slots) (begin (set (extract g nreg) regs) (set (extract g nslot) slots))))

;; Variable `n`'s value into RESULT, from where it is (`l`, in a list); if
;; nowhere, `nil`, or a standard operation as a value.
(define r-var-value (subr rcompiles (rgen rlocs symbol bool) unit)
  (lambda (g l n tail)
    (if (null? l)
        (if (std-nil-name? (symbol->string n))
            (r-op1 g rop-const (wcell-nil))
            (r-standard-value g (symbol->string n) tail))
        (tagcase (car l)
          (rl-reg (k) (r-opn g rop-reg k))
          (rl-slot (s) (r-opn g rop-stack s))
          (rl-free (i) (r-opn g rop-lexical i))
          (rl-global (c) (r-op1 g rop-global (wcell-global c)))
          (else y (r-decline))))))

;; `(with #%fx n)` where `n` is shadowed (the checker made it the plain `n`
;; elsewhere): the standard `n`'s value, as of a name bound nowhere
;; (`TODO.md` §46). Any other `with` the checker did not see: declined.
(define r-fx-value (subr rcompiles (rgen symbol exp bool) unit)
  (lambda (g m body tail)
    (let ((n (c-fx-name m body)))
      (if (string=? n "")
          (r-decline)
          (begin (r-var-value g (the rlocs nil) (string->symbol n) tail) (r-done g tail))))))
;; Whether `x` is an integer, boolean or character literal.
(define r-literal? (subr pure (exp) bool)
  (lambda (x) (tagcase x (e-int (n a b) #t) (e-bool (v a b) #t) (e-char (v a b) #t) (else z #f))))
;; Whether operand `x` neither has an effect nor sees one: a variable or a
;; constant (only a definition writes a global).
(define r-free-operand? (subr rbuilds (renv exp) bool)
  (lambda (env x) (or (r-simple? x) (not (null? (r-known env x))))))
;; Whether `core` (in a list) is there, and is neither `x` nor `y`.
(define r-deeper? (subr rreads (maybe-exp exp exp) bool)
  (lambda (core x y)
    (and (not (null? core))
         (let ((c (car core))) (and (not (r-same-exp? c x)) (not (r-same-exp? c y)))))))

;; The closure of lifted procedure `k` (`c-lifts`), a constant.
(define r-lifted-closure (subr rbuilds (int) wcell)
  (lambda (k)
    (let ((none (the c-lift (product (1 (wcell-nil)) (2 (the syms nil))))))
      (extract (table-ref (get c-lifts) k none) 1))))

;; What `g` makes, for a body where the procedure running is not known.
(define r-unknowing (subr (maxeff rreads (alloc @k)) (rgen) rgen)
  (lambda (g)
    (the rgen
      (product (items (extract g items)) (leaf (extract g leaf)) (nreg (extract g nreg))
               (nslot (extract g nslot)) (mslot (extract g mslot)) (labels (extract g labels))
               (this (the rthis nil)) (start (extract g start))))))

;; What the copy of `sp`'s procedure (global `cell`) specialized at lambda
;; `lps` `lbody`, seen in `te`, is made from (`c-spec`).
(define r-spec-of (subr rcompiles (c-special wglobal exp-params exp cenv) c-spec)
  (lambda (sp cell lps lbody te)
    (the c-spec
      (product (1 (extract sp 1)) (2 cell) (3 (extract sp 2)) (4 (extract sp 6))
               (5 (r-nth-param (extract sp 3) (extract sp 6)))
               (6 (c-count-params (extract sp 3)))
               (7 (extract sp 7)) (8 lps) (9 lbody)
               (10 (c-lambda-captured lps lbody te)) (11 (c-genv-now))))))
;; The copy `spec` of `sp`'s procedure, for lambda body `lbody`, in a
;; list: made once, with the form's words, for the procedure, the lambda,
;; what it captures and the globals it sees (`c-make-copy`); none if none
;; was.
(define r-spec-word (subr rcompiles (c-special c-spec exp) c-spec-copies)
  (lambda (sp spec lbody)
    (c-spec-copy-find (table-ref (get c-spec-made) (c-span-key (exp-start lbody) (exp-end lbody))
                                 (the c-spec-copies nil))
                      (extract sp 2) (extract spec 10) (extract spec 11))))
;; Each free value of `fv` into REGj+1 (`r-reg-moves`, `r-free-regs`): the
;; patches for the siblings not made yet.
(define r-free-into-regs (subr rcompiles (rgen syms renv) patches)
  (lambda (g fv env) (begin (r-par-moves g (r-reg-moves fv env 0)) (r-free-regs g fv env 0))))

;; Whether evaluating `x`, in `te`, may collect here: never in a leaf.
(define r-collects-here? (subr rcompiles (rgen exp cenv bool) bool)
  (lambda (g x te tail) (and (not (extract g leaf)) (r-collects x te (extract g this) tail))))
;; The cellular scope of the lambda's body, in a copy specialized at it
;; (`sp`): its parameters, and the values its closure captured.
(define r-spec-scope (subr rcompiles (c-spec) cenv)
  (lambda (sp) (r-local-syms (r-local-params (the cenv nil) (extract sp 8)) (extract sp 10))))
;; Whether that body may collect here (never in a leaf), as it is compiled:
;; in the globals the lambda saw.
(define r-spec-body-collects? (subr rcompiles (rgen c-spec bool) bool)
  (lambda (g sp tail)
    (and (not (extract g leaf))
         (let ((outer-genv (get c-genv)))
           (begin
             (set c-genv (extract sp 11))
             (let ((c (r-collects (extract sp 9) (r-spec-scope sp) (the rthis nil) tail)))
               (begin (set c-genv outer-genv) c)))))))

(define r-imm-operand (subr (alloc @k) (wcells) roperands)
  (lambda (v) (product (1 v) (2 (the (listof int @k) nil)))))
(define r-reg-operand (subr (alloc @k) (int) roperands)
  (lambda (k) (product (1 (the wcells nil)) (2 (the (listof int @k) (cons k nil))))))
;; `x`'s cell, in a list, if it is a constant (`r-known`).
(define r-known-cell (subr rbuilds (renv exp) wcells)
  (lambda (env x)
    (let ((k (r-known env x)))
      (if (null? k) nil (the wcells (cons (r-const-cell (car k)) nil)))))))))
