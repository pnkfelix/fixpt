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
(hide (include regcode-helpers-types) (include regcode-types) (include compile-types)
      (include compile-exps-types) (include compile-plan-types) (include parser-types)
      (include check-subst-types) (include regcode-exps-types) (include check-resolve-types))
;; The types it uses of the files before it.
;; What it uses of the modules it is given: all of each, hidden.
(hide (include layout) (include regcode) (include regcode-exps) (include compile-exps)
      (include compile) (include compile-state) (include compile-plan) (include compile-lift)
      (include check-resolve) (include regcode-places) (include tables))
;; What it uses of the modules it is given.

(define r-unroll-hooks (ref (listof r-unroll-hook @k) @k) (new nil))
;; The procedure `f` names, if one of `c-unrolls`, with its global, called
;; on `args` with at least one constant list (a constant, or a global that
;; is one), not unrolled 16 deep here, and its body writing no global: in a
;; list, the call's hook noted. As the Rust compiler's `r_unrolled`.
(define r-unrolled (subr (maxeff emits spin) (renv exp exps) (listof rinline @k))
  (lambda (env f args)
    (tagcase f
      (e-var (n a b abk)
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
      (if (or (not (extract ks 3))
              (>= (c-summary-at (exp-start body) (exp-end body) (exp-kth body)) 3))
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
      (e-var (n x y xyk)
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
                       (e-app (f args a b abk) (r-split-app env (r-standard-name env f) args))
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
  (subr (maxeff emits spin) (int int int renv exp exps int) (listof rinline @k))
  (lambda (a b abk env f args n)
    (let ((u (r-unrolled env f args))) (if (null? u) (r-inline-of a b abk env f n) u))))
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
  (lambda (x)
    (tagcase x (e-int (n a b abk) #t) (e-bool (v a b abk) #t) (e-char (v a b abk) #t) (else z #f))))
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
    (c-spec-copy-find (table-ref (get c-spec-made) (exp-at lbody)
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
      (if (null? k) nil (the wcells (cons (r-const-cell (car k)) nil))))))
;; The knot's `r-exp` and `r-prim`, as `r-bloblet` is given them.
(define-type r-exper (subr rcompiles (rgen exp renv cenv bool) unit))
(define-type r-primer (subr rcompiles (rgen string rargs renv cenv) unit))
;; A bloblet form `x`, by its field index, or else (a blobref's) what the
;; checker found of it: a scalar's layout, an array's, a flat sum's; then
;; done.
(define r-bloblet (subr rcompiles (rgen exp renv cenv bool r-exper r-primer) unit)
  (lambda (g x env te tail r-exp r-prim)
    (tagcase x
      (e-bloblet (sop fi args got a b abk)
        (begin (r-bloblet-op g (symbol->string sop) (if (< fi 0) (r-datum-operand got a b abk) fi)
                             args env te r-exp r-prim)
               (r-done g tail)))
      (else y (r-decline)))))
(define r-bloblet-op (subr rcompiles (rgen string int exps renv cenv r-exper r-primer) unit)
(lambda (g op i args env te r-exp r-prim)
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
               ;; At a literal offset, in line (`prim2imm`).
               (("blobref-at")
                (begin
                  (tagcase (car (cdr args))
                    (e-int (k a b abk)
                      (if (and (>= k 0) (< k 67108864))
                          (r-prim g "%suffix-ref" (r-args-2 (a-e (car args)) (a-v (wcell-int k)))
                                  env te)
                          (r-prim g "%suffix-ref" all env te)))
                    (else y (r-prim g "%suffix-ref" all env te)))
                  (r-fits g i)))
               (("blobref+") (begin (r-prim g "%suffix-ref+" all env te) (r-fits g i)))
               (("blobref-owner") (r-prim g "%suffix-ref-owner" all env te))
               (("blobref-offset") (r-prim g "%suffix-ref-offset" all env te))
               (("blobref-get")
                (if (< i 0)
                    (r-decline)
                    (r-prim g "%fx26-suffix-ref-get"
                            (r-args-2 (a-e (car args)) (a-v (wcell-int i))) env te)))
               (("blobref-length")
                (if (< i 0)
                    (r-decline)
                    (r-prim g "%fx26-suffix-ref-length"
                            (r-args-2 (a-e (car args)) (a-v (wcell-int i))) env te)))
               (("blobref-index" "blobref-set!" "blobref-variant!")
                (if (< i 0)
                    (r-decline)
                    (r-prim3 g (case op (("blobref-index") "%fx26-blobref-index")
                                        (("blobref-set!") "%fx26-suffix-ref-set!")
                                        (else "%fx26-flat-variant!"))
                             (car args) (wcell-int i) (car (cdr args)) env te r-exp)))
               (else (r-decline))))))


;; Runtime primitive `name` declined if there is none; else, if it never
;; collects and its operands are a value and a constant, in line
;; (`prim2imm`), or a value alone (`prim1`), as `Compiler::r_prim` does:
;; whether it was any of these.
(define r-prim-imm (subr rcompiles (rgen string rargs renv cenv r-exper) bool)
  (lambda (g name args env te r-exp)
    (let ((p (runtime-primitive name)) (n (r-count-args args)))
      (cond ((< p 0) (begin (r-decline) #t))
            ((not (r-never-collects? name)) #f)
            ((= n 1)
             (and (r-arg-loaded g (r-nth-arg args 0) env te r-exp)
                  (begin (r-opn g rop-prim1 p) #t)))
            ((not (= n 2)) #f)
            (else
             (tagcase (r-nth-arg args 1)
               (a-v (v)
                 (and (r-arg-loaded g (r-nth-arg args 0) env te r-exp)
                      (begin (r-op2 g rop-prim2imm (wcell-int p) v) #t)))
               (else y #f)))))))
;; Operand `a` into RESULT, if an expression or a frame slot: whether it was.
(define r-arg-loaded (subr rcompiles (rgen rarg renv cenv r-exper) bool)
  (lambda (g a env te r-exp)
    (tagcase a
      (a-e (x) (begin (r-exp g x env te #f) #t))
      (a-slot (s) (begin (r-opn g rop-stack s) #t))
      (else y #f))))
;; The operand of what the checker found the operation `a` `b` `k` takes,
;; holding `got` if it is a form kept to be inlined (`k-datum-operand`).
(define r-datum-operand
  (subr (maxeff (read @globals) (read @k) (alloc @k)) (k-datums int int int) int)
  (lambda (got a b k) (k-datum-operand (c-datum-of got a b k))))
;; `(extract p l)`, `x`, by what the checker found it takes: a field of a
;; product; or a blobref to its field at its offset; declined if the
;; checker did not see it.
(define r-extract (subr rcompiles (rgen exp renv cenv bool r-exper r-primer) unit)
  (lambda (g x env te tail r-exp r-prim)
    (tagcase x
      (e-extract (p l got a b abk)
        (let ((d (c-datum-of got a b abk)))
          (if (null? d)
              (r-decline)
              (tagcase (car d)
                (datum-field (i)
                  (begin (r-exp g p env te #f) (r-opn g rop-field (+ i 2)) (r-done g tail)))
                (datum-blobref-field (o)
                  (begin (r-prim g "%suffix-ref+" (r-args-2 (a-e p) (a-v (wcell-int o))) env te)
                         (r-done g tail)))
                (else y (r-decline))))))
      (else y (r-decline)))))
;; A `tagcase` on a blobref to a flat sum, of layout code `k`
;; (`Compiler::r_flat_tagcase`): the blobref and its tag, a label, kept in
;; places (registers in a leaf); each arm's name a blobref to its variant,
;; `k / 256` bytes along; no arm for the tag a failure. No call-outs.
(define r-flat-tagcase
  (subr rcompiles (rgen int exp exp-arms exp-let-bs renv cenv bool r-exper r-primer) unit)
  (lambda (g k s arms els env te tail r-exp r-prim)
    (let ((regs (get (extract g nreg))) (slots (get (extract g nslot))))
      (begin
        (let* ((sc (r-scrutinee-place g s env te r-exp))
               (tag (begin (r-imm-prim g "%fx26-flat-tag" (wcell-int k)) (r-place-value g)))
               (end (r-new-label g)))
          (begin
            (r-flat-arms g k arms sc tag end regs slots env te tail r-exp)
            (if (null? els)
                (begin (r-get g tag) (r-opn g rop-prim1 (runtime-primitive "%fx26-flat-no-arm"))
                       (r-done g tail))
                (let ((n (extract (car els) 1)))
                  (r-exp g (extract (car els) 2) (r-bind n sc env) (r-local te n) tail)))
            (r-emit g (r-label end))))
        (r-restore g regs slots)))))
(define r-flat-arms
  (subr rcompiles (rgen int exp-arms rloc rloc int int int renv cenv bool r-exper) unit)
  (lambda (g k arms sc tag end regs0 slots0 env te tail r-exp)
    (if (null? arms)
        #u
        (let* ((arm (car arms)) (next (r-new-label g)))
          (begin
            (r-get g tag)
            (r-op2imm g routine-eq (c-flat-label (extract arm 1) k))
            (r-emit g (r-branch #t next))
            (let ((regs (get (extract g nreg))) (slots (get (extract g nslot))))
              (begin
                (r-get g sc)
                (r-imm-prim g "%suffix-ref+" (wcell-int (quotient k 256)))
                ;; The arm's ref where the blobref and its tag were: neither
                ;; is used past here on this path (`Compiler::r_flat_tagcase`).
                (r-restore g regs0 slots0)
                (let* ((x (car (extract arm 3))) (at (r-place-value g)))
                  (r-exp g (extract arm 4) (r-bind x at env) (r-local te x) tail))
                (r-restore g regs slots)))
            (if tail #u (r-emit g (r-branch #f end)))
            (r-emit g (r-label next))
            (r-flat-arms g k (cdr arms) sc tag end regs0 slots0 env te tail r-exp))))))
;; Argument `i` of a loop (`r-self-temps`), `x`, kept: where it is already
;; if it is the parameter itself, unchanged (no move then); else its value
;; kept as `r-place-value` keeps it.
(define r-self-temp (subr rcompiles (rgen exp int renv cenv r-exper) rloc)
  (lambda (g x i env te r-exp)
    (let ((v (r-plain-var-loc env x)) (leaf (extract g leaf)))
      (if (and (not (null? v))
               (tagcase (car v) (rl-reg (r) (and leaf (= r (+ i 1))))
                 (rl-slot (n) (and (not leaf) (= n i))) (else y #f)))
          (car v)
          (begin (r-exp g x env te #f) (r-place-value g))))))
;; `s`'s value into RESULT, and where it is kept: where it is already, if
;; a variable in a register or the frame; else a place of its own.
(define r-scrutinee-place (subr rcompiles (rgen exp renv cenv r-exper) rloc)
  (lambda (g s env te r-exp)
    (let ((v (r-plain-var-loc env s)))
      (if (and (not (null? v))
               (tagcase (car v) (rl-reg (r) #t) (rl-slot (n) #t) (else y #f)))
          (begin (r-get g (car v)) (car v))
          (begin (r-exp g s env te #f) (r-place-value g))))))
;; RESULT := runtime primitive `name`, one that never collects, of `a`'s
;; value, constant `x` and `b`'s (`prim3imm`), as `Compiler::r_prim3`: `a`
;; kept in its place while `b` is made into a register of its own.
(define r-prim3 (subr rcompiles (rgen string exp wcell exp renv cenv r-exper) unit)
  (lambda (g name a x b env te r-exp)
    (let ((regs (get (extract g nreg))) (slots (get (extract g nslot))))
      (begin
        (r-exp g a env te #f)
        (let* ((at (r-place-value g))
               (k (begin (r-exp g b env te #f) (r-reg g))))
          (begin (r-opn g rop-setreg k)
                 (r-get g at)
                 (r-op2 g rop-prim3imm (wcell-int (runtime-primitive name)) x)
                 (r-emit g (r-cell (wcell-int k)))))
        (r-restore g regs slots)))))
;; A new blobref's flat's `size` bytes checked in the suffix, in line
;; (`Checker::note_fits`); declined where the checker noted none.
(define r-fits (subr rcompiles (rgen int) unit)
  (lambda (g size)
    (cond ((< size 0) (r-decline))
          ((> size 1) (r-imm-prim g "%fx26-suffix-fits" (wcell-int size)))
          (else #u))))
;; RESULT := runtime primitive `name`, one that never collects, of RESULT
;; and constant `v` (`prim2imm`).
(define r-imm-prim (subr rcompiles (rgen string wcell) unit)
  (lambda (g name v) (r-op2 g rop-prim2imm (wcell-int (runtime-primitive name)) v)))
)))
