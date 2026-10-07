;;; Register code, in FX-26: helpers of the compiler proper,
;;; `regcode-core.fx`. `regcode.fx` first (PLAN.md 13h′).

;;; ------------------------------------------- helpers of the compiler proper

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define regcode-helpers-module (module
;; An expression, or none: a call's procedure (`r-args`), a closure's
;; region (`r-lambda`).
(define-type maybe-exp (listof exp @k))
;; A call unrolled over a constant list (`r-unrolled`, as the Rust
;; compiler's `r_unroll`, `TODO.md` §44): its procedure's expression, each
;; argument that is a global holding a constant list, with it (one that is
;; a constant here `r-known` finds), and the globals to guard. `r-inline`
;; compiles it, reading these (`r-known-arg`,
;; `r-guards-for`); newest first, as a call's arguments may hold others.
(define-type r-unroll-known (listof (pairof exp rconst @k) @k))
(define-type r-wglobals (listof wglobal @k))
(define-type r-unroll-found (productof (1 r-unroll-known) (2 r-wglobals) (3 bool)))
(define-type r-unroll-hook (productof (1 exp) (2 r-unroll-known) (3 r-wglobals)))
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
;; The global `a` names and its constant, if it is one.
(define-type r-unroll-globals (listof (pairof wglobal rconst @k) @k))
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
;; An expression split as `core + k` (`r-split`), and such a split, if any.
(define-type rsplit (productof (1 (listof exp @k)) (2 int)))
(define-type rsplits (listof rsplit @k))
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
;; A lambda's word, and the names it captures.
(define-type rmade (productof (1 tword) (2 syms)))
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

;; What `r-operands` makes of its second operand: an immediate, or the
;; register it is in, in a list.
(define-type roperands (productof (1 wcells) (2 (listof int @k))))
(define r-imm-operand (subr (alloc @k) (wcells) roperands)
  (lambda (v) (product (1 v) (2 (the (listof int @k) nil)))))
(define r-reg-operand (subr (alloc @k) (int) roperands)
  (lambda (k) (product (1 (the wcells nil)) (2 (the (listof int @k) (cons k nil))))))
;; `x`'s cell, in a list, if it is a constant (`r-known`).
(define r-known-cell (subr rbuilds (renv exp) wcells)
  (lambda (env x)
    (let ((k (r-known env x)))
      (if (null? k) nil (the wcells (cons (r-const-cell (car k)) nil))))))))

(define-type maybe-exp (select regcode-helpers-module maybe-exp))
(define r-just-exp (with regcode-helpers-module r-just-exp))
(define r-args-2 (with regcode-helpers-module r-args-2))
(define r-args-3 (with regcode-helpers-module r-args-3))
(define r-const-value (with regcode-helpers-module r-const-value))
(define r-unit (with regcode-helpers-module r-unit))
(define r-op2imm (with regcode-helpers-module r-op2imm))
(define r-add-imm (with regcode-helpers-module r-add-imm))
(define r-negate (with regcode-helpers-module r-negate))
(define r-index-field (with regcode-helpers-module r-index-field))
(define r-restore (with regcode-helpers-module r-restore))
(define r-var-value (with regcode-helpers-module r-var-value))
(define r-fx-value (with regcode-helpers-module r-fx-value))
(define r-literal? (with regcode-helpers-module r-literal?))
(define r-free-operand? (with regcode-helpers-module r-free-operand?))
(define r-deeper? (with regcode-helpers-module r-deeper?))
(define r-lifted-closure (with regcode-helpers-module r-lifted-closure))
(define r-unknowing (with regcode-helpers-module r-unknowing))
(define r-spec-of (with regcode-helpers-module r-spec-of))
(define r-spec-word (with regcode-helpers-module r-spec-word))
(define r-free-into-regs (with regcode-helpers-module r-free-into-regs))
(define r-collects-here? (with regcode-helpers-module r-collects-here?))
(define r-spec-body-collects? (with regcode-helpers-module r-spec-body-collects?))
(define-type roperands (select regcode-helpers-module roperands))
(define r-imm-operand (with regcode-helpers-module r-imm-operand))
(define r-reg-operand (with regcode-helpers-module r-reg-operand))
(define r-known-cell (with regcode-helpers-module r-known-cell))
(define r-known-arg (with regcode-helpers-module r-known-arg))
(define r-known-slow (with regcode-helpers-module r-known-slow))
(define r-const-list? (with regcode-helpers-module r-const-list?))
(define r-guards-for (with regcode-helpers-module r-guards-for))
(define r-inline-or-unroll (with regcode-helpers-module r-inline-or-unroll))
(define r-knowing (with regcode-helpers-module r-knowing))
(define-type rsplits (select regcode-helpers-module rsplits))
(define r-split-app (with regcode-helpers-module r-split-app))
(define r-identity-arg (with regcode-helpers-module r-identity-arg))
(define r-lifted-call-args (with regcode-helpers-module r-lifted-call-args))
