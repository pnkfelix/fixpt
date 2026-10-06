;;; Register code, in FX-26: helpers of the compiler proper,
;;; `regcode-core.fx`. `regcode.fx` first (PLAN.md 13h′).

;;; ------------------------------------------- helpers of the compiler proper

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define regcode-helpers-module (module
;; An expression, or none: a call's procedure (`r-args`), a closure's
;; region (`r-lambda`).
(define-type maybe-exp (listof exp @k))
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
;; The copy's word's name: the procedure's and the lambda's.
(define r-spec-name (subr rcompiles (c-special exp) (listof string @k))
  (lambda (sp lbody)
    (the (listof string @k)
      (cons (string-append (symbol->string (extract sp 1))
                           (string-append "@lambda@" (c-place-name (exp-start lbody))))
            nil))))
;; A lambda's word, and the names it captures.
(define-type rmade (productof (1 tword) (2 syms)))
;; The copy `spec` of `sp`'s procedure, for lambda body `lbody`, compiled
;; apart: what this body assumes is not its; in the globals `sp` saw.
(define r-spec-word (subr rcompiles (c-special c-spec exp) rmade)
  (lambda (sp spec lbody)
    (let ((outer-spec (get c-spec-now)) (outer-genv (get c-genv))
          (outer-assuming (get r-assuming)) (outer-assumed (get r-assumed)))
      (begin
        (set r-assuming #f)
        (set r-assumed (the r-assumptions nil))
        (set c-spec-now (the (listof c-spec @k) (cons spec nil)))
        (set c-genv (extract sp 5))
        (set c-word-name (r-spec-name sp lbody))
        (let ((made (c-lambda-word (extract sp 3) (extract sp 4) (the cenv nil) (the syms nil))))
          (begin (set c-spec-now outer-spec) (set c-genv outer-genv)
                 (set r-assuming outer-assuming) (set r-assumed outer-assumed)
                 made))))))
;; The word lambda `ps` `body` compiles to: made already (`c-made-word`),
;; or now (`c-lambda-word`).
(define r-made-word (subr rcompiles (exp-params exp cenv syms) rmade)
  (lambda (ps body te own)
    (let ((m (c-made-word ps body te own)))
      (if (null? m) (c-lambda-word ps body te own) (car m)))))
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
(define r-literal? (with regcode-helpers-module r-literal?))
(define r-free-operand? (with regcode-helpers-module r-free-operand?))
(define r-deeper? (with regcode-helpers-module r-deeper?))
(define r-lifted-closure (with regcode-helpers-module r-lifted-closure))
(define r-unknowing (with regcode-helpers-module r-unknowing))
(define r-spec-of (with regcode-helpers-module r-spec-of))
(define r-spec-word (with regcode-helpers-module r-spec-word))
(define r-made-word (with regcode-helpers-module r-made-word))
(define r-free-into-regs (with regcode-helpers-module r-free-into-regs))
(define r-collects-here? (with regcode-helpers-module r-collects-here?))
(define r-spec-body-collects? (with regcode-helpers-module r-spec-body-collects?))
(define-type roperands (select regcode-helpers-module roperands))
(define r-imm-operand (with regcode-helpers-module r-imm-operand))
(define r-reg-operand (with regcode-helpers-module r-reg-operand))
(define r-known-cell (with regcode-helpers-module r-known-cell))
