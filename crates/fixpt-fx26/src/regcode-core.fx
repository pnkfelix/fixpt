;;; Register code, in FX-26: the expressions' compiler proper, one
;;; recursive group. After `regcode-exps.fx`.

;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define regcode-core-module (module
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
              ((not (null? r)) ((get r-reshape-code) g x (car r) env te tail))
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
              (r-exp g th env te tail)
              (if tail #u (r-emit g (r-branch #f end)))
              (r-emit g (r-label no))
              (r-exp g el env te tail)
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
        (e-module (items a b) ((get r-module-code) g x env te tail))
        (e-with (m body a b) ((get r-module-code) g x env te tail)))))))
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
        (cond ((string=? op "bloblet-ref")
               (begin (r-exp g (car args) env te #f) (r-opn g rop-field (+ i 2))))
              ((string=? op "make-bloblet") (r-prim g "%make-bloblet" all env te))
              ((string=? op "rmake-bloblet") (r-prim g "%region-make-bloblet" all env te))
              ((string=? op "bloblet-set!")
               (let* ((field (a-v (wcell-int (+ i 2))))
                      (ops (r-args-3 (a-e (car args)) field (a-e (car (cdr args))))))
                 (begin (r-prim g "%bloblet-set!" ops env te) (r-unit g))))
              ((string=? op "bloblet-byte") (r-prim g "%bloblet-byte" all env te))
              ((string=? op "bloblet-set-byte!")
               (begin (r-prim g "%bloblet-set-byte!" all env te) (r-unit g)))
              ((string=? op "bloblet-bytes") (r-prim g "%bloblet-bytes" all env te))
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
               (let* ((sp (car (get c-spec-now))) (cell (extract sp 2)) (word (extract sp 3)))
                 (r-self-guarded g cell word (get r-spec-start) f args env te tail)))
              ;; A top-level procedure calling itself through its global, its
              ;; own name not an inlined body's, which may name an older global.
              ((not (null? (r-own-self env f args)))
               (let ((o (car (get r-own-now))) (cell (car (r-own-self env f args))))
                 (r-self-guarded g cell (extract o 2) (extract o 4) f args env te tail)))
              (else
               (let ((name (r-standard-name env f)))
                 (if (string=? name "")
                     (r-call g f args a b env te tail)
                     (cond ((and tail (and (string=? name "with-mark") (= n 3)))
                            (r-withmark-tail g args env te))
                           ((and (string=? name "apply") (= n 2))
                            (r-apply g args env te tail (not (c-apply-shares-at a b))))
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
              ((not (null? (r-inline-of a b env f n)))
               (if (and (not (get r-assuming)) (extract g leaf))
                   (r-decline)
                   (let ((i (car (r-inline-of a b env f n))))
                     (r-inline g (car i) (cdr i) f args env te tail))))
              ((extract g leaf)
               (if (and tail
                        (and (< n register-regs)
                             (and (null? (r-special-of a b env f args)) (< (r-lifted-at env f) 0))))
                   ((get r-leaf-call) g f args env te)
                   (r-decline)))
              ((not (null? (r-special-of a b env f args)))
               (let ((i (car (r-special-of a b env f args))))
                 (r-specialize g (extract i 1) (extract i 2) (extract i 3) args env te tail)))
              ;; A lifted procedure's call: the names it would have captured,
              ;; then the arguments, into REG1…REGn; its closure, a constant.
              ((>= (r-lifted-at env f) 0)
               (let* ((k (r-lifted-at env f))
                      (all (r-name-args (c-lift-added k) (r-exp-args args)))
                      (m (r-count-args all)))
                 (begin
                   (r-args g all env te (the maybe-exp nil))
                   (r-op1 g rop-const (r-lifted-closure k))
                   (r-invoke g m tail))))
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
        (let ((assumed (r-assume cell (extract i 2))))
          (begin
            (if assumed #u (r-guard g cell (extract i 2) call))
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
                 (k (r-known env a))
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
                 (arg (cond ((not (null? k)) (a-v (r-const-cell (car k))))
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
          (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
                 (spec (r-spec-of sp cell lps lbody te))
                 ;; Named for the procedure and the lambda.
                 (made (r-spec-word sp spec lbody))
                 (s (r-slot g))
                 (n (c-count-exps args)))
            (begin
              (r-op2 g rop-lambda (wcell-word (extract made 1)) (wcell-int 0))
              (r-opn g rop-setstk s)
              (r-exp-args-into g args env te)
              (let* ((call (r-new-label g)) (end (r-new-label g)))
                (if (r-assume cell (extract sp 2))
                    (begin (r-opn g rop-stack s) (r-invoke g n tail))
                    (begin
                      (r-guard g cell (extract sp 2) call)
                      (r-opn g rop-stack s)
                      (r-invoke g n tail)
                      (if tail #u (r-emit g (r-branch #f end)))
                      (r-emit g (r-label call))
                      (r-op1 g rop-global (wcell-global cell))
                      (r-invoke g n tail)
                      (r-emit g (r-label end)))))
              (r-restore g regs slots))))
        (else y (r-decline)))))
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
  ;; passed as itself): the arguments made; then, if the global still holds
  ;; a closure of `word` (its own, or the one the copy was made from), this
  ;; procedure again, by its own entry, or in tail position a loop back to
  ;; `start`; else the global.
  (r-self-guarded (subr rcompiles (rgen wglobal tword int exp exps renv cenv bool) unit)
    (lambda (g cell word start f args env te tail)
      (let ((n (c-count-exps args)))
        ;; In a fast version, a call in tail position is a loop, in a leaf too.
        (if (and (extract g leaf) (or (not (and tail (get r-assuming))) (> n register-regs)))
            (r-decline)
            (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
                   (call (r-new-label g)) (end (r-new-label g)))
              (begin
                (if tail
                    (let* ((made (r-self-temps g args env te)) (assumed (r-assume cell word)))
                      (begin
                        (if assumed #u (r-guard g cell word call))
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
                      (if (r-assume cell word)
                          (r-opn g rop-invokeself n)
                          (begin
                            (r-guard g cell word call)
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
      (cond ((string=? what "array-ref")
             (begin
               (r-exp-args-into g args env te)
               (r-index-field g)
               (r-opnn g rop-cellular routine-field-ref 2)))
            ((string=? what "array-set!")
             (let ((p (runtime-primitive "%bloblet-set!")))
               (begin
                 (r-exp-args-into g args env te)
                 (r-index-field g)
                 (r-opnn g rop-prim p 3)
                 (r-unit g))))
            ((string=? what "array-length")
             (begin (r-prim g "%bloblet-fields" (r-exp-args args) env te)
                    (r-add-imm g -1)))
            ((string=? what "make-array")
             (let ((ops (r-args-3 (a-v (wcell-int 0)) (a-e (car args)) (a-e (car (cdr args))))))
               (r-prim g "%make-bloblet-filled" ops env te)))
            ((string=? what "make-box")
             (r-prim g "%make-box" (the rargs (cons (a-v (wcell-unit)) nil)) env te))
            ;; The runtime's, which refuses a pair not to be written; then
            ;; unit.
            ((or (string=? what "set-car!") (string=? what "set-cdr!"))
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
        (r-lambda g ps lbody (extract own 1) (extract own 2) self region #f)))))))

(define r-exp (with regcode-core-module r-exp))
(define r-exp-as-is (with regcode-core-module r-exp-as-is))
(define r-make-frozen (with regcode-core-module r-make-frozen))
(define r-apply (with regcode-core-module r-apply))
(define r-call (with regcode-core-module r-call))
(define r-inline (with regcode-core-module r-inline))
(define r-specialize (with regcode-core-module r-specialize))
(define r-self-guarded (with regcode-core-module r-self-guarded))
(define r-operands (with regcode-core-module r-operands))
(define r-into (with regcode-core-module r-into))
(define r-args (with regcode-core-module r-args))
(define r-list (with regcode-core-module r-list))
(define r-lambda (with regcode-core-module r-lambda))
