;;; Register code, in FX-26: the expressions' compiler proper, one
;;; recursive group. After `regcode-exps.fx`.

(define-rec
  ;; `x`'s value into RESULT; in tail position, returned. A procedure
  ;; converted to a convention is made, then given to `%fx26-convert` with
  ;; what it is converted to.
  (r-exp (subr (maxeff compiles spin) (rgen exp renv cenv bool) unit)
    (lambda (g x env te tail)
      (let ((k (c-conversion-at x)))
        (if (< k 0)
            (r-exp-as-is g x env te tail)
            (begin
              (r-prim g "%fx26-convert" (the rargs (cons (a-as-is x) (cons (a-v (wcell-int k)) nil))) env te)
              (r-done g tail))))))
  ;; `x`'s value into RESULT; in tail position, returned.
  (r-exp-as-is (subr (maxeff compiles spin) (rgen exp renv cenv bool) unit)
    (lambda (g x env te tail)
      (let ((k (r-known env x)))
        (if (not (null? k))
            (begin (r-op1 g rop-const (r-const-cell (car k))) (r-done g tail))
      (tagcase x
        (e-var (n a b)
          (let ((l (r-where env n)))
            (begin
              (if (null? l)
                  (if (string=? (symbol->string n) "nil") (r-op1 g rop-const (wcell-nil)) (r-standard-value g (symbol->string n) tail))
                  (tagcase (car l)
                    (rl-reg (k) (r-opn g rop-reg k))
                    (rl-slot (s) (r-opn g rop-stack s))
                    (rl-free (i) (r-opn g rop-lexical i))
                    (rl-global (c) (r-op1 g rop-global (wcell-global c)))
                    (else y (r-decline))))
              (r-done g tail))))
        (e-int (n a b) (begin (r-op1 g rop-const (wcell-int n)) (r-done g tail)))
        (e-bool (v a b) (begin (r-op1 g rop-const (wcell-bool v)) (r-done g tail)))
        (e-char (v a b) (begin (r-op1 g rop-const (wcell-char v)) (r-done g tail)))
        (e-str (s a b) (begin (r-op1 g rop-const (wcell-string s)) (r-done g tail)))
        (e-sym (s a b) (begin (r-op1 g rop-const (wcell-symbol s)) (r-done g tail)))
        (e-unit (a b) (begin (r-op1 g rop-const (wcell-unit)) (r-done g tail)))
        (e-plambda (d body a b) (r-exp g body env te tail))
        (e-proj (body ds a b) (r-exp g body env te tail))
        (e-the (d body a b) (r-exp g body env te tail))
        (e-convention (cnv body a b) (r-exp g body env te tail))
        ;; The region's name bound, as a `let`'s, to a region entered (never
        ;; in a leaf), and left with the body's value, which is so not in
        ;; tail position.
        (e-letregion (k r i body a b)
          (if (or (= k 0) (= k 3)) (r-exp g body env te tail)
          (if (extract g leaf)
              (r-decline)
              (let ((regs (get (extract g nreg))) (slots (get (extract g nslot))))
                (begin
                  (r-prim g (if (= k 1) "%region-enter" "%reap-enter") (the rargs nil) env te)
                  (let ((h (r-slot g)))
                    (begin
                      (r-opn g rop-setstk h)
                      (r-exp g body (the renv (cons (cons r (rl-slot h)) env)) (r-local te r) #f)
                      (let ((v (r-slot g)))
                        (begin
                          (r-opn g rop-setstk v)
                          (r-prim g "%region-exit" (the rargs (cons (a-slot h) (cons (a-slot v) nil))) env te)
                          (r-done g tail)))))
                  (set (extract g nreg) regs)
                  (set (extract g nslot) slots))))))
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
          (if (null? es) (begin (r-op1 g rop-const (wcell-unit)) (r-done g tail)) (r-begin g es env te tail)))
        (e-let (bs body a b) (r-let g bs body env te tail))
        (e-extract (p l a b)
          (let ((i (c-field-at a b)))
            (if (< i 0)
                (r-decline)
                (begin (r-exp g p env te #f) (r-opn g rop-field (+ i 2)) (r-done g tail)))))
        (e-lambda (ps body a b) (begin (r-lambda g ps body env te (the syms nil) (the (listof exp @k) nil) tail) (r-done g tail)))
        (e-rlambda (r l a b)
          (tagcase l
            (e-lambda (ps body la lb)
              (begin (r-lambda g ps body env te (the syms nil) (the (listof exp @k) (cons r nil)) #f) (r-done g tail)))
            (else y (r-decline))))
        (e-sum (t v a b)
          (begin
            (r-prim g "%make-frozen" (the rargs (cons (a-v (wcell-int 36)) (cons (a-v (wcell-symbol t)) (cons (a-e v) nil)))) env te)
            (r-done g tail)))
        (e-product (fs a b)
          (begin
            (r-prim g "%make-frozen" (the rargs (cons (a-v (wcell-int 37)) (r-field-args fs))) env te)
            (r-done g tail)))
        (e-bloblet (op i args a b) (begin (r-bloblet g (symbol->string op) i args env te) (r-done g tail)))
        (e-prompt (t body h a b)
          (begin
            (r-call-out g rop-cellular routine-prompt (the rargs (cons (a-e t) (cons (a-e h) (cons (a-thunk body) nil)))) env te)
            (r-done g tail)))
        (e-tagcase (s arms els a b) (r-tagcase g s arms els env te tail))
        (e-letrec (bs body a b)
          (let ((ks (r-lifted a b)))
            (if (not (null? ks))
                ;; Lifted as its stack code lifted it (`c-lift`).
                (r-exp g body (r-bind-lifted bs (car ks) env) (c-bind-lifted bs (car ks) te) tail)
                ;; A leaf makes no closure; join points it may have.
                (if (and (extract g leaf) (not (r-all? (r-join-flags bs body tail)))) (r-decline) (r-letrec g bs body env te tail)))))
        ;; A lambda applied at once: a `let` (`c-applied-let`).
        (e-app (f args a b)
          (let ((l (c-applied-let f args)))
            (if (null? l) (r-app g f args env te tail) (r-let g (extract (car l) 1) (extract (car l) 2) env te tail)))))))))
  ;; Code that goes to `label` if `x` is `when` (true: anything but #f), and
  ;; on if not: a test as jumps. `and` and `or` (`if`s, as the parser makes
  ;; them), `not` and constants make no boolean, and are tested no more than
  ;; once.
  (r-branch-on (subr (maxeff compiles spin) (rgen exp bool int renv cenv) unit)
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
            ((not (null? tc))
             (let ((skip (r-new-label g)))
               (begin (r-branch-on g t #t skip env te) (r-branch-on g el when label env te) (r-emit g (r-label skip)))))
            ;; `(if a t K)`: `and`'s shape.
            ((and (not (null? ec)) (r-holds? ec when))
             (begin (r-branch-on g t #f label env te) (r-branch-on g th when label env te)))
            ((not (null? ec))
             (let ((skip (r-new-label g)))
               (begin (r-branch-on g t #f skip env te) (r-branch-on g th when label env te) (r-emit g (r-label skip)))))
            (else
             (let ((no (r-new-label g)) (end (r-new-label g)))
               (begin (r-branch-on g t #f no env te) (r-branch-on g th when label env te)
                      (r-emit g (r-branch #f end)) (r-emit g (r-label no))
                      (r-branch-on g el when label env te) (r-emit g (r-label end))))))))
      (else y (r-branch-plain g x when label env te)))))
  ;; The same for a test that is not `not` or an `if`: a constant decided
  ;; now, anything else made and branched on.
  (r-branch-plain (subr (maxeff compiles spin) (rgen exp bool int renv cenv) unit)
  (lambda (g x when label env te)
    (let ((k (r-known env x)))
      (if (not (null? k))
          (if (r-holds? k when) (r-emit g (r-branch #f label)) #u)
          (begin (r-exp g x env te #f) (r-emit g (if when (r-brancht label) (r-branch #t label))))))))
  (r-begin (subr (maxeff compiles spin) (rgen (listof exp acyclic) renv cenv bool) unit)
    (lambda (g es env te tail)
      (if (null? (cdr es))
          (r-exp g (car es) env te tail)
          (begin (r-exp g (car es) env te #f) (r-begin g (cdr es) env te tail)))))
  ;; Each binding's value made, in the scope outside, and put where it
  ;; lives: a register in a leaf, else a frame slot. In order.
  (r-let-bind (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 exp)) acyclic) renv cenv (listof bool acyclic)) renv)
    (lambda (g bs env te flags)
      (if (null? bs)
          nil
          (let* ((k (r-known env (extract (car bs) 2)))
                 ;; A constant is bound as itself.
                 (l (if (null? k)
                        (begin (r-exp g (extract (car bs) 2) env te #f) (r-keep g (car flags)))
                        (rl-const (car k)))))
            (cons (cons (extract (car bs) 1) l) (r-let-bind g (cdr bs) env te (cdr flags)))))))
  (r-bloblet (subr (maxeff compiles spin) (rgen string int (listof exp acyclic) renv cenv) unit)
    (lambda (g op i args env te)
      (cond ((string=? op "bloblet-ref")
             (begin (r-exp g (car args) env te #f) (r-opn g rop-field (+ i 2))))
            ((string=? op "make-bloblet") (r-prim g "%make-bloblet" (r-exp-args args) env te))
            ((string=? op "rmake-bloblet") (r-prim g "%region-make-bloblet" (r-exp-args args) env te))
            ((string=? op "bloblet-set!")
             (begin
               (r-prim g "%bloblet-set!"
                       (the rargs (cons (a-e (car args)) (cons (a-v (wcell-int (+ i 2))) (cons (a-e (car (cdr args))) nil))))
                       env te)
               (r-op1 g rop-const (wcell-unit))))
            ((string=? op "bloblet-byte") (r-prim g "%bloblet-byte" (r-exp-args args) env te))
            ((string=? op "bloblet-set-byte!")
             (begin (r-prim g "%bloblet-set-byte!" (r-exp-args args) env te) (r-op1 g rop-const (wcell-unit))))
            ((string=? op "bloblet-bytes") (r-prim g "%bloblet-bytes" (r-exp-args args) env te))
            (else (r-decline)))))
  ;;; ---------------------------------------------------------- applications
  (r-app (subr (maxeff compiles spin) (rgen exp (listof exp acyclic) renv cenv bool) unit)
    (lambda (g f args env te tail)
      (let ((n (c-count-exps args)))
        (cond ((not (null? (r-join-of env f))) (r-jump g (car (r-join-of env f)) args env te tail))
              ((and tail (r-self-known? g f n te)) (r-loop g args env te))
              ;; In a procedure specialized at a lambda: the lambda called,
              ;; or the procedure calling itself.
              ((and (r-spec-param? env f) (= n (extract (car (get c-spec-now)) 7))) (r-spec-lambda g args env te tail))
              ((r-spec-self? env f args)
               (let ((sp (car (get c-spec-now))))
                 (r-self-guarded g (extract sp 2) (extract sp 3) (get r-spec-start) f args env te tail)))
              ;; A top-level procedure calling itself through its global, its
              ;; own name not an inlined body's, which may name an older global.
              ((not (null? (r-own-self env f args)))
               (let ((o (car (get r-own-now))))
                 (r-self-guarded g (car (r-own-self env f args)) (extract o 2) (extract o 4) f args env te tail)))
              (else
               (let ((name (r-standard-name env f)))
                 (if (string=? name "")
                     (r-call g f args env te tail)
                     (if (and tail (and (string=? name "with-mark") (= n 3)))
                         (r-withmark-tail g args env te)
                         (begin (r-standard-app g name args env te tail) (r-done g tail))))))))))
  (r-standard-app (subr (maxeff compiles spin) (rgen string (listof exp acyclic) renv cenv bool) unit)
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
                 (split (if (and (or (string=? name "+") (string=? name "-")) (or (r-adds? env x) (r-adds? env y)))
                            (r-split-app env name args)
                            (the (listof (productof (1 (listof exp @k)) (2 int)) @k) nil)))
                 (core (if (null? split) (the (listof exp @k) nil) (extract (car split) 1)))
                 ;; (Asked only where it can matter, and a literal first:
                 ;; what is known is looked up, and that costs.)
                 (literal (tagcase x (e-int (n a b) #t) (e-bool (v a b) #t) (e-char (v a b) #t) (else z #f)))
                 (free-x (and swap (or (r-simple? x) (not (null? (r-known env x))))))
                 (free-y (and swap (and (not free-x) (or (r-simple? y) (not (null? (r-known env y))))))))
            (begin
              (cond ((and (not (null? core)) (and (not (r-same-exp? (car core) x)) (not (r-same-exp? (car core) y))))
                     (let ((k (extract (car split) 2)))
                       (begin
                         (r-exp g (car core) env te #f)
                         (cond ((> k 0) (r-op2 g rop-op2imm (wcell-int routine-int-add) (wcell-int k)))
                               ((< k 0) (r-op2 g rop-op2imm (wcell-int routine-int-sub) (wcell-int (- 0 k))))
                               (else #u)))))
                    ((and swap (and (not free-x) (not free-y))) (r-binary-swapped g r x y env te))
                    ((or swap (and (or (= r routine-int-add) (= r routine-eq)) (and literal (null? (r-known env y)))))
                     (r-binary g r y x env te))
                    (else (r-binary g r x y env te)))
              (if negate (r-op2 g rop-op2imm (wcell-int routine-eq) (wcell-bool #f)) #u))))
        (s-op1 (r) (begin (r-exp g (car args) env te #f) (r-opn g rop-op1 r)))
        (s-op2imm (r v) (begin (r-exp g (car args) env te #f) (r-op2 g rop-op2imm (wcell-int r) v)))
        (s-field (k) (begin (r-exp g (car args) env te #f) (r-opn g rop-field k)))
        (s-prim (p) (r-call-out g rop-prim p (r-exp-args args) env te))
        ;; (A mark in tail position is `r-withmark-tail`'s.)
        (s-cellular (r) (r-call-out g rop-cellular r (r-exp-args args) env te))
        (s-identity () (r-exp g (car args) env te #f))
        (s-set ()
          (let ((k (extract (r-operands g (car args) (car (cdr args)) env te #f) 2)))
            (if (null? k)
                (r-decline)
                (begin (r-opnn g rop-setfield 2 (car k)) (r-op1 g rop-const (wcell-unit))))))
        (s-special (what) (r-special g what args env te))
        (s-none () (r-decline)))))
  ;; In tail position a mark replaces this frame's, as stack code's
  ;; `withmark-tail` does: the arguments made, the frame left, and the
  ;; call-out, which calls the thunk as a tail call.
  (r-withmark-tail (subr (maxeff compiles spin) (rgen (listof exp acyclic) renv cenv) unit)
    (lambda (g args env te)
      (begin
        (r-args g (r-exp-args args) env te (the (listof exp @k) nil))
        (r-leave g)
        (r-opnn g rop-cellular routine-withmark-tail 3)
      ;; Never reached (the call-out goes on in the thunk): register code
      ;; ends each path so.
      (r-op0 g rop-return))))
  ;; A call: the arguments into REG1…REGn, the procedure in RESULT.
  (r-call (subr (maxeff compiles spin) (rgen exp (listof exp acyclic) renv cenv bool) unit)
    (lambda (g f args env te tail)
      (let ((n (c-count-exps args)))
        (cond ;; An inlined call: in a fast version, no call, so in a leaf too.
              ((not (null? (r-inlined env f n)))
               (if (and (not (get r-assuming)) (extract g leaf))
                   (r-decline)
                   (let ((i (car (r-inlined env f n)))) (r-inline g (car i) (cdr i) f args env te tail))))
              ((extract g leaf) (r-decline))
              ((not (null? (r-specialized env f args)))
               (let ((i (car (r-specialized env f args)))) (r-specialize g (extract i 1) (extract i 2) (extract i 3) args env te tail)))
              ;; A lifted procedure's call: the names it would have captured,
              ;; then the arguments, into REG1…REGn; its closure, a constant.
              ((>= (r-lifted-at env f) 0)
               (let* ((k (r-lifted-at env f))
                      (all (r-name-args (c-lift-added k) (r-exp-args args)))
                      (m (r-count-args all)))
                 (begin
                   (r-args g all env te (the (listof exp @k) nil))
                   (r-op1 g rop-const (extract (table-ref (get c-lifts) k (the c-lift (product (1 (wcell-nil)) (2 (the syms nil))))) 1))
                   (if tail
                       (begin (r-leave g) (r-opn g rop-tailinvoke m))
                       (r-opn g rop-invoke m)))))
              ;; A call of the procedure itself, not in tail position: by its
              ;; own entry, with no closure fetched.
              ((and (not tail) (r-self-known? g f n te))
               (begin (r-args g (r-exp-args args) env te (the (listof exp @k) nil)) (r-opn g rop-invokeself n)))
              (else
               (begin
                 (r-args g (r-exp-args args) env te (the (listof exp @k) (cons f nil)))
                 (if tail
                     (begin (r-leave g) (r-opn g rop-tailinvoke n))
                     (r-opn g rop-invoke n))))))))
  ;; A call of a small global procedure, inlined: the arguments made and
  ;; kept (one that is a variable in the frame or the closure is used where
  ;; it is); then, if the global still holds a closure of the word the body
  ;; was compiled to, the body, in a scope of its own where the parameters
  ;; are the arguments and the globals those it saw; else the call. A
  ;; redefinition makes a new closure, of a new word: the call.
  (r-inline (subr (maxeff compiles spin) (rgen c-inline wglobal exp (listof exp acyclic) renv cenv bool) unit)
    (lambda (g i cell f args env te tail)
      (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
             (bound (r-inline-args g (extract i 3) args env te))
             (call (r-new-label g)) (end (r-new-label g))
             (outer-genv (get c-genv)) (outer-inlining (get c-inlining))
             (n (c-count-exps args))
             ;; The procedure running is not known in the body.
             (h (the rgen (product (items (extract g items)) (leaf (extract g leaf)) (nreg (extract g nreg)) (nslot (extract g nslot))
                                   (mslot (extract g mslot)) (labels (extract g labels)) (this (the (listof c-this @k) nil))
                                   (start (extract g start))))))
        (let ((assumed (r-assume cell (extract i 2))))
          (begin
            (if assumed #u (r-guard g cell (extract i 2) call))
            (set c-genv (extract i 5))
            (set c-inlining (cons (extract i 1) outer-inlining))
            (r-exp h (extract i 4) (extract bound 1) (extract bound 2) tail)
            (set c-inlining outer-inlining)
            (set c-genv outer-genv)
            (if assumed
                #u
                (begin
                  (if tail #u (r-emit g (r-branch #f end)))
                  (r-emit g (r-label call))
                  (r-args g (extract bound 3) env te (the (listof exp @k) (cons f nil)))
                  (if tail
                      (begin (r-leave g) (r-opn g rop-tailinvoke n))
                      (r-opn g rop-invoke n))
                  (r-emit g (r-label end))))
            (set (extract g nreg) regs)
            (set (extract g nslot) slots))))))
  ;; Each parameter bound to its argument, in order: where the body finds
  ;; them, as the body's cellular scope has them, and as the call's
  ;; arguments.
  (r-inline-args
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syns-a)) acyclic) (listof exp acyclic) renv cenv)
          (productof (1 renv) (2 cenv) (3 rargs)))
    (lambda (g ps args env te)
      (if (or (null? ps) (null? args))
          (product (1 (the renv nil)) (2 (the cenv nil)) (3 (the rargs nil)))
          (let* ((p (extract (car ps) 1)) (a (car args))
                 (k (r-known env a))
                 (l (if (null? k) (tagcase a (e-var (n x y) (r-where env n)) (else y (the (listof rloc @k) nil))) (the (listof rloc @k) (cons (rl-const (car k)) nil))))
                 (kept (if (null? l)
                           (the (listof rloc @k) nil)
                           (tagcase (car l)
                             (rl-slot (s) l)
                             (rl-free (j) l)
                             (rl-const (c) l)
                             ;; In a fast version, where no call comes after
                             ;; to clobber it.
                             (rl-reg (r) (if (get r-assuming) l (the (listof rloc @k) nil)))
                             (else y (the (listof rloc @k) nil)))))
                 (here (if (null? kept)
                           (begin (r-exp g a env te #f) (r-keep g (extract g leaf)))
                           (car kept)))
                 (arg (cond ((not (null? k)) (a-v (r-const-cell (car k))))
                            ((null? kept) (tagcase here (rl-slot (s) (a-slot s)) (else y (a-e a))))
                            (else (a-e a))))
                 (rest (r-inline-args g (cdr ps) (cdr args) env te)))
            (product (1 (the renv (cons (cons p here) (extract rest 1))))
                     (2 (r-local (extract rest 2) p))
                     (3 (the rargs (cons arg (extract rest 3)))))))))
  ;; A call of a global procedure with a lambda at a parameter it only
  ;; calls: a copy of the procedure made for the lambda (`c-spec`), whose
  ;; closure is made first; then the arguments, the lambda's closure among
  ;; them; then, if the global still holds a closure of the word the copy
  ;; was made from, the copy called, else the global.
  (r-specialize (subr (maxeff compiles spin) (rgen c-special wglobal exp (listof exp acyclic) renv cenv bool) unit)
    (lambda (g sp cell lam args env te tail)
      (tagcase lam
        (e-lambda (lps lbody la lb)
          (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
                 (spec (the c-spec
                         (product (1 (extract sp 1)) (2 cell) (3 (extract sp 2)) (4 (extract sp 6))
                                  (5 (r-nth-param (extract sp 3) (extract sp 6))) (6 (c-count-params (extract sp 3)))
                                  (7 (extract sp 7)) (8 lps) (9 lbody)
                                  (10 (c-lambda-captured lps lbody te)) (11 (c-genv-now)))))
                 (outer-spec (get c-spec-now)) (outer-genv (get c-genv))
                 ;; The copy compiled apart: what this body assumes is not its.
                 (outer-assuming (get r-assuming)) (outer-assumed (get r-assumed))
                 (made (begin
                         (set r-assuming #f)
                         (set r-assumed (the r-assumptions nil))
                         (set c-spec-now (the (listof c-spec @k) (cons spec nil)))
                         (set c-genv (extract sp 5))
                         ;; Named for the procedure and the lambda.
                         (set c-word-name
                              (the (listof string @k)
                                (cons (string-append (symbol->string (extract sp 1))
                                                     (string-append "@lambda@" (int->string (exp-start lbody))))
                                      nil)))
                         (c-lambda-word (extract sp 3) (extract sp 4) (the cenv nil) (the syms nil))))
                 (s (begin (set c-spec-now outer-spec) (set c-genv outer-genv)
                           (set r-assuming outer-assuming) (set r-assumed outer-assumed)
                           (r-slot g)))
                 (n (c-count-exps args)))
            (begin
              (r-op2 g rop-lambda (wcell-word (extract made 1)) (wcell-int 0))
              (r-opn g rop-setstk s)
              (r-args g (r-exp-args args) env te (the (listof exp @k) nil))
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
              (set (extract g nreg) regs)
              (set (extract g nslot) slots))))
        (else y (r-decline)))))
  ;; In a procedure specialized at a lambda, a call of the parameter the
  ;; lambda is: the lambda's body, its parameters bound to the arguments and
  ;; the values its closure captured to those fields of the parameter's
  ;; value, where the globals are those it saw.
  (r-spec-lambda (subr (maxeff compiles spin) (rgen (listof exp acyclic) renv cenv bool) unit)
    (lambda (g args env te tail)
      (let* ((sp (car (get c-spec-now))) (at (car (get r-spec-at)))
             (regs (get (extract g nreg))) (slots (get (extract g nslot)))
             (outer-genv (get c-genv))
             ;; The body as it is compiled: in the globals the lambda saw.
             (body-collects
              (begin (set c-genv (extract sp 11))
                     (let ((c (and (not (extract g leaf))
                                   (r-collects (extract sp 9) (r-local-syms (r-local-params (the cenv nil) (extract sp 8)) (extract sp 10))
                                               (the (listof c-this @k) nil) tail))))
                       (begin (set c-genv outer-genv) c))))
             (flags (r-in-regs g args (c-length (extract sp 10)) te body-collects))
             (bound (r-spec-args g (extract sp 8) args env te flags))
             (all (r-spec-free g at (extract sp 10) 0 (extract bound 1) (extract bound 2) (r-drop-bools flags (c-count-exps args))))
             (outer (get c-genv)))
        (begin
          (set c-genv (extract sp 11))
          (r-exp g (extract sp 9) (extract all 1) (extract all 2) tail)
          (set c-genv outer)
          (set (extract g nreg) regs)
          (set (extract g nslot) slots)))))
  ;; Each of the lambda's parameters bound to its argument, made and kept,
  ;; in order.
  (r-spec-args
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syns-a)) acyclic) (listof exp acyclic) renv cenv (listof bool acyclic))
          (productof (1 renv) (2 cenv)))
    (lambda (g ps args env te flags)
      (if (or (null? ps) (null? args))
          (product (1 (the renv nil)) (2 (the cenv nil)))
          (let* ((p (extract (car ps) 1))
                 (k (r-known env (car args)))
                 (l (if (null? k) (begin (r-exp g (car args) env te #f) (r-keep g (car flags))) (rl-const (car k))))
                 (rest (r-spec-args g (cdr ps) (cdr args) env te (cdr flags))))
            (product (1 (the renv (cons (cons p l) (extract rest 1)))) (2 (r-local (extract rest 2) p)))))))
  ;; A procedure calling itself through its global `cell` (a top-level
  ;; definition's, or, in a copy specialized at a lambda, with the parameter
  ;; passed as itself): the arguments made; then, if the global still holds
  ;; a closure of `word` (its own, or the one the copy was made from), this
  ;; procedure again, by its own entry, or in tail position a loop back to
  ;; `start`; else the global.
  (r-self-guarded (subr (maxeff compiles spin) (rgen wglobal tword int exp (listof exp acyclic) renv cenv bool) unit)
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
                              (r-args g (r-slot-args-of made) env te (the (listof exp @k) (cons f nil)))
                              (r-invoke g n #t)))))
                    (begin
                      (r-args g (r-exp-args args) env te (the (listof exp @k) nil))
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
                (set (extract g nreg) regs)
                (set (extract g nslot) slots)))))))
  ;; Each argument kept, in a register in a leaf, else a frame slot, in
  ;; order: where each is.
  (r-self-temps (subr (maxeff compiles spin) (rgen (listof exp acyclic) renv cenv) (listof rloc @k))
    (lambda (g args env te)
      (if (null? args)
          nil
          (let* ((l (begin (r-exp g (car args) env te #f) (r-keep g (extract g leaf))))
                 (rest (r-self-temps g (cdr args) env te)))
            (cons l rest)))))
  ;; RESULT := r(a, b), `a` evaluated first; a constant `b` an immediate.
  (r-binary (subr (maxeff compiles spin) (rgen int exp exp renv cenv) unit)
    (lambda (g r a b env te)
      (let ((o (r-operands g a b env te #t)))
        (cond ((not (null? (extract o 1))) (r-op2 g rop-op2imm (wcell-int r) (car (extract o 1))))
              ((not (null? (extract o 2))) (r-opnn g rop-op2 r (car (extract o 2))))
              (else (r-decline))))))
  ;; RESULT := r(y, x), `x` evaluated first, as written: for an operation
  ;; whose operands trade places, where they may not run in the other
  ;; order. `x` is kept in a register, or the frame if `y` calls.
  (r-binary-swapped (subr (maxeff compiles spin) (rgen int exp exp renv cenv) unit)
    (lambda (g r x y env te)
      (let ((regs (get (extract g nreg))) (slots (get (extract g nslot))))
        (begin
          (r-exp g x env te #f)
          (let* ((collects (and (not (extract g leaf)) (r-collects y te (extract g this) #f)))
                 (k (r-reg g)))
            (begin
              (if collects
                  (let ((s (r-slot g)))
                    (begin (r-opn g rop-setstk s) (r-exp g y env te #f) (r-opnn g rop-load k s)))
                  (begin (r-opn g rop-setreg k) (r-exp g y env te #f)))
              (r-opnn g rop-op2 r k)))
          (set (extract g nreg) regs) (set (extract g nslot) slots)))))
  ;; `a` into RESULT and `b` into a register, `a` evaluated first; or, if
  ;; `imm` and `b` is a constant, `b` as an immediate. The register is free
  ;; again after: use it at once.
  (r-operands (subr (maxeff compiles spin) (rgen exp exp renv cenv bool) (productof (1 (listof wcell @k)) (2 (listof int @k))))
    (lambda (g a b env te imm)
      (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
             (v (if imm
                    (let ((k (r-known env b))) (if (null? k) (the (listof wcell @k) nil) (the (listof wcell @k) (cons (r-const-cell (car k)) nil))))
                    (the (listof wcell @k) nil)))
             (bl (tagcase b (e-var (n x y) (r-where env n)) (else z (the (listof rloc @k) nil))))
             (breg (if (null? bl) -1 (tagcase (car bl) (rl-reg (k) k) (else z -1))))
             (out
              (cond
                ((not (null? v)) (begin (r-exp g a env te #f) (product (1 v) (2 (the (listof int @k) nil)))))
                ((>= breg 0) (begin (r-exp g a env te #f) (product (1 (the (listof wcell @k) nil)) (2 (the (listof int @k) (cons breg nil))))))
                ;; `b` first (`a` has no effect, and sees none), made before
                ;; its register is taken: a chain of operations nested in
                ;; their second operands then needs one register, not one a
                ;; level.
                ((r-simple? a)
                 (let ((k (if (r-simple? b)
                              (let ((k (r-reg g))) (begin (r-into g b k env te) k))
                              (begin (r-exp g b env te #f) (let ((k (r-reg g))) (begin (r-opn g rop-setreg k) k))))))
                   (begin (r-exp g a env te #f)
                          (product (1 (the (listof wcell @k) nil)) (2 (the (listof int @k) (cons k nil)))))))
                (else
                 (begin
                   (r-exp g a env te #f)
                   (let* ((collects (and (not (extract g leaf)) (r-collects b te (extract g this) #f)))
                          (kept (if collects
                                    (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) (rl-slot s)))
                                    (let ((t (r-reg g))) (begin (r-opn g rop-setreg t) (rl-reg t)))))
                          (k (r-reg g)))
                     (begin
                       (r-into g b k env te)
                       (tagcase kept (rl-slot (s) (r-opn g rop-stack s)) (rl-reg (t) (r-opn g rop-reg t)) (else z #u))
                       (product (1 (the (listof wcell @k) nil)) (2 (the (listof int @k) (cons k nil)))))))))))
        (begin (set (extract g nreg) regs) (set (extract g nslot) slots) out))))
  ;; `x`'s value into REGk: straight from a register or the frame when it is
  ;; a variable there, else by way of RESULT.
  (r-into (subr (maxeff compiles spin) (rgen exp int renv cenv) unit)
    (lambda (g x k env te)
      (let ((l (tagcase x (e-var (n a b) (if (< (c-conversion-at x) 0) (r-where env n) (the (listof rloc @k) nil))) (else y (the (listof rloc @k) nil)))))
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
  (r-args (subr (maxeff compiles spin) (rgen rargs renv cenv (listof exp @k)) unit)
    (lambda (g args env te f)
      (if (extract g leaf)
          (r-decline)
          (let* ((n (r-count-args args))
                 (many (> n register-regs))
                 (slots (get (extract g nslot)))
                 ;; The last argument that is not simple goes straight to its
                 ;; register, when the procedure is simple too.
                 (direct (if (or many (and (not (null? f)) (not (r-simple? (car f))))) -1 (r-last-hard args 0 -1)))
                 (kept (r-args-hard g args 0 direct env te many))
                 (fun (if (and (not (null? f)) (not (r-simple? (car f))))
                          (begin (r-exp g (car f) env te #f) (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) s)))
                          -1)))
            (begin
              (if many
                  (begin
                    (r-op1 g rop-const (wcell-nil))
                    (r-args-list g args kept (- n 1) env te)
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
  (r-args-hard (subr (maxeff compiles spin) (rgen rargs int int renv cenv bool) (listof int @k))
    (lambda (g args i direct env te many)
      (if (null? args)
          nil
          (if (r-arg-simple-here? (car args) env many)
              (cons -1 (r-args-hard g (cdr args) (+ i 1) direct env te many))
              (begin
                (tagcase (car args)
                  (a-e (x) (r-exp g x env te #f))
                  (a-as-is (x) (r-exp-as-is g x env te #f))
                  (a-thunk (body)
                    (begin (r-lambda g (the (listof (productof (1 symbol) (2 syns-a)) acyclic) nil) body env te
                                     (the syms nil) (the (listof exp @k) nil) #f)
                           #u))
                  (a-name (n) (r-name g n env))
                  (else y #u))
                (let ((k (if (= i direct)
                             (begin (r-opn g rop-setreg (+ i 1)) -2)
                             (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) s)))))
                  (cons k (r-args-hard g (cdr args) (+ i 1) direct env te many))))))))
  ;; The arguments from the `i`th, short of the `stop`th, each into its
  ;; register.
  (r-args-into (subr (maxeff compiles spin) (rgen rargs (listof int @k) int int renv cenv) unit)
    (lambda (g args kept i stop env te)
      (if (or (null? args) (= i stop))
          #u
          (begin
            (r-arg-into g (car args) (car kept) (+ i 1) env te)
            (r-args-into g (cdr args) (cdr kept) (+ i 1) stop env te)))))
  ;; Argument `a` into REGk: from the frame slot it was kept in, if it was
  ;; (-2: in its register already), else made there.
  (r-arg-into (subr (maxeff compiles spin) (rgen rarg int int renv cenv) unit)
    (lambda (g a kept k env te)
      (cond ((= kept -2) #u)
            ((>= kept 0) (r-opnn g rop-load k kept))
            (else
             (tagcase a
               (a-e (x) (r-into g x k env te))
               (a-v (v) (begin (r-op1 g rop-const v) (r-opn g rop-setreg k)))
               (a-slot (s) (r-opnn g rop-load k s))
               (a-lexical (j) (begin (r-opn g rop-lexical j) (r-opn g rop-setreg k)))
               (a-thunk (b) #u)
               (a-as-is (x) #u)
               (a-name (n)
                 (let ((l (r-where env n)))
                   (if (null? l)
                       (r-decline)
                       (tagcase (car l)
                         (rl-slot (s) (r-opnn g rop-load k s))
                         (rl-reg (r) (if (= r k) #u (r-opnn g rop-movereg r k)))
                         (rl-free (j) (begin (r-opn g rop-lexical j) (r-opn g rop-setreg k)))
                         (rl-const (c) (begin (r-op1 g rop-const (r-const-cell c)) (r-opn g rop-setreg k)))
                         (else y (r-decline)))))))))))
  ;; The list of the arguments from the `i`th down to the eighth, onto the
  ;; list in RESULT, by `cons`.
  (r-args-list (subr (maxeff compiles spin) (rgen rargs (listof int @k) int renv cenv) unit)
    (lambda (g args kept i env te)
      (if (< i (- register-regs 1))
          #u
          (begin
            (r-opn g rop-setreg 2)
            (r-arg-into g (r-nth-arg args i) (r-nth-int kept i) 1 env te)
            (r-opnn g rop-cellular routine-cons 2)
            (r-args-list g args kept (- i 1) env te)))))
  ;; A call-out, `prim p n` or `cellular r n`, on `args` in REG1…REGn.
  (r-call-out (subr (maxeff compiles spin) (rgen int int rargs renv cenv) unit)
    (lambda (g how what args env te)
      (begin (r-args g args env te (the (listof exp @k) nil)) (r-opnn g how what (r-count-args args)))))
  (r-prim (subr (maxeff compiles spin) (rgen string rargs renv cenv) unit)
    (lambda (g name args env te)
      (let ((p (runtime-primitive name))) (if (< p 0) (r-decline) (r-call-out g rop-prim p args env te)))))
  ;; A closure of a lambda into RESULT, its free values into REG1…REGn first;
  ;; `own` as for `c-lambda-word`. With a `region` (an `rlambda`'s, one or
  ;; none), the closure is made there, by `%region-closure h fv … w`. What it
  ;; gives: for each sibling not made yet (a `letrec`'s), the free value's
  ;; index and the sibling's frame slot.
  ;; A leaf makes a closure only as its value, in tail position (`tail`): its
  ;; call-out, where the free space has no room, may collect, and then
  ;; nothing but the closure is used after.
  (r-lambda (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syns-a)) acyclic) exp renv cenv syms (listof exp @k) bool) patches)
    (lambda (g ps body env te own region tail)
      (if (and (extract g leaf) (not (and tail (null? region))))
          (begin (r-decline) (the patches nil))
          (let* ((made (let ((m (c-made-word ps body te own))) (if (null? m) (c-lambda-word ps body te own) (car m)))) (w (extract made 1)) (fv (extract made 2)) (n (c-length fv)))
            (if (null? region)
                ;; Past `register-regs`, the rest a list, as a call's
                ;; arguments are (`r-args`).
                (if (> n register-regs)
                    (let ((pa (r-free-args fv env 0)))
                      (begin (r-args g (extract pa 1) env te (the (listof exp @k) nil))
                             (r-op2 g rop-lambda (wcell-word w) (wcell-int n))
                             (extract pa 2)))
                    (let ((patches (begin (r-par-moves g (r-reg-moves fv env 0)) (r-free-regs g fv env 0))))
                      (begin (r-op2 g rop-lambda (wcell-word w) (wcell-int n)) patches)))
                (let* ((pa (r-free-args fv env 0)))
                  (begin
                    (r-prim g "%region-closure"
                            (the rargs (cons (a-e (car region)) (r-append-arg (extract pa 1) (a-v (wcell-word w)))))
                            env te)
                    (extract pa 2))))))))
  ;; Arrays, and the tag and key makers: as the stack compiler does them.
  (r-special (subr (maxeff compiles spin) (rgen string (listof exp acyclic) renv cenv) unit)
    (lambda (g what args env te)
      (cond ((string=? what "array-ref")
             (begin
               (r-args g (r-exp-args args) env te (the (listof exp @k) nil))
               (r-opn g rop-reg 2) (r-op2 g rop-op2imm (wcell-int routine-int-add) (wcell-int 2)) (r-opn g rop-setreg 2)
               (r-opnn g rop-cellular routine-field-ref 2)))
            ((string=? what "array-set!")
             (let ((p (runtime-primitive "%bloblet-set!")))
               (begin
                 (r-args g (r-exp-args args) env te (the (listof exp @k) nil))
                 (r-opn g rop-reg 2) (r-op2 g rop-op2imm (wcell-int routine-int-add) (wcell-int 2)) (r-opn g rop-setreg 2)
                 (r-opnn g rop-prim p 3)
                 (r-op1 g rop-const (wcell-unit)))))
            ((string=? what "array-length")
             (begin (r-prim g "%bloblet-fields" (r-exp-args args) env te)
                    (r-op2 g rop-op2imm (wcell-int routine-int-sub) (wcell-int 1))))
            ((string=? what "make-array")
             (r-prim g "%make-bloblet-filled"
                     (the rargs (cons (a-v (wcell-int 0)) (cons (a-e (car args)) (cons (a-e (car (cdr args))) nil)))) env te))
            ((string=? what "make-box")
             (r-prim g "%make-box" (the rargs (cons (a-v (wcell-unit)) nil)) env te))
            ;; The runtime's, which refuses a pair not to be written; then
            ;; unit.
            ((or (string=? what "set-car!") (string=? what "set-cdr!"))
             (begin (r-prim g what (r-exp-args args) env te) (r-op1 g rop-const (wcell-unit))))
            (else (r-decline)))))
  ;; `tagcase`: the scrutinee kept; each arm's tag compared, the last's not
  ;; when there is no `else` (a checked program covers every tag); the value,
  ;; or its product's members, bound.
  (r-tagcase
    (subr (maxeff compiles spin) (rgen exp (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) (listof (productof (1 symbol) (2 exp)) acyclic) renv cenv bool) unit)
    (lambda (g s arms els env te tail)
      (let ((regs (get (extract g nreg))) (slots (get (extract g nslot))))
        (begin
          (r-exp g s env te #f)
          (let* ((sc (r-place-value g)) (end (r-new-label g)))
            (begin
              (r-arms g arms (null? els) sc end env te tail)
              (if (null? els)
                  #u
                  (r-exp g (extract (car els) 2) (the renv (cons (cons (extract (car els) 1) sc) env))
                         (r-local te (extract (car els) 1)) tail))
              (r-emit g (r-label end))))
          (set (extract g nreg) regs)
          (set (extract g nslot) slots)))))
  (r-arms
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) bool rloc int renv cenv bool) unit)
    (lambda (g arms no-else sc end env te tail)
      (if (null? arms)
          #u
          (let* ((arm (car arms)) (last (and no-else (null? (cdr arms)))) (next (r-new-label g))
                 (regs (get (extract g nreg))) (slots (get (extract g nslot))))
            (begin
              (if last
                  #u
                  (begin (r-get g sc) (r-opn g rop-field 2)
                         (r-op2 g rop-op2imm (wcell-int routine-eq) (wcell-symbol (extract arm 1)))
                         (r-emit g (r-branch #t next))))
              (let ((bound (if (extract arm 2)
                               (r-members g sc (extract arm 3) 0 (the renv nil))
                               (begin (r-get g sc) (r-opn g rop-field 3)
                                      (the renv (cons (cons (car (extract arm 3)) (r-place-value g)) nil))))))
                (r-exp g (extract arm 4) (r-bind-all (r-reverse-env bound nil) env) (r-local-all (r-reverse-env bound nil) te) tail))
              (set (extract g nreg) regs)
              (set (extract g nslot) slots)
              (if tail #u (r-emit g (r-branch #f end)))
              (r-emit g (r-label next))
              (r-arms g (cdr arms) no-else sc end env te tail))))))
  ;; A tail call of the procedure itself: the new arguments made, then put
  ;; where the parameters are, and back to the start.
  (r-loop (subr (maxeff compiles spin) (rgen (listof exp acyclic) renv cenv) unit)
    (lambda (g args env te)
      (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot))) (made (r-loop-make g args env te)))
        (begin
          (r-loop-move g made 0)
          (r-emit g (r-branch #f (extract g start)))
          (set (extract g nreg) regs)
          (set (extract g nslot) slots)))))
  (r-loop-make (subr (maxeff compiles spin) (rgen (listof exp acyclic) renv cenv) (listof int @k))
    (lambda (g args env te)
      (if (null? args)
          nil
          (begin
            (r-exp g (car args) env te #f)
            (let ((m (if (extract g leaf)
                         (let ((r (r-reg g))) (begin (r-opn g rop-setreg r) r))
                         (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) s)))))
              (cons m (r-loop-make g (cdr args) env te)))))))
  ;; `letrec`: each closure made into its slot, a placeholder for a sibling
  ;; not made yet; then each placeholder patched.
  (r-letrec (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp renv cenv bool) unit)
    (lambda (g bs body env te tail)
      (let* ((slots (get (extract g nslot))) (regs (get (extract g nreg)))
             (joins (r-join-flags bs body tail))
             ;; A slot for each closure (a join point is none).
             (at (r-letrec-slots-j g joins))
             (patches (r-letrec-make g bs bs at 0 env te joins))
             ;; Each join point's parameters' places, and its label.
             (places (begin (r-letrec-patch g patches at) (r-join-places g bs joins (r-letrec-te-j bs joins te))))
             (env2 (r-letrec-env-j bs at places env))
             (te2 (r-letrec-te-j bs joins te)))
        (begin
          (r-exp g body env2 te2 tail)
          (r-join-bodies g bs places env2 te2 tail)
          (set (extract g nslot) slots)
          (set (extract g nreg) regs)))))
  ;; A `let`: each value made, in the scope outside, and kept in a register
  ;; where no call comes before the body is done with it (else the frame).
  (r-let (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 exp)) acyclic) exp renv cenv bool) unit)
  (lambda (g bs body env te tail)
    (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
           (body-collects (and (not (extract g leaf)) (r-collects body (r-local-names te bs) (extract g this) tail)))
           (flags (r-in-regs g (r-let-inits bs) 0 te body-collects)))
      (let ((bound (r-let-bind g bs env te flags)))
        (begin
          (r-exp g body (r-bind-all bound env) (r-local-all bound te) tail)
          (set (extract g nreg) regs)
          (set (extract g nslot) slots))))))
  ;; A join point's call: each argument made and kept (a register in a
  ;; leaf, else a frame slot), then each into its parameter's place, and a
  ;; jump.
  (r-jump (subr (maxeff compiles spin) (rgen rloc (listof exp acyclic) renv cenv bool) unit)
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
                  (set (extract g nreg) regs)
                  (set (extract g nslot) slots)))))
        (else y (r-decline)))))
  (r-jump-args (subr (maxeff compiles spin) (rgen (listof exp acyclic) renv cenv (listof bool acyclic)) (listof rloc @k))
    (lambda (g args env te flags)
      (if (null? args)
          nil
          (let* ((l (begin (r-exp g (car args) env te #f) (r-keep g (car flags))))
                 (rest (r-jump-args g (cdr args) env te (cdr flags))))
            (cons l rest)))))
  ;; Each join point's body, after the `letrec`'s, which ends every path
  ;; itself: where its calls go.
  (r-join-bodies
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof (listof (pairof (listof rloc @k) int @k) @k) @k) renv cenv bool) unit)
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
                        (r-exp g lbody (r-bind-places env ps (car p)) (r-local-params te ps) tail))))
                  (else y (r-decline))))
            (r-join-bodies g (cdr bs) (cdr places) env te tail)))))
  (r-letrec-make
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof int @k) int renv cenv (listof bool acyclic))
          (listof patches @k))
    (lambda (g all bs at i env te joins)
      (cond
        ((null? bs) nil)
        ;; A join point is no closure.
        ((car joins) (cons (the patches nil) (r-letrec-make g all (cdr bs) at (+ i 1) env te (cdr joins))))
        (else
          (let* ((lam (c-lambda-of (extract (car bs) 3)))
                 (name (extract (car bs) 1))
                 (p (tagcase (car lam)
                      (e-lambda (ps lbody a b)
                        (r-letrec-one g all at i name ps lbody (the (listof exp @k) nil) env te))
                      (e-rlambda (r l a b)
                        (tagcase l
                          (e-lambda (ps lbody la lb) (r-letrec-one g all at i name ps lbody (the (listof exp @k) (cons r nil)) env te))
                          (else y (begin (r-decline) (the patches nil)))))
                      (else y (begin (r-decline) (the patches nil))))))
            (begin
              (r-opn g rop-setstk (r-nth-int at i))
              (cons p (r-letrec-make g all (cdr bs) at (+ i 1) env te (cdr joins)))))))))
  (r-letrec-one
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof int @k) int symbol
                   (listof (productof (1 symbol) (2 syns-a)) acyclic) exp (listof exp @k) renv cenv)
          patches)
    (lambda (g all at i name ps lbody region env te)
      (let* ((n (c-count-params ps))
             (own (r-sibling-env all at i 0 lbody n env te)))
        (r-lambda g ps lbody (extract own 1) (extract own 2) (the syms (cons name nil)) region #f)))))
