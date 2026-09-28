;;; Register code for a lambda, in FX-26 (PLAN.md 13h′ (e)): what the Rust
;;; compiler's `cellular/regcode.rs` makes, instruction for instruction, as
;;; the lambda's word's twin: the MacScheme machine's instructions
;;; (`layout::regcode`, the `rop-` numbers), made from the same trees.
;;;
;;; A leaf (a procedure that neither calls nor calls out, loops aside) keeps
;;; its parameters, its `let`s and its temporaries in registers; any other
;;; keeps its parameters and `let`s in a frame made on entry, since a call or
;;; a call-out may collect, and then only the frame holds values. What this
;;; compiler does not do, it declines, and the lambda keeps its stack code
;;; alone: it notes that it declined (`r-declined`) and goes on, making
;;; nothing anyone keeps, where the Rust compiler returns `None`.
;;;
;;; `compile.fx` calls it through `c-register-code`, which this sets.

;;; ---------------------------------------------------------------- items

(define-datatype ritem
  (r-cell wcell)
  (r-label int)
  ;; `branch` (#f) or `branchf` (#t) to a label.
  (r-branch bool int)
  ;; The frame's size, known when the body is done.
  (r-frame)
  ;; `global-guard g w` to a label: unless global cell `g` holds a closure
  ;; made from word `w`.
  (r-guard-to wcell wcell int))

;; Where a variable is, to register code.
;; A constant that needs no allocation, as register code may know one.
(define-datatype rconst (rc-int int) (rc-bool bool) (rc-char char) (rc-nil))

(define-datatype rloc
  (rl-reg int)
  (rl-slot int)
  (rl-free int)
  (rl-global wglobal)
  (rl-loop)
  ;; A `letrec` sibling not made yet, to be in this frame slot.
  (rl-pending int)
  ;; A constant, bound to the name (`r-known`): no place at all.
  (rl-const rconst)
  ;; A `letrec`-bound procedure only called in tail position, a join point
  ;; (`r-join-ok?`): where its parameters are, and its label.
  (rl-join (listof rloc @k) int))
(define-type renv (listof (pairof symbol rloc @k) @k))

;; An operand of a call-out: an expression, a constant, a procedure of no
;; arguments whose body is an expression (a `prompt`'s), a frame slot's
;; value, or a free value of the closure running.
(define-datatype rarg (a-e exp) (a-v wcell) (a-thunk exp) (a-slot int) (a-lexical int))
(define-type rargs (listof rarg @k))

;; A standard operation, as register code does it.
(define-datatype rstd
  ;; `op2 r`, operands in order, or swapped; then `not`, if asked.
  (s-op2 int bool bool)
  (s-op1 int)
  (s-op2imm int wcell)
  (s-field int)
  ;; A call-out: a runtime primitive, or a cellular routine.
  (s-prim int)
  (s-cellular int)
  ;; Its argument itself (`%fx26-identity`).
  (s-identity)
  ;; A reference written: `setfield 2`, then unit.
  (s-set)
  ;; Arrays, the tag and key makers: several instructions.
  (s-special string)
  (s-none))

;; What is being made: the items, newest first; whether a leaf; the next
;; register and frame slot, and the most slots used; the labels; and, for a
;; procedure that knows itself, what it knows and its start's label.
(define-type rgen
  (productof (items (ref (listof ritem @k) @k)) (leaf bool) (nreg (ref int @k)) (nslot (ref int @k))
             (mslot (ref int @k)) (labels (ref int @k)) (this (listof c-this @k)) (start int)))

;; Whether the register code being made has been declined.
(define r-declined (ref bool @k) (new #f))
(define r-decline (subr (maxeff (read @globals) (write @k)) () unit) (lambda () (set r-declined #t)))

(define r-emit (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen ritem) unit)
  (lambda (g i) (let ((items (extract g items))) (set items (cons i (get items))))))
(define r-op0 (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (rgen int) unit)
  (lambda (g op) (r-emit g (r-cell (wcell-int op)))))
(define r-op1 (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (rgen int wcell) unit)
  (lambda (g op x) (begin (r-op0 g op) (r-emit g (r-cell x)))))
(define r-op2 (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (rgen int wcell wcell) unit)
  (lambda (g op x y) (begin (r-op1 g op x) (r-emit g (r-cell y)))))
(define r-opn (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (rgen int int) unit)
  (lambda (g op n) (r-op1 g op (wcell-int n))))
(define r-opnn (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (rgen int int int) unit)
  (lambda (g op n m) (r-op2 g op (wcell-int n) (wcell-int m))))
(define r-new-label (subr (maxeff (read @k) (write @k)) (rgen) int)
  (lambda (g) (let* ((l (extract g labels)) (n (get l))) (begin (set l (+ n 1)) n))))
(define r-reg (subr (maxeff (read @globals) (read @k) (write @k)) (rgen) int)
  (lambda (g)
    (let* ((r (extract g nreg)) (n (+ (get r) 1)))
      (begin (set r n) (if (> n register-regs) (r-decline) #u) n))))
(define r-slot (subr (maxeff (read @k) (write @k)) (rgen) int)
  (lambda (g)
    (let* ((s (extract g nslot)) (n (get s)) (m (extract g mslot)))
      (begin (set s (+ n 1)) (if (> (+ n 1) (get m)) (set m (+ n 1)) #u) n))))
;; Pop the frame, if there is one, before leaving.
(define r-leave (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (rgen) unit)
  (lambda (g) (if (extract g leaf) #u (begin (r-op0 g rop-pop) (r-emit g (r-frame))))))
(define r-done (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (rgen bool) unit)
  (lambda (g tail) (if tail (begin (r-leave g) (r-op0 g rop-return)) #u)))

(define r-reverse (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof ritem @k) (listof ritem @k)) (listof ritem @k))
  (lambda (xs acc) (if (null? xs) acc (r-reverse (cdr xs) (cons (car xs) acc)))))
(define r-size (subr pure (ritem) int)
  (lambda (i) (tagcase i (r-cell (x) 1) (r-label (n) 0) (r-branch (f n) 2) (r-frame () 1) (r-guard-to (c w n) 4))))
(define r-place (subr (maxeff (read @globals) (read @k) (write @k) spin) ((listof ritem @k) (arrayof int @k) int) int)
  (lambda (xs at pos)
    (if (null? xs)
        pos
        (begin (tagcase (car xs) (r-label (n) (array-set! at n pos)) (else x #u))
               (r-place (cdr xs) at (+ pos (r-size (car xs))))))))
;; The cells, branches resolved (an offset counts from the cell after it),
;; and the frame's size in place: from the items newest first, each ending
;; at `end`, onto those after it, in a loop, however long the code.
(define r-cells (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof ritem @k) (arrayof int @k) int int (listof wcell @k)) (listof wcell @k))
  (lambda (xs at end frame acc)
    (if (null? xs)
        acc
        (let ((pos (- end (r-size (car xs)))))
          (r-cells (cdr xs) at pos frame
                   (tagcase (car xs)
                     (r-cell (x) (cons x acc))
                     (r-label (n) acc)
                     (r-frame () (cons (wcell-int frame) acc))
                     (r-branch (f n)
                       (cons (wcell-int (if f rop-branchf rop-branch)) (cons (wcell-int (- (array-ref at n) (+ pos 2))) acc)))
                     (r-guard-to (c w n)
                       (cons (wcell-int rop-global-guard) (cons c (cons w (cons (wcell-int (- (array-ref at n) (+ pos 4))) acc)))))))))))
(define r-assemble (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (rgen) (listof wcell @k))
  (lambda (g)
    (let* ((items (get (extract g items)))
           (at (the (arrayof int @k) (make-array (+ 1 (get (extract g labels))) 0)))
           (end (r-place (r-reverse items nil) at 0)))
      (r-cells items at end (get (extract g mslot)) nil))))

;;; ------------------------------------------------------------- variables

(define r-where (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv symbol) (listof rloc @k))
  (lambda (env n)
    (cond ((null? env)
           (let ((l (c-where (the cenv nil) n)))
             (if (null? l)
                 nil
                 (tagcase (car l) (at-global (g) (the (listof rloc @k) (cons (rl-global g) nil))) (else y nil)))))
          ((symbol=? (car (car env)) n) (the (listof rloc @k) (cons (cdr (car env)) nil)))
          (else (r-where (cdr env) n)))))

;; A let-bound name in the cellular environment: a local, captured as such.
(define r-local (subr (maxeff (read @globals) (alloc @k)) (cenv symbol) cenv)
  (lambda (te n) (the cenv (cons (cons n (at-slot -1)) te))))

(define r-simple? (subr pure (exp) bool)
  (lambda (x)
    (tagcase x
      (e-var (n a b) #t) (e-int (n a b) #t) (e-bool (v a b) #t) (e-char (v a b) #t)
      (e-sym (v a b) #t) (e-unit (a b) #t) (e-str (v a b) #t)
      (else y #f))))

;; A constant's cell.
(define r-const-cell (subr pure (rconst) wcell)
  (lambda (c) (tagcase c (rc-int (n) (wcell-int n)) (rc-bool (v) (wcell-bool v)) (rc-char (v) (wcell-char v)) (rc-nil () (wcell-nil)))))
;; Whether a constant is #f.
(define r-const-false? (subr pure (rconst) bool)
  (lambda (c) (tagcase c (rc-bool (v) (not v)) (else y #f))))
;; An integer under 2^30 in size, in a list, if `c` is one.
(define r-const-small (subr (alloc @k) (rconst) (listof int @k))
  (lambda (c)
    (tagcase c
      (rc-int (n) (if (and (< n 1073741824) (> n -1073741824)) (the (listof int @k) (cons n nil)) nil))
      (else y nil))))

(define r-this-name? (subr (read @k) ((listof c-this @k) symbol int) bool)
  (lambda (this n nargs)
    (and (not (null? this)) (and (symbol=? n (extract (car this) 1)) (= nargs (extract (car this) 3))))))

;; Whether `f` is the procedure running, called with its arity: its own
;; name, still bound where the procedure knows itself to be.
(define r-self-known? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (rgen exp int cenv) bool)
  (lambda (g f nargs te)
    (tagcase f
      (e-var (n a b)
        (and (r-this-name? (extract g this) n nargs)
             (let ((l (c-find te n))) (and (not (null? l)) (c-this-loc? (car l) (extract (car (extract g this)) 2))))))
      (else y #f))))

;;; ------------------------------------------------------ standard names

;; Runtime primitive `name` as a call-out, when it is one and `n` = `k`.
(define r-prim-std (subr (read @globals) (string int int) rstd)
  (lambda (name n k)
    (let ((p (runtime-primitive name))) (if (and (>= p 0) (= n k)) (s-prim p) (s-none)))))

;; Whether `name`, applied to `n` arguments, is a standard operation register
;; code does, and how: as the Rust compiler's `r_standard`, whose last case
;; is what the cellular compiler does with one runtime primitive.
(define r-standard (subr (maxeff (read @globals) (read @k) (alloc @k)) (string int) rstd)
  (lambda (name n)
    (let ((is (lambda ((s string) (k int)) (and (string=? name s) (= n k)))))
      (cond ((is "+" 2) (s-op2 routine-int-add #f #f))
            ((is "-" 2) (s-op2 routine-int-sub #f #f))
            ((is "<" 2) (s-op2 routine-int-less #f #f))
            ((is ">" 2) (s-op2 routine-int-less #t #f))
            ((is "<=" 2) (s-op2 routine-int-less #t #t))
            ((is ">=" 2) (s-op2 routine-int-less #f #t))
            ((or (is "=" 2) (or (is "char=?" 2) (is "symbol=?" 2))) (s-op2 routine-eq #f #f))
            ((is "not" 1) (s-op2imm routine-eq (wcell-bool #f)))
            ((or (is "null?" 1) (is "datum-null?" 1)) (s-op2imm routine-eq (wcell-nil)))
            ((or (is "car" 1) (is "datum-car" 1)) (s-op1 routine-pair-car))
            ((or (is "cdr" 1) (is "datum-cdr" 1)) (s-op1 routine-pair-cdr))
            ((is "get" 1) (s-field 2))
            ((or (is "cons" 2) (is "datum-cons" 2)) (s-cellular routine-cons))
            ((is "set" 2) (s-set))
            ((is "abort-current-continuation" 2) (s-cellular routine-abort))
            ((is "call-with-composable-continuation" 2) (s-cellular routine-callcomp))
            ((is "cwcc" 1) (s-cellular routine-callcc))
            ((is "with-mark" 3) (s-cellular routine-withmark))
            ((is "first-mark" 2) (s-cellular routine-firstmark))
            ((is "current-marks" 1) (s-cellular routine-currentmarks))
            ((is "marks-of" 2) (s-cellular routine-marksof))
            ((is "array-ref" 2) (s-special "array-ref"))
            ((is "array-set!" 3) (s-special "array-set!"))
            ((is "array-length" 1) (s-special "array-length"))
            ((is "make-array" 2) (s-special "make-array"))
            ((or (is "make-continuation-prompt-tag" 0) (is "make-continuation-mark-key" 0)) (s-special "make-box"))
            ;; What the cellular compiler does as one runtime primitive
            ;; (`c-standard-on`), register code does too.
            ((or (is "set-car!" 2) (is "set-cdr!" 2)) (s-special name))
            ((string=? name "new") (r-prim-std "%make-box" n 1))
            ((string=? name "char->string") (r-prim-std "string" n 1))
            ((or (string=? name "*") (string=? name "modulo") (string=? name "quotient")
                 (string=? name "char->integer") (string=? name "integer->char") (string=? name "string-append")
                 (string=? name "string-length") (string=? name "string-ref") (string=? name "substring")
                 (string=? name "string=?") (string=? name "string->symbol") (string=? name "symbol->string"))
             (r-prim-std name n n))
            (else
             (let ((p (standard-primitive name)))
               (cond ((string=? p "%fx26-identity") (if (= n 1) (s-identity) (s-none)))
                     ((string=? p "") (s-none))
                     (else (r-prim-std p n n)))))))))
;; The operator under the type abstractions, projections, ascriptions and
;; conversions, which compile to nothing: `((proj car @r) xs)` is `car`
;; applied.
(define r-operator (subr (maxeff (read @globals) (read @k) spin) (exp) exp)
  (lambda (f)
    (tagcase f
      (e-plambda (d body a b) (r-operator body))
      (e-proj (body ds a b) (r-operator body))
      (e-the (d body a b) (r-operator body))
      (e-convention (cnv body a b) (r-operator body))
      (else y y))))
(define r-standard-name (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp) string)
  (lambda (env f)
    (tagcase (r-operator f) (e-var (n a b) (if (null? (r-where env n)) (symbol->string n) "")) (else y ""))))
(define r-rev-consts (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof rconst @k) (listof rconst @k)) (listof rconst @k))
  (lambda (xs acc) (if (null? xs) acc (r-rev-consts (cdr xs) (cons (car xs) acc)))))
(define c-length-consts (subr (maxeff (read @globals) (read @k) spin) ((listof rconst @k)) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (c-length-consts (cdr xs))))))
;; Standard operation `name` on constants `vs`, folded, if it is one that
;; folds.
(define r-fold (subr (maxeff (read @globals) (read @k) (alloc @k)) (string (listof rconst @k)) (listof rconst @k))
  (lambda (name vs)
    (let* ((two (and (not (null? vs)) (and (not (null? (cdr vs))) (null? (cdr (cdr vs))))))
           (one (and (not (null? vs)) (null? (cdr vs))))
           (a (if two (r-const-small (car vs)) (the (listof int @k) nil)))
           (b (if two (r-const-small (car (cdr vs))) (the (listof int @k) nil)))
           (ints (and (not (null? a)) (not (null? b))))
           (int (lambda ((n int)) (the (listof rconst @k) (cons (rc-int n) nil))))
           (bool (lambda ((v bool)) (the (listof rconst @k) (cons (rc-bool v) nil)))))
      (cond ((and ints (string=? name "+")) (int (+ (car a) (car b))))
            ((and ints (string=? name "-")) (int (- (car a) (car b))))
            ((and ints (string=? name "<")) (bool (< (car a) (car b))))
            ((and ints (string=? name ">")) (bool (> (car a) (car b))))
            ((and ints (string=? name "<=")) (bool (<= (car a) (car b))))
            ((and ints (string=? name ">=")) (bool (>= (car a) (car b))))
            ((and ints (string=? name "=")) (bool (= (car a) (car b))))
            ((and one (string=? name "not")) (bool (r-const-false? (car vs))))
            ((and one (string=? name "null?")) (bool (tagcase (car vs) (rc-nil () #t) (else y #f))))
            ((and two (string=? name "char=?"))
             (tagcase (car vs)
               (rc-char (x) (tagcase (car (cdr vs)) (rc-char (y) (bool (char=? x y))) (else z nil)))
               (else z nil)))
            (else nil)))))
(define-rec
  ;; `x`'s value, if it is a constant that needs no allocation, as the Rust
  ;; compiler's `r_const` says: a literal, a name bound to one, `nil`, or a
  ;; standard operation on constants folded (`+` and `-` on integers under
  ;; 2^30 in size, which cannot overflow; comparisons; `not`; `null?`;
  ;; `char=?`).
  (r-known (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp) (listof rconst @k))
    (lambda (env x)
      (tagcase x
        (e-int (n a b) (the (listof rconst @k) (cons (rc-int n) nil)))
        (e-bool (v a b) (the (listof rconst @k) (cons (rc-bool v) nil)))
        (e-char (v a b) (the (listof rconst @k) (cons (rc-char v) nil)))
        (e-var (n a b)
          (let ((l (r-where env n)))
            (if (null? l)
                (if (string=? (symbol->string n) "nil") (the (listof rconst @k) (cons (rc-nil) nil)) nil)
                (tagcase (car l) (rl-const (c) (the (listof rconst @k) (cons c nil))) (else y nil)))))
        (e-the (d body a b) (r-known env body))
        (e-plambda (d body a b) (r-known env body))
        (e-proj (body ds a b) (r-known env body))
        (e-app (f args a b)
          (let ((name (r-standard-name env f)))
            (if (string=? name "")
                nil
                (let ((vs (r-knowns env args nil)))
                  (if (or (null? vs) (not (= (c-length-consts (car vs)) (c-count-exps args))))
                      nil
                      (r-fold name (car vs)))))))
        (else y nil))))
  ;; Each of `es`' constants, in order, onto `acc` reversed, in a list; none
  ;; if one is not a constant.
  (r-knowns (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv (listof exp finite) (listof rconst @k)) (listof (listof rconst @k) @k))
    (lambda (env es acc)
      (if (null? es)
          (the (listof (listof rconst @k) @k) (cons (r-rev-consts acc nil) nil))
          (let ((c (r-known env (car es))))
            (if (null? c) nil (r-knowns env (cdr es) (cons (car c) acc))))))))


;;; ---------------------------------------------------------------- lists

(define r-count-args (subr (maxeff (read @globals) (read @k) spin) (rargs) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (r-count-args (cdr xs))))))
(define r-exp-args (subr (maxeff (read @globals) (alloc @k)) ((listof exp finite)) rargs)
  (lambda (es) (if (null? es) nil (cons (a-e (car es)) (r-exp-args (cdr es))))))
(define r-arg-simple? (subr (read @globals) (rarg) bool)
  (lambda (a) (tagcase a (a-e (x) (r-simple? x)) (a-thunk (b) #f) (else y #t))))
;; The last argument that is not simple, or -1.
(define r-last-hard (subr (maxeff (read @globals) (read @k) spin) (rargs int int) int)
  (lambda (xs i found)
    (if (null? xs) found (r-last-hard (cdr xs) (+ i 1) (if (r-arg-simple? (car xs)) found i)))))
(define r-nth-int (subr (maxeff (read @globals) (read @k) spin) ((listof int @k) int) int)
  (lambda (xs i) (if (= i 0) (car xs) (r-nth-int (cdr xs) (- i 1)))))
(define r-nth-exp (subr (read @globals) ((listof exp finite) int) exp)
  (lambda (es i) (if (= i 0) (car es) (r-nth-exp (cdr es) (- i 1)))))

;;; ---------------------------------------------------------- expressions

;; In a procedure specialized at a lambda (`c-spec-now`): where the
;; parameter the lambda is, in a list, and the label at the body's start.
(define r-spec-at (ref (listof rloc @k) @k) (new nil))
(define r-spec-start (ref int @k) (new 0))
;; Whether two places for a value are the same register or frame slot.
(define r-same-loc? (subr pure (rloc rloc) bool)
  (lambda (a b)
    (tagcase a
      (rl-reg (i) (tagcase b (rl-reg (j) (= i j)) (else y #f)))
      (rl-slot (i) (tagcase b (rl-slot (j) (= i j)) (else y #f)))
      (else y #f))))
;; The guard of an inlined or specialized call: to `call` unless the global
;; `cell` holds a closure of `word`.
(define r-guard (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (rgen wglobal tword int) unit)
  (lambda (g cell word call) (r-emit g (r-guard-to (wcell-global cell) (wcell-word word) call))))
;; `n` arguments in registers, the procedure in RESULT: called, or in tail
;; position, the frame left first.
(define r-invoke (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (rgen int bool) unit)
  (lambda (g n tail) (if tail (begin (r-leave g) (r-opn g rop-tailinvoke n)) (r-opn g rop-invoke n))))
;; RESULT kept where a `let` keeps a value: a register (`reg`), else a
;; frame slot.
(define r-keep (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (rgen bool) rloc)
  (lambda (g reg)
    (if reg
        (let ((r (r-reg g))) (begin (r-opn g rop-setreg r) (rl-reg r)))
        (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) (rl-slot s))))))
;; The one of `c-specials` that `n`, taking `k` arguments, names, if any.
(define r-special-named (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof c-special finite) symbol int) (listof c-special @k))
  (lambda (xs n k)
    (cond ((null? xs) nil)
          ((and (symbol=? (extract (car xs) 1) n) (= (c-count-params (extract (car xs) 3)) k))
           (the (listof c-special @k) (cons (car xs) nil)))
          (else (r-special-named (cdr xs) n k)))))
;; Parameter `k` of `ps`.
(define r-nth-param (subr (read @globals) ((listof (productof (1 symbol) (2 syns-a)) finite) int) symbol)
  (lambda (ps k) (if (= k 0) (extract (car ps) 1) (r-nth-param (cdr ps) (- k 1)))))
;; Which of `c-specials`, its global, and the lambda argument, when `f`
;; names one of them and the argument at its parameter is a lambda small
;; enough to inline, taking as many arguments as it is called with; not
;; while a procedure is being specialized.
(define r-specialized
  (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp (listof exp finite)) (listof (productof (1 c-special) (2 wglobal) (3 exp)) @k))
  (lambda (env f args)
    (if (not (null? (get c-spec-now)))
        nil
        (tagcase f
          (e-var (n a b)
            (let ((l (r-where env n)))
              (if (null? l)
                  nil
                  (tagcase (car l)
                    (rl-global (cell)
                      (let ((sp (r-special-named (get c-specials) n (c-count-exps args))))
                        (if (null? sp)
                            nil
                            (let ((lam (c-nth args (extract (car sp) 6))))
                              (tagcase lam
                                (e-lambda (ps body la lb)
                                  (if (and (= (c-count-params ps) (extract (car sp) 7)) (>= (c-inline-room body c-inline-limit) 0))
                                      (the (listof (productof (1 c-special) (2 wglobal) (3 exp)) @k)
                                        (cons (product (1 (car sp)) (2 cell) (3 lam)) nil))
                                      nil))
                                (else y nil))))))
                    (else y nil)))))
          (else y nil)))))
;; Whether `x` is the parameter a procedure being specialized has the lambda
;; at, where it is.
(define r-spec-param? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp) bool)
  (lambda (env x)
    (and (not (null? (get c-spec-now)))
         (and (not (null? (get r-spec-at)))
              (tagcase x
                (e-var (m a b)
                  (and (symbol=? m (extract (car (get c-spec-now)) 5))
                       (let ((l (r-where env m))) (and (not (null? l)) (r-same-loc? (car l) (car (get r-spec-at)))))))
                (else y #f))))))
;; Whether `f` is, in a procedure being specialized, its own global: in an
;; inlined body, or the lambda's, the parameter is not in scope.
(define r-spec-self? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp (listof exp finite)) bool)
  (lambda (env f args)
    (and (not (null? (get c-spec-now)))
         (and (not (null? (get r-spec-at)))
              (let ((sp (car (get c-spec-now))))
                (and (tagcase f
                       (e-var (n a b)
                         (and (symbol=? n (extract sp 1))
                              (let ((l (r-where env n)))
                                (and (not (null? l)) (tagcase (car l) (rl-global (c) #t) (else y #f))))))
                       (else y #f))
                     (and (= (c-count-exps args) (extract sp 6)) (r-spec-param? env (c-nth args (extract sp 4))))))))))
;; Each of `made` into parameter slot `i` on.
(define r-spec-moves (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (rgen (listof int @k) int) unit)
  (lambda (g made i)
    (if (null? made)
        #u
        (begin (r-opn g rop-stack (car made)) (r-opn g rop-setstk i) (r-spec-moves g (cdr made) (+ i 1))))))
;; Frame slots as call-out operands.
(define r-slot-args (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof int @k)) rargs)
  (lambda (ss) (if (null? ss) nil (the rargs (cons (a-slot (car ss)) (r-slot-args (cdr ss)))))))
;; `n` of `b`, onto `acc`.
(define r-repeat (subr (maxeff (read @globals) (alloc @k) spin) (bool int (listof bool @k)) (listof bool @k))
  (lambda (b n acc) (if (= n 0) acc (r-repeat b (- n 1) (cons b acc)))))
;; Those flagged, while fewer than half the registers are taken from `next`.
(define r-budget (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof bool @k) int) (listof bool @k))
  (lambda (fs next)
    (cond ((null? fs) nil)
          ((and (car fs) (< next (quotient register-regs 2))) (cons #t (r-budget (cdr fs) (+ next 1))))
          (else (cons #f (r-budget (cdr fs) next))))))
;; `te` with each of `bs`' names bound, as `let`s are to the cellular
;; compiler.
(define r-local-names (subr (maxeff (read @globals) (alloc @k)) (cenv (listof (productof (1 symbol) (2 exp)) finite)) cenv)
  (lambda (te bs) (if (null? bs) te (r-local-names (r-local te (extract (car bs) 1)) (cdr bs)))))
;; A `let`'s inits, in order.
(define r-let-inits (subr (maxeff (read @globals) (alloc @k) spin) ((listof (productof (1 symbol) (2 exp)) finite)) (listof exp finite))
  (lambda (bs) (if (null? bs) nil (the (listof exp finite) (cons (extract (car bs) 2) (r-let-inits (cdr bs)))))))
;; `te` with parameters, or names, bound as `let`s are.
(define r-local-params (subr (maxeff (read @globals) (alloc @k)) (cenv (listof (productof (1 symbol) (2 syns-a)) finite)) cenv)
  (lambda (te ps) (if (null? ps) te (r-local-params (r-local te (extract (car ps) 1)) (cdr ps)))))
(define r-local-syms (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (cenv syms) cenv)
  (lambda (te ns) (if (null? ns) te (r-local-syms (r-local te (car ns)) (cdr ns)))))
;; `fs` without its first `n`.
(define r-drop-bools (subr (maxeff (read @globals) (read @k) spin) ((listof bool @k) int) (listof bool @k))
  (lambda (fs n) (if (= n 0) fs (r-drop-bools (cdr fs) (- n 1)))))
;; In a top-level definition's procedure: its name, its word, its arity, and
;; the label at the body's start (`r-self-guarded`), in a list.
(define r-own-now (ref (listof (productof (1 symbol) (2 tword) (3 int) (4 int)) @k) @k) (new nil))
;; The global `f` names, in a list, when it is the procedure's own, called
;; with its arity, and not from an inlined body, whose names may be an
;; older global's.
(define r-own-self (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp (listof exp finite)) (listof wglobal @k))
  (lambda (env f args)
    (if (or (null? (get r-own-now)) (not (null? (get c-inlining))))
        nil
        (let ((o (car (get r-own-now))))
          (if (not (= (c-count-exps args) (extract o 3)))
              nil
              (tagcase f
                (e-var (m a b)
                  (if (symbol=? m (extract o 1))
                      (let ((l (r-where env m)))
                        (if (null? l) nil (tagcase (car l) (rl-global (c) (the (listof wglobal @k) (cons c nil))) (else y nil))))
                      nil))
                (else y nil)))))))
(define r-nth-binding
  (subr (read @globals) ((listof (productof (1 symbol) (2 syn) (3 exp)) finite) int) (productof (1 symbol) (2 syn) (3 exp)))
  (lambda (bs i) (if (= i 0) (car bs) (r-nth-binding (cdr bs) (- i 1)))))
;; Whether no binding of `bs` but the `i`th mentions `name`; `k` counts.
(define r-unmentioned? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) finite) symbol int int) bool)
  (lambda (bs name i k)
    (or (null? bs)
        (and (or (= k i) (not (c-mentions? (extract (car bs) 3) name))) (r-unmentioned? (cdr bs) name i (+ k 1))))))
;; Whether `letrec` binding `i` of `bs` is a join point, as the Rust
;; compiler's `r_join_ok` says: a lambda whose body calls it only in tail
;; position, as the `letrec`'s body does, and that no sibling mentions; so
;; no closure of it need be made, and each call is a jump.
(define r-join-ok? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) finite) exp int) bool)
  (lambda (bs body i)
    (let* ((b (r-nth-binding bs i)) (name (extract b 1)) (lam (c-lambda-of (extract b 3))))
      (and (not (null? lam))
           (tagcase (car lam)
             (e-lambda (ps lbody la lb)
               (let ((n (c-count-params ps)))
                 (and (not (c-member? (c-bind-params ps nil) name))
                      (and (c-loops-only lbody name n #t)
                           (and (c-loops-only body name n #t) (r-unmentioned? bs name i 0))))))
             (else y #f))))))
;; The flags from `rest`, the `i`th binding of `bs` on.
(define r-join-flags-from
  (subr (maxeff (read @globals) (read @k) (alloc @k) spin)
        ((listof (productof (1 symbol) (2 syn) (3 exp)) finite) (listof (productof (1 symbol) (2 syn) (3 exp)) finite) exp bool int)
        (listof bool @k))
  (lambda (bs rest body tail i)
    (if (null? rest) nil (cons (and tail (r-join-ok? bs body i)) (r-join-flags-from bs (cdr rest) body tail (+ i 1))))))
;; Each binding of `bs`: whether it is a join point (in tail position).
(define r-join-flags (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) finite) exp bool) (listof bool @k))
  (lambda (bs body tail) (r-join-flags-from bs bs body tail 0)))
(define r-all? (subr (maxeff (read @globals) (read @k) spin) ((listof bool @k)) bool)
  (lambda (fs) (or (null? fs) (and (car fs) (r-all? (cdr fs))))))
;; `te` with each of `bs`' names a loop, as join points' are.
(define r-loop-names (subr (maxeff (read @globals) (alloc @k)) (cenv (listof (productof (1 symbol) (2 syn) (3 exp)) finite)) cenv)
  (lambda (te bs) (if (null? bs) te (r-loop-names (the cenv (cons (cons (extract (car bs) 1) (at-loop 0)) te)) (cdr bs)))))
;; The join point `f` names, in a list, if it names one.
(define r-join-of (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp) (listof rloc @k))
  (lambda (env f)
    (tagcase f
      (e-var (m a b)
        (let ((l (r-where env m)))
          (if (null? l) nil (tagcase (car l) (rl-join (ps label) l) (else y nil)))))
      (else y nil))))
(define c-length-locs (subr (maxeff (read @globals) (read @k) spin) ((listof rloc @k)) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (c-length-locs (cdr xs))))))
;; Each value made for a jump into its parameter's place.
(define r-jump-moves (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (rgen (listof rloc @k) (listof rloc @k)) unit)
  (lambda (g made params)
    (if (or (null? made) (null? params))
        #u
        (begin
          (tagcase (car made)
            (rl-reg (a)
              (tagcase (car params)
                (rl-reg (b) (r-opnn g rop-movereg a b))
                (rl-slot (b) (begin (r-opn g rop-reg a) (r-opn g rop-setstk b)))
                (else y (r-decline))))
            (rl-slot (a)
              (tagcase (car params)
                (rl-reg (b) (r-opnn g rop-load b a))
                (rl-slot (b) (begin (r-opn g rop-stack a) (r-opn g rop-setstk b)))
                (else y (r-decline))))
            (else y (r-decline)))
          (r-jump-moves g (cdr made) (cdr params))))))
;; A join point's parameters' places: registers in a leaf, else frame slots.
(define r-param-places (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (rgen (listof (productof (1 symbol) (2 syns-a)) finite) bool) (listof rloc @k))
  (lambda (g ps regs)
    (if (null? ps)
        nil
        (let ((l (if regs (rl-reg (r-reg g)) (rl-slot (r-slot g)))))
          (cons l (r-param-places g (cdr ps) regs))))))
;; `env` with each parameter at its place.
(define r-bind-places (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv (listof (productof (1 symbol) (2 syns-a)) finite) (listof rloc @k)) renv)
  (lambda (env ps ls)
    (if (or (null? ps) (null? ls)) env (r-bind-places (the renv (cons (cons (extract (car ps) 1) (car ls)) env)) (cdr ps) (cdr ls)))))
;; A frame slot for each binding that is no join point; -1 for one that is.
(define r-letrec-slots-j (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (rgen (listof bool @k)) (listof int @k))
  (lambda (g joins) (if (null? joins) nil (let ((s (if (car joins) -1 (r-slot g)))) (cons s (r-letrec-slots-j g (cdr joins)))))))
;; The one of `c-inlines` that `n`, taking `k` arguments, names, if any.
(define r-inline-named (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof c-inline finite) symbol int) (listof c-inline finite))
  (lambda (xs n k)
    (cond ((null? xs) nil)
          ((and (symbol=? (extract (car xs) 1) n) (= (c-count-params (extract (car xs) 3)) k))
           (the (listof c-inline finite) (cons (car xs) nil)))
          (else (r-inline-named (cdr xs) n k)))))
;; Which of `c-inlines`, and its global, when `f` names one of them, taking
;; `k` arguments, whose body is not being inlined already.
(define r-inlined (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp int) (listof (pairof c-inline wglobal @k) @k))
  (lambda (env f k)
    (tagcase f
      (e-var (n a b)
        (let ((l (r-where env n)))
          (if (or (null? l) (c-member? (get c-inlining) n))
              nil
              (tagcase (car l)
                (rl-global (cell)
                  (let ((i (r-inline-named (get c-inlines) n k)))
                    (if (null? i) nil (the (listof (pairof c-inline wglobal @k) @k) (cons (cons (car i) cell) nil)))))
                (else y nil)))))
      (else y nil))))
(define-rec
  ;; Whether evaluating `x` may call or call out, and so collect. Loops do
  ;; not; declined forms are said to, which does not matter.
  (r-collects (subr (maxeff compiles spin) (exp cenv (listof c-this @k) bool) bool)
    (lambda (x e this tail)
      (tagcase x
        (e-var (n a b) #f) (e-int (n a b) #f) (e-bool (v a b) #f) (e-str (v a b) #f) (e-char (v a b) #f)
        ;; Join points only: no closure made, and their calls are jumps.
        (e-letrec (bs body a b)
          (if (and tail (r-all? (r-join-flags bs body #t)))
              (let ((inner (r-loop-names e bs)))
                (or (r-collects body inner this tail) (r-collects-joins bs inner this)))
              #t))
        (e-sym (v a b) #f) (e-unit (a b) #f)
        (e-if (t th el a b) (or (r-collects t e this #f) (or (r-collects th e this tail) (r-collects el e this tail))))
        (e-let (bs body a b) (or (r-collects-let bs e this) (r-collects body e this tail)))
        (e-begin (es a b) (r-collects-begin es e this tail))
        ;; A place is made and ended by calling out; a region for analysis
        ;; only is nothing at run time.
        (e-letregion (k r i body a b) (if (or (= k 0) (= k 3)) (r-collects body e this tail) #t))
        (e-plambda (d body a b) (r-collects body e this tail))
        (e-proj (body ds a b) (r-collects body e this tail))
        (e-the (d body a b) (r-collects body e this tail))
        (e-convention (cnv body a b) (r-collects body e this tail))
        (e-extract (p l a b) (r-collects p e this #f))
        (e-bloblet (op i args a b)
          (if (string=? (symbol->string op) "bloblet-ref") (r-collects-all args e this) #t))
        (e-tagcase (s arms els a b)
          (or (r-collects s e this #f) (or (r-collects-arms arms e this tail) (r-collects-else els e this tail))))
        (e-app (f args a b)
          (let* ((args-collect (r-collects-all args e this))
                 ;; A loop: a call of the procedure itself, in tail position.
                 (loop-call (and tail (tagcase f
                                        (e-var (n a2 b2)
                                          (or (r-this-name? this n (c-count-exps args))
                                              (let ((l (c-find e n))) (and (not (null? l)) (c-loop? (car l))))))
                                        (else y #f))))
                 (inline (tagcase (r-operator f)
                           (e-var (n a2 b2)
                             (if (null? (c-where e n))
                                 (tagcase (r-standard (symbol->string n) (c-count-exps args))
                                   (s-op1 (r) #t) (s-op2 (r w z) #t) (s-op2imm (r v) #t) (s-field (k) #t)
                                   (s-identity () #t) (s-set () #t) (else y #f))
                                 #f))
                           (else y #f))))
            (or args-collect (not (or loop-call inline)))))
        (else y #t))))
  (r-collects-all (subr (maxeff compiles spin) ((listof exp finite) cenv (listof c-this @k)) bool)
    (lambda (es e this) (and (not (null? es)) (or (r-collects (car es) e this #f) (r-collects-all (cdr es) e this)))))
  (r-collects-let (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 exp)) finite) cenv (listof c-this @k)) bool)
    (lambda (bs e this) (and (not (null? bs)) (or (r-collects (extract (car bs) 2) e this #f) (r-collects-let (cdr bs) e this)))))
  (r-collects-begin (subr (maxeff compiles spin) ((listof exp finite) cenv (listof c-this @k) bool) bool)
    (lambda (es e this tail)
      (cond ((null? es) #f)
            ((null? (cdr es)) (r-collects (car es) e this tail))
            (else (or (r-collects (car es) e this #f) (r-collects-begin (cdr es) e this tail))))))
  (r-collects-arms (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) finite) cenv (listof c-this @k) bool) bool)
    (lambda (arms e this tail)
      (and (not (null? arms)) (or (r-collects (extract (car arms) 4) e this tail) (r-collects-arms (cdr arms) e this tail)))))
  (r-collects-else (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 exp)) finite) cenv (listof c-this @k) bool) bool)
    (lambda (els e this tail) (and (not (null? els)) (r-collects (extract (car els) 2) e this tail))))
  ;; Whether any of `bs`' lambdas' bodies, their parameters bound in `e`,
  ;; calls or calls out.
  (r-collects-joins (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) finite) cenv (listof c-this @k)) bool)
    (lambda (bs e this)
      (and (not (null? bs))
           (or (let ((lam (c-lambda-of (extract (car bs) 3))))
                 (if (null? lam)
                     #t
                     (tagcase (car lam)
                       (e-lambda (ps lbody la lb) (r-collects lbody (r-local-params e ps) this #t))
                       (e-rlambda (r l la lb)
                         (tagcase l (e-lambda (ps lbody x y) (r-collects lbody (r-local-params e ps) this #t)) (else z #t)))
                       (else y #t))))
               (r-collects-joins (cdr bs) e this)))))
  ;; For values bound in turn, the first made by `inits` in `te`, then `m`
  ;; more made without a call, and then seen by a body that calls or calls
  ;; out, or not (`body-collects`): whether each is kept in a register, as
  ;; the Rust compiler's `r_in_regs` says. In a leaf, each is. Else one is
  ;; where nothing after it calls or calls out, which is all that clobbers
  ;; registers or collects; so many, at most, as leave half the registers
  ;; for the operations' temporaries.
  (r-in-regs (subr (maxeff compiles spin) (rgen (listof exp finite) int cenv bool) (listof bool @k))
    (lambda (g inits m te body-collects)
      (if (extract g leaf)
          (r-repeat #t (+ (c-count-exps inits) m) nil)
          (r-budget (car (r-free-flags inits te (extract g this) (not body-collects) (r-repeat (not body-collects) m nil)))
                    (get (extract g nreg))))))
  ;; Each of `inits`' flags, onto `after`: set where nothing after it calls;
  ;; and whether nothing from the first init on calls.
  (r-free-flags
    (subr (maxeff compiles spin) ((listof exp finite) cenv (listof c-this @k) bool (listof bool @k)) (pairof (listof bool @k) bool @k))
    (lambda (inits te this free after)
      (if (null? inits)
          (cons after free)
          (let* ((rest (r-free-flags (cdr inits) te this free after))
                 (mine (cdr rest)))
            (cons (cons mine (car rest)) (and mine (not (r-collects (car inits) te this #f))))))))

  ;; `x`'s value into RESULT; in tail position, returned.
  (r-exp (subr (maxeff compiles spin) (rgen exp renv cenv bool) unit)
    (lambda (g x env te tail)
      (let ((k (r-known env x)))
        (if (not (null? k))
            (begin (r-op1 g rop-const (r-const-cell (car k))) (r-done g tail))
      (tagcase x
        (e-var (n a b)
          (let ((l (r-where env n)))
            (begin
              (if (null? l)
                  (if (string=? (symbol->string n) "nil") (r-op1 g rop-const (wcell-nil)) (r-decline))
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
              (r-exp g t env te #f)
              (r-emit g (r-branch #t no))
              (r-exp g th env te tail)
              (if tail #u (r-emit g (r-branch #f end)))
              (r-emit g (r-label no))
              (r-exp g el env te tail)
              (r-emit g (r-label end))))))
        (e-begin (es a b)
          (if (null? es) (begin (r-op1 g rop-const (wcell-unit)) (r-done g tail)) (r-begin g es env te tail)))
        (e-let (bs body a b)
          (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
                 (body-collects (and (not (extract g leaf)) (r-collects body (r-local-names te bs) (extract g this) tail)))
                 (flags (r-in-regs g (r-let-inits bs) 0 te body-collects)))
            (let ((bound (r-let-bind g bs env te flags)))
              (begin
                (r-exp g body (r-bind-all bound env) (r-local-all bound te) tail)
                (set (extract g nreg) regs)
                (set (extract g nslot) slots)))))
        (e-extract (p l a b)
          (let ((i (c-field-index (get c-facts) a b)))
            (if (< i 0)
                (r-decline)
                (begin (r-exp g p env te #f) (r-opn g rop-field (+ i 2)) (r-done g tail)))))
        (e-lambda (ps body a b) (begin (r-lambda g ps body env te (the syms nil) (the (listof exp @k) nil)) (r-done g tail)))
        (e-rlambda (r l a b)
          (tagcase l
            (e-lambda (ps body la lb)
              (begin (r-lambda g ps body env te (the syms nil) (the (listof exp @k) (cons r nil))) (r-done g tail)))
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
          ;; A leaf makes no closure; join points it may have.
          (if (and (extract g leaf) (not (r-all? (r-join-flags bs body tail)))) (r-decline) (r-letrec g bs body env te tail)))
        (e-app (f args a b) (r-app g f args env te tail)))))))
  (r-begin (subr (maxeff compiles spin) (rgen (listof exp finite) renv cenv bool) unit)
    (lambda (g es env te tail)
      (if (null? (cdr es))
          (r-exp g (car es) env te tail)
          (begin (r-exp g (car es) env te #f) (r-begin g (cdr es) env te tail)))))
  (r-field-args (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 exp)) finite)) rargs)
    (lambda (fs) (if (null? fs) nil (cons (a-e (extract (car fs) 2)) (r-field-args (cdr fs))))))
  ;; Each binding's value made, in the scope outside, and put where it
  ;; lives: a register in a leaf, else a frame slot. In order.
  (r-let-bind (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 exp)) finite) renv cenv (listof bool @k)) renv)
    (lambda (g bs env te flags)
      (if (null? bs)
          nil
          (let* ((k (r-known env (extract (car bs) 2)))
                 ;; A constant is bound as itself.
                 (l (if (null? k)
                        (begin (r-exp g (extract (car bs) 2) env te #f) (r-keep g (car flags)))
                        (rl-const (car k)))))
            (cons (cons (extract (car bs) 1) l) (r-let-bind g (cdr bs) env te (cdr flags)))))))
  (r-bind-all (subr (maxeff compiles spin) (renv renv) renv)
    (lambda (bound env) (if (null? bound) env (r-bind-all (cdr bound) (cons (car bound) env)))))
  (r-local-all (subr (maxeff compiles spin) (renv cenv) cenv)
    (lambda (bound te) (if (null? bound) te (r-local-all (cdr bound) (r-local te (car (car bound)))))))
  (r-bloblet (subr (maxeff compiles spin) (rgen string int (listof exp finite) renv cenv) unit)
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
  (r-app (subr (maxeff compiles spin) (rgen exp (listof exp finite) renv cenv bool) unit)
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
  (r-standard-app (subr (maxeff compiles spin) (rgen string (listof exp finite) renv cenv bool) unit)
    (lambda (g name args env te tail)
      (tagcase (r-standard name (c-count-exps args))
        (s-op2 (r swap not)
          (begin
            (if swap
                (r-binary g r (car (cdr args)) (car args) env te)
                (r-binary g r (car args) (car (cdr args)) env te))
            (if not (r-op2 g rop-op2imm (wcell-int routine-eq) (wcell-bool #f)) #u)))
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
  (r-withmark-tail (subr (maxeff compiles spin) (rgen (listof exp finite) renv cenv) unit)
    (lambda (g args env te)
      (begin
        (r-args g (r-exp-args args) env te (the (listof exp @k) nil))
        (r-leave g)
        (r-opnn g rop-cellular routine-withmark-tail 3)
      ;; Never reached (the call-out goes on in the thunk): register code
      ;; ends each path so.
      (r-op0 g rop-return))))
  ;; A call: the arguments into REG1…REGn, the procedure in RESULT.
  (r-call (subr (maxeff compiles spin) (rgen exp (listof exp finite) renv cenv bool) unit)
    (lambda (g f args env te tail)
      (let ((n (c-count-exps args)))
        (cond ((or (extract g leaf) (> n register-regs)) (r-decline))
              ((not (null? (r-inlined env f n)))
               (let ((i (car (r-inlined env f n)))) (r-inline g (car i) (cdr i) f args env te tail)))
              ((not (null? (r-specialized env f args)))
               (let ((i (car (r-specialized env f args)))) (r-specialize g (extract i 1) (extract i 2) (extract i 3) args env te tail)))
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
  (r-inline (subr (maxeff compiles spin) (rgen c-inline wglobal exp (listof exp finite) renv cenv bool) unit)
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
        (begin
          (r-guard g cell (extract i 2) call)
          (set c-genv (extract i 5))
          (set c-inlining (cons (extract i 1) outer-inlining))
          (r-exp h (extract i 4) (extract bound 1) (extract bound 2) tail)
          (set c-inlining outer-inlining)
          (set c-genv outer-genv)
          (if tail #u (r-emit g (r-branch #f end)))
          (r-emit g (r-label call))
          (r-args g (extract bound 3) env te (the (listof exp @k) (cons f nil)))
          (if tail
              (begin (r-leave g) (r-opn g rop-tailinvoke n))
              (r-opn g rop-invoke n))
          (r-emit g (r-label end))
          (set (extract g nreg) regs)
          (set (extract g nslot) slots)))))
  ;; Each parameter bound to its argument, in order: where the body finds
  ;; them, as the body's cellular scope has them, and as the call's
  ;; arguments.
  (r-inline-args
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syns-a)) finite) (listof exp finite) renv cenv)
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
                             (else y (the (listof rloc @k) nil)))))
                 (here (if (null? kept)
                           (begin (r-exp g a env te #f) (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) (rl-slot s))))
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
  (r-specialize (subr (maxeff compiles spin) (rgen c-special wglobal exp (listof exp finite) renv cenv bool) unit)
    (lambda (g sp cell lam args env te tail)
      (tagcase lam
        (e-lambda (lps lbody la lb)
          (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
                 (spec (the c-spec
                         (product (1 (extract sp 1)) (2 cell) (3 (extract sp 2)) (4 (extract sp 6))
                                  (5 (r-nth-param (extract sp 3) (extract sp 6))) (6 (c-count-params (extract sp 3)))
                                  (7 (extract sp 7)) (8 lps) (9 lbody)
                                  (10 (c-captured (c-free lbody (c-bind-params lps nil) nil) te)) (11 (get c-genv)))))
                 (outer-spec (get c-spec-now)) (outer-genv (get c-genv))
                 (made (begin
                         (set c-spec-now (the (listof c-spec @k) (cons spec nil)))
                         (set c-genv (extract sp 5))
                         ;; Named for the procedure and the lambda.
                         (set c-word-name
                              (the (listof string @k)
                                (cons (string-append (symbol->string (extract sp 1))
                                                     (string-append "@lambda@" (int->string (exp-start lbody))))
                                      nil)))
                         (c-lambda-word (extract sp 3) (extract sp 4) (the cenv nil) (the syms nil))))
                 (s (begin (set c-spec-now outer-spec) (set c-genv outer-genv) (r-slot g)))
                 (n (c-count-exps args)))
            (begin
              (r-op2 g rop-lambda (wcell-word (extract made 1)) (wcell-int 0))
              (r-opn g rop-setstk s)
              (r-args g (r-exp-args args) env te (the (listof exp @k) nil))
              (let* ((call (r-new-label g)) (end (r-new-label g)))
                (begin
                  (r-guard g cell (extract sp 2) call)
                  (r-opn g rop-stack s)
                  (r-invoke g n tail)
                  (if tail #u (r-emit g (r-branch #f end)))
                  (r-emit g (r-label call))
                  (r-op1 g rop-global (wcell-global cell))
                  (r-invoke g n tail)
                  (r-emit g (r-label end))))
              (set (extract g nreg) regs)
              (set (extract g nslot) slots))))
        (else y (r-decline)))))
  ;; In a procedure specialized at a lambda, a call of the parameter the
  ;; lambda is: the lambda's body, its parameters bound to the arguments and
  ;; the values its closure captured to those fields of the parameter's
  ;; value, where the globals are those it saw.
  (r-spec-lambda (subr (maxeff compiles spin) (rgen (listof exp finite) renv cenv bool) unit)
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
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syns-a)) finite) (listof exp finite) renv cenv (listof bool @k))
          (productof (1 renv) (2 cenv)))
    (lambda (g ps args env te flags)
      (if (or (null? ps) (null? args))
          (product (1 (the renv nil)) (2 (the cenv nil)))
          (let* ((p (extract (car ps) 1))
                 (k (r-known env (car args)))
                 (l (if (null? k) (begin (r-exp g (car args) env te #f) (r-keep g (car flags))) (rl-const (car k))))
                 (rest (r-spec-args g (cdr ps) (cdr args) env te (cdr flags))))
            (product (1 (the renv (cons (cons p l) (extract rest 1)))) (2 (r-local (extract rest 2) p)))))))
  ;; Each value the lambda's closure captured, from the parameter's value at
  ;; `at`, field `j` on, kept, in order, onto `env` and `te`.
  (r-spec-free (subr (maxeff compiles spin) (rgen rloc syms int renv cenv (listof bool @k)) (productof (1 renv) (2 cenv)))
    (lambda (g at fv j env te flags)
      (if (null? fv)
          (product (1 env) (2 te))
          (begin
            (tagcase at
              (rl-reg (k) (r-opn g rop-reg k))
              (rl-slot (s) (r-opn g rop-stack s))
              (else y (r-decline)))
            (r-opn g rop-field (+ cellular-closure-free0 j))
            (let ((l (r-keep g (car flags))))
              (r-spec-free g at (cdr fv) (+ j 1) (the renv (cons (cons (car fv) l) env)) (r-local te (car fv)) (cdr flags)))))))
  ;; A procedure calling itself through its global `cell` (a top-level
  ;; definition's, or, in a copy specialized at a lambda, with the parameter
  ;; passed as itself): the arguments made; then, if the global still holds
  ;; a closure of `word` (its own, or the one the copy was made from), this
  ;; procedure again, by its own entry, or in tail position a loop back to
  ;; `start`; else the global.
  (r-self-guarded (subr (maxeff compiles spin) (rgen wglobal tword int exp (listof exp finite) renv cenv bool) unit)
    (lambda (g cell word start f args env te tail)
      (let ((n (c-count-exps args)))
        (if (or (extract g leaf) (> n register-regs))
            (r-decline)
            (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
                   (call (r-new-label g)) (end (r-new-label g)))
              (begin
                (if tail
                    (let ((made (r-spec-temps g args env te)))
                      (begin
                        (r-guard g cell word call)
                        (r-spec-moves g made 0)
                        (r-emit g (r-branch #f start))
                        (r-emit g (r-label call))
                        (r-args g (r-slot-args made) env te (the (listof exp @k) (cons f nil)))
                        (r-invoke g n #t)))
                    (begin
                      (r-args g (r-exp-args args) env te (the (listof exp @k) nil))
                      (r-guard g cell word call)
                      (r-opn g rop-invokeself n)
                      (r-emit g (r-branch #f end))
                      (r-emit g (r-label call))
                      (r-op1 g rop-global (wcell-global cell))
                      (r-opn g rop-invoke n)
                      (r-emit g (r-label end))))
                (set (extract g nreg) regs)
                (set (extract g nslot) slots)))))))
  ;; Each argument into a frame slot of its own, in order: the slots.
  (r-spec-temps (subr (maxeff compiles spin) (rgen (listof exp finite) renv cenv) (listof int @k))
    (lambda (g args env te)
      (if (null? args)
          nil
          (let* ((s (begin (r-exp g (car args) env te #f) (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) s))))
                 (rest (r-spec-temps g (cdr args) env te)))
            (cons s rest)))))
  ;; RESULT := r(a, b), `a` evaluated first; a constant `b` an immediate.
  (r-binary (subr (maxeff compiles spin) (rgen int exp exp renv cenv) unit)
    (lambda (g r a b env te)
      (let ((o (r-operands g a b env te #t)))
        (cond ((not (null? (extract o 1))) (r-op2 g rop-op2imm (wcell-int r) (car (extract o 1))))
              ((not (null? (extract o 2))) (r-opnn g rop-op2 r (car (extract o 2))))
              (else (r-decline))))))
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
                ((r-simple? a)
                 (let ((k (r-reg g)))
                   (begin (r-into g b k env te) (r-exp g a env te #f)
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
      (let ((l (tagcase x (e-var (n a b) (r-where env n)) (else y (the (listof rloc @k) nil)))))
        (if (null? l)
            (begin (r-exp g x env te #f) (r-opn g rop-setreg k))
            (tagcase (car l)
              (rl-slot (s) (r-opnn g rop-load k s))
              (rl-reg (r) (if (= r k) #u (r-opnn g rop-movereg r k)))
              (else y (begin (r-exp g x env te #f) (r-opn g rop-setreg k))))))))
  ;; The arguments into REG1…REGn, in order, and then `f`, if a call's (one
  ;; or none), into RESULT. Not in a leaf: an argument that is not simple is
  ;; kept in the frame until all are made; a simple one is made last.
  (r-args (subr (maxeff compiles spin) (rgen rargs renv cenv (listof exp @k)) unit)
    (lambda (g args env te f)
      (if (or (extract g leaf) (> (r-count-args args) register-regs))
          (r-decline)
          (let* ((slots (get (extract g nslot)))
                 ;; The last argument that is not simple goes straight to its
                 ;; register, when the procedure is simple too.
                 (direct (if (and (not (null? f)) (not (r-simple? (car f)))) -1 (r-last-hard args 0 -1)))
                 (kept (r-args-hard g args 0 direct env te))
                 (fun (if (and (not (null? f)) (not (r-simple? (car f))))
                          (begin (r-exp g (car f) env te #f) (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) s)))
                          -1)))
            (begin
              (r-args-into g args kept 0 env te)
              (cond ((>= fun 0) (r-opn g rop-stack fun))
                    ((not (null? f)) (r-exp g (car f) env te #f))
                    (else #u))
              (set (extract g nslot) slots))))))
  ;; For each argument: -1 if simple, made later; -2 if made into its
  ;; register now; else the frame slot it is kept in.
  (r-args-hard (subr (maxeff compiles spin) (rgen rargs int int renv cenv) (listof int @k))
    (lambda (g args i direct env te)
      (if (null? args)
          nil
          (if (r-arg-simple? (car args))
              (cons -1 (r-args-hard g (cdr args) (+ i 1) direct env te))
              (begin
                (tagcase (car args)
                  (a-e (x) (r-exp g x env te #f))
                  (a-thunk (body)
                    (begin (r-lambda g (the (listof (productof (1 symbol) (2 syns-a)) finite) nil) body env te
                                     (the syms nil) (the (listof exp @k) nil))
                           #u))
                  (else y #u))
                (let ((k (if (= i direct)
                             (begin (r-opn g rop-setreg (+ i 1)) -2)
                             (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) s)))))
                  (cons k (r-args-hard g (cdr args) (+ i 1) direct env te))))))))
  (r-args-into (subr (maxeff compiles spin) (rgen rargs (listof int @k) int renv cenv) unit)
    (lambda (g args kept i env te)
      (if (null? args)
          #u
          (begin
            (let ((k (car kept)))
              (cond ((= k -2) #u)
                    ((>= k 0) (r-opnn g rop-load (+ i 1) k))
                    (else
                     (tagcase (car args)
                       (a-e (x) (r-into g x (+ i 1) env te))
                       (a-v (v) (begin (r-op1 g rop-const v) (r-opn g rop-setreg (+ i 1))))
                       (a-slot (s) (r-opnn g rop-load (+ i 1) s))
                       (a-lexical (j) (begin (r-opn g rop-lexical j) (r-opn g rop-setreg (+ i 1))))
                       (a-thunk (b) #u)))))
            (r-args-into g (cdr args) (cdr kept) (+ i 1) env te)))))
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
  (r-lambda (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syns-a)) finite) exp renv cenv syms (listof exp @k)) patches)
    (lambda (g ps body env te own region)
      (if (extract g leaf)
          (begin (r-decline) (the patches nil))
          (let* ((made (c-lambda-word ps body te own)) (w (extract made 1)) (fv (extract made 2)) (n (c-length fv)))
            (if (null? region)
                (if (> n register-regs)
                    (begin (r-decline) (the patches nil))
                    (let ((patches (r-free-regs g fv env 0)))
                      (begin (r-op2 g rop-lambda (wcell-word w) (wcell-int n)) patches)))
                (if (> (+ n 2) register-regs)
                    (begin (r-decline) (the patches nil))
                    (let* ((pa (r-free-args fv env 0)))
                      (begin
                        (r-prim g "%region-closure"
                                (the rargs (cons (a-e (car region)) (r-append-arg (extract pa 1) (a-v (wcell-word w)))))
                                env te)
                        (extract pa 2)))))))))
  ;; Each free value into REGj+1, as `lambda` wants them; a sibling not made
  ;; yet as `#f`, to be patched.
  (r-free-regs (subr (maxeff compiles spin) (rgen syms renv int) patches)
    (lambda (g fv env j)
      (if (null? fv)
          nil
          (let ((l (r-where env (car fv))))
            (if (null? l)
                (begin (r-decline) (the patches nil))
                (tagcase (car l)
                  (rl-slot (s) (begin (r-opnn g rop-load (+ j 1) s) (r-free-regs g (cdr fv) env (+ j 1))))
                  (rl-free (i) (begin (r-opn g rop-lexical i) (r-opn g rop-setreg (+ j 1)) (r-free-regs g (cdr fv) env (+ j 1))))
                  (rl-pending (s)
                    (begin (r-op1 g rop-const (wcell-bool #f)) (r-opn g rop-setreg (+ j 1))
                           (cons (cons j s) (r-free-regs g (cdr fv) env (+ j 1)))))
                  (rl-const (c)
                    (begin (r-op1 g rop-const (r-const-cell c)) (r-opn g rop-setreg (+ j 1)) (r-free-regs g (cdr fv) env (+ j 1))))
                  (else y (begin (r-decline) (the patches nil)))))))))
  ;; The same, as a call-out's operands.
  (r-free-args (subr (maxeff compiles spin) (syms renv int) (productof (1 rargs) (2 patches)))
    (lambda (fv env j)
      (if (null? fv)
          (product (1 (the rargs nil)) (2 (the patches nil)))
          (let* ((rest (r-free-args (cdr fv) env (+ j 1))) (l (r-where env (car fv))))
            (if (null? l)
                (begin (r-decline) rest)
                (tagcase (car l)
                  (rl-slot (s) (product (1 (cons (a-slot s) (extract rest 1))) (2 (extract rest 2))))
                  (rl-free (i) (product (1 (cons (a-lexical i) (extract rest 1))) (2 (extract rest 2))))
                  (rl-pending (s)
                    (product (1 (cons (a-v (wcell-bool #f)) (extract rest 1))) (2 (cons (cons j s) (extract rest 2)))))
                  (rl-const (c) (product (1 (cons (a-v (r-const-cell c)) (extract rest 1))) (2 (extract rest 2))))
                  (else y (begin (r-decline) rest))))))))
  (r-append-arg (subr (maxeff compiles spin) (rargs rarg) rargs)
    (lambda (xs x) (if (null? xs) (cons x nil) (cons (car xs) (r-append-arg (cdr xs) x)))))
  ;; Arrays, and the tag and key makers: as the stack compiler does them.
  (r-special (subr (maxeff compiles spin) (rgen string (listof exp finite) renv cenv) unit)
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
    (subr (maxeff compiles spin) (rgen exp (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) finite) (listof (productof (1 symbol) (2 exp)) finite) renv cenv bool) unit)
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
  ;; RESULT kept: in a register in a leaf, else in a frame slot.
  (r-place-value (subr compiles (rgen) rloc)
    (lambda (g)
      (if (extract g leaf)
          (let ((r (r-reg g))) (begin (r-opn g rop-setreg r) (rl-reg r)))
          (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) (rl-slot s))))))
  (r-get (subr compiles (rgen rloc) unit)
    (lambda (g l) (tagcase l (rl-reg (r) (r-opn g rop-reg r)) (rl-slot (s) (r-opn g rop-stack s)) (else y #u))))
  (r-arms
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) finite) bool rloc int renv cenv bool) unit)
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
  ;; A product's members, each kept, newest first.
  (r-members (subr (maxeff compiles spin) (rgen rloc names int renv) renv)
    (lambda (g sc xs j acc)
      (if (null? xs)
          acc
          (begin (r-get g sc) (r-opn g rop-field 3) (r-opn g rop-field (+ j 2))
                 (let ((l (r-place-value g)))
                   (r-members g sc (cdr xs) (+ j 1) (the renv (cons (cons (car xs) l) acc))))))))
  (r-reverse-env (subr (maxeff compiles spin) (renv renv) renv)
    (lambda (xs acc) (if (null? xs) acc (r-reverse-env (cdr xs) (cons (car xs) acc)))))
  ;; A tail call of the procedure itself: the new arguments made, then put
  ;; where the parameters are, and back to the start.
  (r-loop (subr (maxeff compiles spin) (rgen (listof exp finite) renv cenv) unit)
    (lambda (g args env te)
      (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot))) (made (r-loop-make g args env te)))
        (begin
          (r-loop-move g made 0)
          (r-emit g (r-branch #f (extract g start)))
          (set (extract g nreg) regs)
          (set (extract g nslot) slots)))))
  (r-loop-make (subr (maxeff compiles spin) (rgen (listof exp finite) renv cenv) (listof int @k))
    (lambda (g args env te)
      (if (null? args)
          nil
          (begin
            (r-exp g (car args) env te #f)
            (let ((m (if (extract g leaf)
                         (let ((r (r-reg g))) (begin (r-opn g rop-setreg r) r))
                         (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) s)))))
              (cons m (r-loop-make g (cdr args) env te)))))))
  (r-loop-move (subr (maxeff compiles spin) (rgen (listof int @k) int) unit)
    (lambda (g made i)
      (if (null? made)
          #u
          (begin
            (if (extract g leaf)
                (r-opnn g rop-movereg (car made) (+ i 1))
                (begin (r-opn g rop-stack (car made)) (r-opn g rop-setstk i)))
            (r-loop-move g (cdr made) (+ i 1))))))
  ;; `letrec`: each closure made into its slot, a placeholder for a sibling
  ;; not made yet; then each placeholder patched.
  (r-letrec (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) finite) exp renv cenv bool) unit)
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
  ;; A join point's call: each argument made and kept (a register in a
  ;; leaf, else a frame slot), then each into its parameter's place, and a
  ;; jump.
  (r-jump (subr (maxeff compiles spin) (rgen rloc (listof exp finite) renv cenv bool) unit)
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
  (r-jump-args (subr (maxeff compiles spin) (rgen (listof exp finite) renv cenv (listof bool @k)) (listof rloc @k))
    (lambda (g args env te flags)
      (if (null? args)
          nil
          (let* ((l (begin (r-exp g (car args) env te #f) (r-keep g (car flags))))
                 (rest (r-jump-args g (cdr args) env te (cdr flags))))
            (cons l rest)))))
  ;; Each join point's place: its parameters' places and its label, in a
  ;; list; none for a binding that is not one.
  (r-join-places
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) finite) (listof bool @k) cenv)
          (listof (listof (pairof (listof rloc @k) int @k) @k) @k))
    (lambda (g bs joins named)
      (if (null? bs)
          nil
          (let* ((here
                  (if (car joins)
                      (tagcase (car (c-lambda-of (extract (car bs) 3)))
                        (e-lambda (ps lbody la lb)
                          ;; In registers where its body makes no call (or in a
                          ;; leaf), so many as leave half of them.
                          (let* ((in-regs (or (extract g leaf)
                                              (and (not (r-collects lbody (r-local-params named ps) (extract g this) #t))
                                                   (<= (+ (get (extract g nreg)) (c-count-params ps)) (quotient register-regs 2)))))
                                 (locs (r-param-places g ps in-regs)) (label (r-new-label g)))
                            (the (listof (pairof (listof rloc @k) int @k) @k) (cons (the (pairof (listof rloc @k) int @k) (cons locs label)) nil))))
                        (else y (the (listof (pairof (listof rloc @k) int @k) @k) nil)))
                      (the (listof (pairof (listof rloc @k) int @k) @k) nil)))
                 (rest (r-join-places g (cdr bs) (cdr joins) named)))
            (cons here rest)))))
  ;; Each join point's body, after the `letrec`'s, which ends every path
  ;; itself: where its calls go.
  (r-join-bodies
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) finite) (listof (listof (pairof (listof rloc @k) int @k) @k) @k) renv cenv bool) unit)
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
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) finite) (listof (productof (1 symbol) (2 syn) (3 exp)) finite) (listof int @k) int renv cenv (listof bool @k))
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
    (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) finite) (listof int @k) int symbol
                   (listof (productof (1 symbol) (2 syns-a)) finite) exp (listof exp @k) renv cenv)
          patches)
    (lambda (g all at i name ps lbody region env te)
      (let* ((n (c-count-params ps))
             (own (r-sibling-env all at i 0 lbody n env te)))
        (r-lambda g ps lbody (extract own 1) (extract own 2) (the syms (cons name nil)) region))))
  ;; Each sibling where the closure being made sees it: a loop, if it is this
  ;; one and only called so in its body; else the slot it will be in.
  (r-sibling-env
    (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) finite) (listof int @k) int int exp int renv cenv)
          (productof (1 renv) (2 cenv)))
    (lambda (bs at i k lbody n env te)
      (if (null? bs)
          (product (1 env) (2 te))
          (let* ((sib (extract (car bs) 1))
                 (loops (and (= k i) (c-loops-only lbody sib n #t)))
                 (s (r-nth-int at k)))
            (r-sibling-env (cdr bs) at i (+ k 1) lbody n
                           (the renv (cons (cons sib (if loops (rl-loop) (rl-pending s))) env))
                           (the cenv (cons (cons sib (if loops (at-loop 0) (at-pending s))) te)))))))
  (r-letrec-patch (subr (maxeff compiles spin) (rgen (listof patches @k) (listof int @k)) unit)
    (lambda (g made at)
      (if (null? made)
          #u
          (begin
            (r-patch-one g (car made) (car at))
            (r-letrec-patch g (cdr made) (cdr at))))))
  (r-patch-one (subr (maxeff compiles spin) (rgen patches int) unit)
    (lambda (g ps slot)
      (if (null? ps)
          #u
          (begin
            (r-opnn g rop-load 1 (cdr (car ps)))
            (r-opn g rop-stack slot)
            (r-opnn g rop-setfield (+ cellular-closure-free0 (car (car ps))) 1)
            (r-patch-one g (cdr ps) slot)))))
  (r-letrec-env (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) finite) (listof int @k) renv) renv)
    (lambda (bs at env)
      (if (null? bs) env (r-letrec-env (cdr bs) (cdr at) (the renv (cons (cons (extract (car bs) 1) (rl-slot (car at))) env))))))
  (r-letrec-te (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) finite) cenv) cenv)
    (lambda (bs te) (if (null? bs) te (r-letrec-te (cdr bs) (r-local te (extract (car bs) 1))))))
  ;; The `letrec`'s names where its body sees them: a join point as itself,
  ;; any other in its slot.
  (r-letrec-env-j
    (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) finite) (listof int @k) (listof (listof (pairof (listof rloc @k) int @k) @k) @k) renv) renv)
    (lambda (bs at places env)
      (if (null? bs)
          env
          (r-letrec-env-j (cdr bs) (cdr at) (cdr places)
                          (the renv (cons (cons (extract (car bs) 1)
                                                (if (null? (car places))
                                                    (rl-slot (car at))
                                                    (rl-join (car (car (car places))) (cdr (car (car places))))))
                                          env))))))
  ;; The same to the cellular compiler: a join point a loop.
  (r-letrec-te-j (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) finite) (listof bool @k) cenv) cenv)
    (lambda (bs joins te)
      (if (null? bs)
          te
          (r-letrec-te-j (cdr bs) (cdr joins)
                         (if (car joins) (the cenv (cons (cons (extract (car bs) 1) (at-loop 0)) te)) (r-local te (extract (car bs) 1))))))))


;;; ------------------------------------------------------------ the entry

;; The register environment of a lambda's body, from its cellular one: its
;; parameters in registers in a leaf, else in the frame.
(define r-env-of (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (cenv bool) renv)
  (lambda (inner leaf)
    (if (null? inner)
        nil
        (let ((rest (r-env-of (cdr inner) leaf)) (n (car (car inner))))
          (tagcase (cdr (car inner))
            (at-slot (i) (the renv (cons (cons n (if leaf (rl-reg (+ i 1)) (rl-slot i))) rest)))
            (at-free (i) (the renv (cons (cons n (rl-free i)) rest)))
            (at-loop (z) (the renv (cons (cons n (rl-loop)) rest)))
            (at-global (g) (the renv (cons (cons n (rl-global g)) rest)))
            (at-pending (s) (begin (r-decline) rest)))))))

(define r-store-params (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (rgen int int) unit)
  (lambda (g i n)
    (if (= i n) #u (let ((s (r-slot g))) (begin (r-opnn g rop-store (+ i 1) s) (r-store-params g (+ i 1) n))))))

;; A lambda's register code, whose closure captures what `inner` says, or
;; none where this compiler declines.
(define r-register-code
  (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syns-a)) finite) exp cenv (listof c-this @k)) (listof wcell @k))
  (lambda (ps body inner this)
    (let ((outer (get r-declined)) (n (c-count-params ps))
          (outer-at (get r-spec-at)) (outer-start (get r-spec-start))
          (outer-own (get r-own-now)) (own (get c-own-now)))
      (begin
        (set r-declined #f)
        (set r-spec-at (the (listof rloc @k) nil))
        (set r-own-now (the (listof (productof (1 symbol) (2 tword) (3 int) (4 int)) @k) nil))
        (set c-own-now (the (listof (productof (1 symbol) (2 tword)) @k) nil))
        (let* ((leaf (not (r-collects body inner this #t)))
               (g (the rgen
                    (product (items (new (the (listof ritem @k) nil))) (leaf leaf) (nreg (new 0)) (nslot (new 0))
                             (mslot (new 0)) (labels (new (+ (if (null? this) 0 1) (+ (if (null? (get c-spec-now)) 0 1) (if (null? own) 0 1)))))
                             (this this) (start 0))))
               (cells
                (if (> n register-regs)
                    (the (listof wcell @k) nil)
                    (begin
                      (r-opn g rop-args n)
                      (let ((env (r-env-of inner leaf)))
                        (begin
                          (if leaf
                              (set (extract g nreg) n)
                              (begin (r-op0 g rop-save) (r-emit g (r-frame)) (r-store-params g 0 n)))
                          (if (null? this) #u (r-emit g (r-label 0)))
                          ;; A procedure specialized at a lambda: where the
                          ;; parameter is, and a label at the start.
                          (if (null? (get c-spec-now))
                              #u
                              (let ((l (r-where env (extract (car (get c-spec-now)) 5))) (start (if (null? this) 0 1)))
                                (if (null? l)
                                    (r-decline)
                                    (begin (set r-spec-at (the (listof rloc @k) (cons (car l) nil)))
                                           (set r-spec-start start)
                                           (r-emit g (r-label start))))))
                          ;; A top-level definition's procedure: a label at the
                          ;; start, for its calls of itself.
                          (if (null? own)
                              #u
                              (let ((start (+ (if (null? this) 0 1) (if (null? (get c-spec-now)) 0 1))))
                                (begin (set r-own-now (cons (product (1 (extract (car own) 1)) (2 (extract (car own) 2)) (3 n) (4 start)) nil))
                                       (r-emit g (r-label start)))))
                          (r-exp g body env inner #t)
                          (if (get r-declined) (the (listof wcell @k) nil) (r-assemble g))))))))
          (begin (set r-declined outer) (set r-spec-at outer-at) (set r-spec-start outer-start) (set r-own-now outer-own) cells))))))

(set c-register-code r-register-code)

;; Whether the compiler makes register code from now on: for a driver.
(define compile-registers! (subr (maxeff (read @globals) (write @k)) (bool) unit) (lambda (on) (set c-registers on)))
