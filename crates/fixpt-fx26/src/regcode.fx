;;; Register code for a lambda, in FX-26 (PLAN.md 13h′ (e)): what the Rust
;;; compiler's `threaded/regcode.rs` makes, instruction for instruction, as
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
  (r-frame))

;; Where a variable is, to register code.
(define-datatype rloc
  (rl-reg int)
  (rl-slot int)
  (rl-free int)
  (rl-global wglobal)
  (rl-loop)
  ;; A `letrec` sibling not made yet, to be in this frame slot.
  (rl-pending int))
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
  ;; A call-out: a runtime primitive, or a threaded routine.
  (s-prim int)
  (s-threaded int)
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
(define r-decline (subr (write @k) () unit) (lambda () (set r-declined #t)))

(define r-emit (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen ritem) unit)
  (lambda (g i) (let ((items (extract g items))) (set items (cons i (get items))))))
(define r-op0 (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen int) unit)
  (lambda (g op) (r-emit g (r-cell (wcell-int op)))))
(define r-op1 (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen int wcell) unit)
  (lambda (g op x) (begin (r-op0 g op) (r-emit g (r-cell x)))))
(define r-op2 (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen int wcell wcell) unit)
  (lambda (g op x y) (begin (r-op1 g op x) (r-emit g (r-cell y)))))
(define r-opn (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen int int) unit)
  (lambda (g op n) (r-op1 g op (wcell-int n))))
(define r-opnn (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen int int int) unit)
  (lambda (g op n m) (r-op2 g op (wcell-int n) (wcell-int m))))
(define r-new-label (subr (maxeff (read @k) (write @k)) (rgen) int)
  (lambda (g) (let* ((l (extract g labels)) (n (get l))) (begin (set l (+ n 1)) n))))
(define r-reg (subr (maxeff (read @k) (write @k)) (rgen) int)
  (lambda (g)
    (let* ((r (extract g nreg)) (n (+ (get r) 1)))
      (begin (set r n) (if (> n register-regs) (r-decline) #u) n))))
(define r-slot (subr (maxeff (read @k) (write @k)) (rgen) int)
  (lambda (g)
    (let* ((s (extract g nslot)) (n (get s)) (m (extract g mslot)))
      (begin (set s (+ n 1)) (if (> (+ n 1) (get m)) (set m (+ n 1)) #u) n))))
;; Pop the frame, if there is one, before leaving.
(define r-leave (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen) unit)
  (lambda (g) (if (extract g leaf) #u (begin (r-op0 g rop-pop) (r-emit g (r-frame))))))
(define r-done (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen bool) unit)
  (lambda (g tail) (if tail (begin (r-leave g) (r-op0 g rop-return)) #u)))

(define r-reverse (subr (maxeff (read @k) (alloc @k)) ((listof ritem @k) (listof ritem @k)) (listof ritem @k))
  (lambda (xs acc) (if (null? xs) acc (r-reverse (cdr xs) (cons (car xs) acc)))))
(define r-size (subr pure (ritem) int)
  (lambda (i) (tagcase i (r-cell (x) 1) (r-label (n) 0) (r-branch (f n) 2) (r-frame () 1))))
(define r-place (subr (maxeff (read @k) (write @k)) ((listof ritem @k) (arrayof int @k) int) unit)
  (lambda (xs at pos)
    (if (null? xs)
        #u
        (begin (tagcase (car xs) (r-label (n) (array-set! at n pos)) (else x #u))
               (r-place (cdr xs) at (+ pos (r-size (car xs))))))))
;; The cells, branches resolved (an offset counts from the cell after it),
;; and the frame's size in place.
(define r-cells (subr (maxeff (read @k) (alloc @k)) ((listof ritem @k) (arrayof int @k) int int) (listof wcell @k))
  (lambda (xs at pos frame)
    (if (null? xs)
        nil
        (let ((rest (r-cells (cdr xs) at (+ pos (r-size (car xs))) frame)))
          (tagcase (car xs)
            (r-cell (x) (cons x rest))
            (r-label (n) rest)
            (r-frame () (cons (wcell-int frame) rest))
            (r-branch (f n)
              (cons (wcell-int (if f rop-branchf rop-branch)) (cons (wcell-int (- (array-ref at n) (+ pos 2))) rest))))))))
(define r-assemble (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen) (listof wcell @k))
  (lambda (g)
    (let* ((xs (r-reverse (get (extract g items)) nil))
           (at (the (arrayof int @k) (make-array (+ 1 (get (extract g labels))) 0))))
      (begin (r-place xs at 0) (r-cells xs at 0 (get (extract g mslot)))))))

;;; ------------------------------------------------------------- variables

(define r-where (subr (maxeff (read @k) (alloc @k)) (renv symbol) (listof rloc @k))
  (lambda (env n)
    (cond ((null? env)
           (let ((l (c-where (the cenv nil) n)))
             (if (null? l)
                 nil
                 (tagcase (car l) (at-global (g) (the (listof rloc @k) (cons (rl-global g) nil))) (else y nil)))))
          ((symbol=? (car (car env)) n) (the (listof rloc @k) (cons (cdr (car env)) nil)))
          (else (r-where (cdr env) n)))))

;; A let-bound name in the threaded environment: a local, captured as such.
(define r-local (subr (alloc @k) (cenv symbol) cenv)
  (lambda (te n) (the cenv (cons (cons n (at-slot -1)) te))))

(define r-simple? (subr (read @a) (exp) bool)
  (lambda (x)
    (tagcase x
      (e-var (n a b) #t) (e-int (n a b) #t) (e-bool (v a b) #t) (e-char (v a b) #t)
      (e-sym (v a b) #t) (e-unit (a b) #t) (e-str (v a b) #t)
      (else y #f))))

;; `x`'s value, if it is a constant that needs no allocation.
(define r-constant (subr (maxeff (read @a) (alloc @k)) (exp) (listof wcell @k))
  (lambda (x)
    (tagcase x
      (e-int (n a b) (the (listof wcell @k) (cons (wcell-int n) nil)))
      (e-bool (v a b) (the (listof wcell @k) (cons (wcell-bool v) nil)))
      (e-char (v a b) (the (listof wcell @k) (cons (wcell-char v) nil)))
      (else y (the (listof wcell @k) nil)))))

(define r-this-name? (subr (read @k) ((listof c-this @k) symbol int) bool)
  (lambda (this n nargs)
    (and (not (null? this)) (and (symbol=? n (extract (car this) 1)) (= nargs (extract (car this) 3))))))

;; Whether `f` is the procedure running, called with its arity: its own
;; name, still bound where the procedure knows itself to be.
(define r-self-known? (subr (maxeff (read @a) (read @k) (alloc @k)) (rgen exp int cenv) bool)
  (lambda (g f nargs te)
    (tagcase f
      (e-var (n a b)
        (and (r-this-name? (extract g this) n nargs)
             (let ((l (c-find te n))) (and (not (null? l)) (c-this-loc? (car l) (extract (car (extract g this)) 2))))))
      (else y #f))))

;;; ------------------------------------------------------ standard names

;; Runtime primitive `name` as a call-out, when it is one and `n` = `k`.
(define r-prim-std (subr pure (string int int) rstd)
  (lambda (name n k)
    (let ((p (runtime-primitive name))) (if (and (>= p 0) (= n k)) (s-prim p) (s-none)))))

;; Whether `name`, applied to `n` arguments, is a standard operation register
;; code does, and how: as the Rust compiler's `r_standard`, whose last case
;; is what the threaded compiler does with one runtime primitive.
(define r-standard (subr (maxeff (read @k) (alloc @k)) (string int) rstd)
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
            ((or (is "cons" 2) (is "datum-cons" 2)) (s-threaded routine-cons))
            ((is "set" 2) (s-set))
            ((is "abort-current-continuation" 2) (s-threaded routine-abort))
            ((is "call-with-composable-continuation" 2) (s-threaded routine-callcomp))
            ((is "cwcc" 1) (s-threaded routine-callcc))
            ((is "with-mark" 3) (s-threaded routine-withmark))
            ((is "first-mark" 2) (s-threaded routine-firstmark))
            ((is "current-marks" 1) (s-threaded routine-currentmarks))
            ((is "marks-of" 2) (s-threaded routine-marksof))
            ((is "array-ref" 2) (s-special "array-ref"))
            ((is "array-set!" 3) (s-special "array-set!"))
            ((is "array-length" 1) (s-special "array-length"))
            ((is "make-array" 2) (s-special "make-array"))
            ((or (is "make-continuation-prompt-tag" 0) (is "make-continuation-mark-key" 0)) (s-special "make-box"))
            ;; What the threaded compiler does as one runtime primitive
            ;; (`c-standard-on`), register code does too.
            ((or (string=? name "set-car!") (string=? name "set-cdr!")) (s-none))
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
(define r-standard-name (subr (maxeff (read @a) (read @k) (alloc @k)) (renv exp) string)
  (lambda (env f)
    (tagcase f (e-var (n a b) (if (null? (r-where env n)) (symbol->string n) "")) (else y ""))))

;;; ---------------------------------------------------------------- lists

(define r-count-args (subr (read @k) (rargs) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (r-count-args (cdr xs))))))
(define r-exp-args (subr (maxeff (read @a) (alloc @k)) ((listof exp @a)) rargs)
  (lambda (es) (if (null? es) nil (cons (a-e (car es)) (r-exp-args (cdr es))))))
(define r-arg-simple? (subr (read @a) (rarg) bool)
  (lambda (a) (tagcase a (a-e (x) (r-simple? x)) (a-thunk (b) #f) (else y #t))))
;; The last argument that is not simple, or -1.
(define r-last-hard (subr (maxeff (read @a) (read @k)) (rargs int int) int)
  (lambda (xs i found)
    (if (null? xs) found (r-last-hard (cdr xs) (+ i 1) (if (r-arg-simple? (car xs)) found i)))))
(define r-nth-int (subr (read @k) ((listof int @k) int) int)
  (lambda (xs i) (if (= i 0) (car xs) (r-nth-int (cdr xs) (- i 1)))))
(define r-nth-exp (subr (read @a) ((listof exp @a) int) exp)
  (lambda (es i) (if (= i 0) (car es) (r-nth-exp (cdr es) (- i 1)))))

;;; ---------------------------------------------------------- expressions

(define-rec
  ;; Whether evaluating `x` may call or call out, and so collect. Loops do
  ;; not; declined forms are said to, which does not matter.
  (r-collects (subr compiles (exp cenv (listof c-this @k) bool) bool)
    (lambda (x e this tail)
      (tagcase x
        (e-var (n a b) #f) (e-int (n a b) #f) (e-bool (v a b) #f) (e-str (v a b) #f) (e-char (v a b) #f)
        (e-sym (v a b) #f) (e-unit (a b) #f)
        (e-if (t th el a b) (or (r-collects t e this #f) (or (r-collects th e this tail) (r-collects el e this tail))))
        (e-let (bs body a b) (or (r-collects-let bs e this) (r-collects body e this tail)))
        (e-begin (es a b) (r-collects-begin es e this tail))
        ;; A place is made and ended by calling out; a region for analysis
        ;; only is nothing at run time.
        (e-letregion (k r body a b) (if (or (= k 0) (= k 3)) (r-collects body e this tail) #t))
        (e-plambda (d body a b) (r-collects body e this tail))
        (e-proj (body ds a b) (r-collects body e this tail))
        (e-the (d body a b) (r-collects body e this tail))
        (e-extract (p l a b) (r-collects p e this #f))
        (e-bloblet (op i args a b)
          (if (string=? (symbol->string op) "bloblet-ref") (r-collects-all args e this) #t))
        (e-tagcase (s arms els a b)
          (or (r-collects s e this #f) (or (r-collects-arms arms e this tail) (r-collects-else els e this tail))))
        (e-app (f args a b)
          (let* ((args-collect (r-collects-all args e this))
                 ;; A loop: a call of the procedure itself, in tail position.
                 (loop-call (and tail (tagcase f (e-var (n a2 b2) (r-this-name? this n (c-count-exps args))) (else y #f))))
                 (inline (tagcase f
                           (e-var (n a2 b2)
                             (if (null? (c-where e n))
                                 (tagcase (r-standard (symbol->string n) (c-count-exps args))
                                   (s-op1 (r) #t) (s-op2 (r w z) #t) (s-op2imm (r v) #t) (s-field (k) #t)
                                   (s-identity () #t) (s-set () #t) (else y #f))
                                 #f))
                           (else y #f))))
            (or args-collect (not (or loop-call inline)))))
        (else y #t))))
  (r-collects-all (subr compiles ((listof exp @a) cenv (listof c-this @k)) bool)
    (lambda (es e this) (and (not (null? es)) (or (r-collects (car es) e this #f) (r-collects-all (cdr es) e this)))))
  (r-collects-let (subr compiles ((listof (productof (1 symbol) (2 exp)) @a) cenv (listof c-this @k)) bool)
    (lambda (bs e this) (and (not (null? bs)) (or (r-collects (extract (car bs) 2) e this #f) (r-collects-let (cdr bs) e this)))))
  (r-collects-begin (subr compiles ((listof exp @a) cenv (listof c-this @k) bool) bool)
    (lambda (es e this tail)
      (cond ((null? es) #f)
            ((null? (cdr es)) (r-collects (car es) e this tail))
            (else (or (r-collects (car es) e this #f) (r-collects-begin (cdr es) e this tail))))))
  (r-collects-arms (subr compiles ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a) cenv (listof c-this @k) bool) bool)
    (lambda (arms e this tail)
      (and (not (null? arms)) (or (r-collects (extract (car arms) 4) e this tail) (r-collects-arms (cdr arms) e this tail)))))
  (r-collects-else (subr compiles ((listof (productof (1 symbol) (2 exp)) @a) cenv (listof c-this @k) bool) bool)
    (lambda (els e this tail) (and (not (null? els)) (r-collects (extract (car els) 2) e this tail))))

  ;; `x`'s value into RESULT; in tail position, returned.
  (r-exp (subr compiles (rgen exp renv cenv bool) unit)
    (lambda (g x env te tail)
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
        ;; The region's name bound, as a `let`'s, to a region entered (never
        ;; in a leaf), and left with the body's value, which is so not in
        ;; tail position.
        (e-letregion (k r body a b)
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
          (let ((no (r-new-label g)) (end (r-new-label g)))
            (begin
              (r-exp g t env te #f)
              (r-emit g (r-branch #t no))
              (r-exp g th env te tail)
              (if tail #u (r-emit g (r-branch #f end)))
              (r-emit g (r-label no))
              (r-exp g el env te tail)
              (r-emit g (r-label end)))))
        (e-begin (es a b)
          (if (null? es) (begin (r-op1 g rop-const (wcell-unit)) (r-done g tail)) (r-begin g es env te tail)))
        (e-let (bs body a b)
          (let ((regs (get (extract g nreg))) (slots (get (extract g nslot))))
            (let ((bound (r-let-bind g bs env te)))
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
            (r-call-out g rop-threaded routine-prompt (the rargs (cons (a-e t) (cons (a-e h) (cons (a-thunk body) nil)))) env te)
            (r-done g tail)))
        (e-tagcase (s arms els a b) (r-tagcase g s arms els env te tail))
        (e-letrec (bs body a b) (if (extract g leaf) (r-decline) (r-letrec g bs body env te tail)))
        (e-app (f args a b) (r-app g f args env te tail)))))
  (r-begin (subr compiles (rgen (listof exp @a) renv cenv bool) unit)
    (lambda (g es env te tail)
      (if (null? (cdr es))
          (r-exp g (car es) env te tail)
          (begin (r-exp g (car es) env te #f) (r-begin g (cdr es) env te tail)))))
  (r-field-args (subr compiles ((listof (productof (1 symbol) (2 exp)) @a)) rargs)
    (lambda (fs) (if (null? fs) nil (cons (a-e (extract (car fs) 2)) (r-field-args (cdr fs))))))
  ;; Each binding's value made, in the scope outside, and put where it
  ;; lives: a register in a leaf, else a frame slot. In order.
  (r-let-bind (subr compiles (rgen (listof (productof (1 symbol) (2 exp)) @a) renv cenv) renv)
    (lambda (g bs env te)
      (if (null? bs)
          nil
          (begin
            (r-exp g (extract (car bs) 2) env te #f)
            (let ((l (if (extract g leaf)
                         (let ((r (r-reg g))) (begin (r-opn g rop-setreg r) (rl-reg r)))
                         (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) (rl-slot s))))))
              (cons (cons (extract (car bs) 1) l) (r-let-bind g (cdr bs) env te)))))))
  (r-bind-all (subr compiles (renv renv) renv)
    (lambda (bound env) (if (null? bound) env (r-bind-all (cdr bound) (cons (car bound) env)))))
  (r-local-all (subr compiles (renv cenv) cenv)
    (lambda (bound te) (if (null? bound) te (r-local-all (cdr bound) (r-local te (car (car bound)))))))
  (r-bloblet (subr compiles (rgen string int (listof exp @a) renv cenv) unit)
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
  (r-app (subr compiles (rgen exp (listof exp @a) renv cenv bool) unit)
    (lambda (g f args env te tail)
      (let ((n (c-count-exps args)))
        (if (and tail (r-self-known? g f n te))
            (r-loop g args env te)
            (let ((name (r-standard-name env f)))
              (if (string=? name "")
                  (r-call g f args env te tail)
                  (begin (r-standard-app g name args env te tail) (r-done g tail))))))))
  (r-standard-app (subr compiles (rgen string (listof exp @a) renv cenv bool) unit)
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
        ;; In tail position a mark replaces this frame's, which is stack
        ;; code's way (`withmark-tail`); left to it.
        (s-threaded (r)
          (if (and tail (= r routine-withmark))
              (r-decline)
              (r-call-out g rop-threaded r (r-exp-args args) env te)))
        (s-identity () (r-exp g (car args) env te #f))
        (s-set ()
          (let ((k (extract (r-operands g (car args) (car (cdr args)) env te #f) 2)))
            (if (null? k)
                (r-decline)
                (begin (r-opnn g rop-setfield 2 (car k)) (r-op1 g rop-const (wcell-unit))))))
        (s-special (what) (r-special g what args env te))
        (s-none () (r-decline)))))
  ;; A call: the arguments into REG1…REGn, the procedure in RESULT.
  (r-call (subr compiles (rgen exp (listof exp @a) renv cenv bool) unit)
    (lambda (g f args env te tail)
      (let ((n (c-count-exps args)))
        (cond ((or (extract g leaf) (> n register-regs)) (r-decline))
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
  ;; RESULT := r(a, b), `a` evaluated first; a constant `b` an immediate.
  (r-binary (subr compiles (rgen int exp exp renv cenv) unit)
    (lambda (g r a b env te)
      (let ((o (r-operands g a b env te #t)))
        (cond ((not (null? (extract o 1))) (r-op2 g rop-op2imm (wcell-int r) (car (extract o 1))))
              ((not (null? (extract o 2))) (r-opnn g rop-op2 r (car (extract o 2))))
              (else (r-decline))))))
  ;; `a` into RESULT and `b` into a register, `a` evaluated first; or, if
  ;; `imm` and `b` is a constant, `b` as an immediate. The register is free
  ;; again after: use it at once.
  (r-operands (subr compiles (rgen exp exp renv cenv bool) (productof (1 (listof wcell @k)) (2 (listof int @k))))
    (lambda (g a b env te imm)
      (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot)))
             (v (if imm (r-constant b) (the (listof wcell @k) nil)))
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
  (r-into (subr compiles (rgen exp int renv cenv) unit)
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
  (r-args (subr compiles (rgen rargs renv cenv (listof exp @k)) unit)
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
  (r-args-hard (subr compiles (rgen rargs int int renv cenv) (listof int @k))
    (lambda (g args i direct env te)
      (if (null? args)
          nil
          (if (r-arg-simple? (car args))
              (cons -1 (r-args-hard g (cdr args) (+ i 1) direct env te))
              (begin
                (tagcase (car args)
                  (a-e (x) (r-exp g x env te #f))
                  (a-thunk (body)
                    (begin (r-lambda g (the (listof (productof (1 symbol) (2 syns-a)) @a) nil) body env te
                                     (the syms nil) (the (listof exp @k) nil))
                           #u))
                  (else y #u))
                (let ((k (if (= i direct)
                             (begin (r-opn g rop-setreg (+ i 1)) -2)
                             (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) s)))))
                  (cons k (r-args-hard g (cdr args) (+ i 1) direct env te))))))))
  (r-args-into (subr compiles (rgen rargs (listof int @k) int renv cenv) unit)
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
  ;; A call-out, `prim p n` or `threaded r n`, on `args` in REG1…REGn.
  (r-call-out (subr compiles (rgen int int rargs renv cenv) unit)
    (lambda (g how what args env te)
      (begin (r-args g args env te (the (listof exp @k) nil)) (r-opnn g how what (r-count-args args)))))
  (r-prim (subr compiles (rgen string rargs renv cenv) unit)
    (lambda (g name args env te)
      (let ((p (runtime-primitive name))) (if (< p 0) (r-decline) (r-call-out g rop-prim p args env te)))))
  ;; A closure of a lambda into RESULT, its free values into REG1…REGn first;
  ;; `own` as for `c-lambda-word`. With a `region` (an `rlambda`'s, one or
  ;; none), the closure is made there, by `%region-closure h fv … w`. What it
  ;; gives: for each sibling not made yet (a `letrec`'s), the free value's
  ;; index and the sibling's frame slot.
  (r-lambda (subr compiles (rgen (listof (productof (1 symbol) (2 syns-a)) @a) exp renv cenv syms (listof exp @k)) patches)
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
  (r-free-regs (subr compiles (rgen syms renv int) patches)
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
                  (else y (begin (r-decline) (the patches nil)))))))))
  ;; The same, as a call-out's operands.
  (r-free-args (subr compiles (syms renv int) (productof (1 rargs) (2 patches)))
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
                  (else y (begin (r-decline) rest))))))))
  (r-append-arg (subr compiles (rargs rarg) rargs)
    (lambda (xs x) (if (null? xs) (cons x nil) (cons (car xs) (r-append-arg (cdr xs) x)))))
  ;; Arrays, and the tag and key makers: as the stack compiler does them.
  (r-special (subr compiles (rgen string (listof exp @a) renv cenv) unit)
    (lambda (g what args env te)
      (cond ((string=? what "array-ref")
             (begin
               (r-args g (r-exp-args args) env te (the (listof exp @k) nil))
               (r-opn g rop-reg 2) (r-op2 g rop-op2imm (wcell-int routine-int-add) (wcell-int 2)) (r-opn g rop-setreg 2)
               (r-opnn g rop-threaded routine-field-ref 2)))
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
            (else (r-decline)))))
  ;; `tagcase`: the scrutinee kept; each arm's tag compared, the last's not
  ;; when there is no `else` (a checked program covers every tag); the value,
  ;; or its product's members, bound.
  (r-tagcase
    (subr compiles (rgen exp (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a) (listof (productof (1 symbol) (2 exp)) @a) renv cenv bool) unit)
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
    (subr compiles (rgen (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) @a) bool rloc int renv cenv bool) unit)
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
  (r-members (subr compiles (rgen rloc names int renv) renv)
    (lambda (g sc xs j acc)
      (if (null? xs)
          acc
          (begin (r-get g sc) (r-opn g rop-field 3) (r-opn g rop-field (+ j 2))
                 (let ((l (r-place-value g)))
                   (r-members g sc (cdr xs) (+ j 1) (the renv (cons (cons (car xs) l) acc))))))))
  (r-reverse-env (subr compiles (renv renv) renv)
    (lambda (xs acc) (if (null? xs) acc (r-reverse-env (cdr xs) (cons (car xs) acc)))))
  ;; A tail call of the procedure itself: the new arguments made, then put
  ;; where the parameters are, and back to the start.
  (r-loop (subr compiles (rgen (listof exp @a) renv cenv) unit)
    (lambda (g args env te)
      (let* ((regs (get (extract g nreg))) (slots (get (extract g nslot))) (made (r-loop-make g args env te)))
        (begin
          (r-loop-move g made 0)
          (r-emit g (r-branch #f (extract g start)))
          (set (extract g nreg) regs)
          (set (extract g nslot) slots)))))
  (r-loop-make (subr compiles (rgen (listof exp @a) renv cenv) (listof int @k))
    (lambda (g args env te)
      (if (null? args)
          nil
          (begin
            (r-exp g (car args) env te #f)
            (let ((m (if (extract g leaf)
                         (let ((r (r-reg g))) (begin (r-opn g rop-setreg r) r))
                         (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) s)))))
              (cons m (r-loop-make g (cdr args) env te)))))))
  (r-loop-move (subr compiles (rgen (listof int @k) int) unit)
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
  (r-letrec (subr compiles (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) @a) exp renv cenv bool) unit)
    (lambda (g bs body env te tail)
      (let* ((slots (get (extract g nslot)))
             (at (r-letrec-slots g bs))
             (patches (r-letrec-make g bs bs at 0 env te)))
        (begin
          (r-letrec-patch g patches at)
          (r-exp g body (r-letrec-env bs at env) (r-letrec-te bs te) tail)
          (set (extract g nslot) slots)))))
  (r-letrec-slots (subr compiles (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) @a)) (listof int @k))
    (lambda (g bs) (if (null? bs) nil (let ((s (r-slot g))) (cons s (r-letrec-slots g (cdr bs)))))))
  (r-letrec-make
    (subr compiles (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) @a) (listof (productof (1 symbol) (2 syn) (3 exp)) @a) (listof int @k) int renv cenv)
          (listof patches @k))
    (lambda (g all bs at i env te)
      (if (null? bs)
          nil
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
              (cons p (r-letrec-make g all (cdr bs) at (+ i 1) env te)))))))
  (r-letrec-one
    (subr compiles (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) @a) (listof int @k) int symbol
                   (listof (productof (1 symbol) (2 syns-a)) @a) exp (listof exp @k) renv cenv)
          patches)
    (lambda (g all at i name ps lbody region env te)
      (let* ((n (c-count-params ps))
             (own (r-sibling-env all at i 0 lbody n env te)))
        (r-lambda g ps lbody (extract own 1) (extract own 2) (the syms (cons name nil)) region))))
  ;; Each sibling where the closure being made sees it: a loop, if it is this
  ;; one and only called so in its body; else the slot it will be in.
  (r-sibling-env
    (subr compiles ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) (listof int @k) int int exp int renv cenv)
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
  (r-letrec-patch (subr compiles (rgen (listof patches @k) (listof int @k)) unit)
    (lambda (g made at)
      (if (null? made)
          #u
          (begin
            (r-patch-one g (car made) (car at))
            (r-letrec-patch g (cdr made) (cdr at))))))
  (r-patch-one (subr compiles (rgen patches int) unit)
    (lambda (g ps slot)
      (if (null? ps)
          #u
          (begin
            (r-opnn g rop-load 1 (cdr (car ps)))
            (r-opn g rop-stack slot)
            (r-opnn g rop-setfield (+ threaded-closure-free0 (car (car ps))) 1)
            (r-patch-one g (cdr ps) slot)))))
  (r-letrec-env (subr compiles ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) (listof int @k) renv) renv)
    (lambda (bs at env)
      (if (null? bs) env (r-letrec-env (cdr bs) (cdr at) (the renv (cons (cons (extract (car bs) 1) (rl-slot (car at))) env))))))
  (r-letrec-te (subr compiles ((listof (productof (1 symbol) (2 syn) (3 exp)) @a) cenv) cenv)
    (lambda (bs te) (if (null? bs) te (r-letrec-te (cdr bs) (r-local te (extract (car bs) 1)))))))


;;; ------------------------------------------------------------ the entry

;; The register environment of a lambda's body, from its threaded one: its
;; parameters in registers in a leaf, else in the frame.
(define r-env-of (subr (maxeff (read @k) (write @k) (alloc @k)) (cenv bool) renv)
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

(define r-store-params (subr (maxeff (read @k) (write @k) (alloc @k)) (rgen int int) unit)
  (lambda (g i n)
    (if (= i n) #u (let ((s (r-slot g))) (begin (r-opnn g rop-store (+ i 1) s) (r-store-params g (+ i 1) n))))))

;; A lambda's register code, whose closure captures what `inner` says, or
;; none where this compiler declines.
(define r-register-code
  (subr compiles ((listof (productof (1 symbol) (2 syns-a)) @a) exp cenv (listof c-this @k)) (listof wcell @k))
  (lambda (ps body inner this)
    (let ((outer (get r-declined)) (n (c-count-params ps)))
      (begin
        (set r-declined #f)
        (let* ((leaf (not (r-collects body inner this #t)))
               (g (the rgen
                    (product (items (new (the (listof ritem @k) nil))) (leaf leaf) (nreg (new 0)) (nslot (new 0))
                             (mslot (new 0)) (labels (new (if (null? this) 0 1))) (this this) (start 0))))
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
                          (r-exp g body env inner #t)
                          (if (get r-declined) (the (listof wcell @k) nil) (r-assemble g))))))))
          (begin (set r-declined outer) cells))))))

(set c-register-code r-register-code)

;; Whether the compiler makes register code from now on: for a driver.
(define compile-registers! (subr (write @k) (bool) unit) (lambda (on) (set c-registers on)))
