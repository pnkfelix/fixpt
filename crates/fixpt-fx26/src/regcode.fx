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
  ;; `brancht` to a label.
  (r-brancht int)
  ;; The frame's size, known when the body is done.
  (r-frame)
  ;; `global-guard g w` to a label: unless global cell `g` holds a closure
  ;; made from word `w`.
  (r-guard-to wcell wcell int))

;; Where a variable is, to register code.
;; A constant that needs no allocation when it runs, as register code may
;; know one: a sum or product of constants is made while compiling, once.
(define-datatype rconst (rc-int int) (rc-bool bool) (rc-char char) (rc-nil) (rc-data wcell))

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
  ;; (`c-join-ok?`): where its parameters are, and its label.
  (rl-join (listof rloc @k) int)
  ;; A lambda-lifted procedure (`at-lifted`): only called.
  (rl-lifted int))
(define-type renv (listof (pairof symbol rloc @k) @k))

;; An operand of a call-out: an expression, a constant, a procedure of no
;; arguments whose body is an expression (a `prompt`'s), a frame slot's
;; value, or a free value of the closure running.
;; (`a-name`: a variable's value, wherever it is: a lifted procedure's
;; added argument.)
;; `a-as-is`: an expression's value, not converted as the checker said it
;; is (the conversion's own operand).
(define-datatype rarg (a-e exp) (a-v wcell) (a-thunk exp) (a-slot int) (a-lexical int) (a-name symbol) (a-as-is exp))
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
  (lambda (i) (tagcase i (r-cell (x) 1) (r-label (n) 0) (r-branch (f n) 2) (r-brancht (n) 2) (r-frame () 1) (r-guard-to (c w n) 4))))
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
                     (r-brancht (n)
                       (cons (wcell-int rop-brancht) (cons (wcell-int (- (array-ref at n) (+ pos 2))) acc)))
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

;; Whether `x` needs no register code of its own to be had: a constant, or
;; a variable not named as a standard operation is (which may be one made a
;; value, a closure); and not converted.
(define r-simple? (subr (maxeff (read @globals) (read @k)) (exp) bool)
  (lambda (x)
    (and (< (c-conversion-at x) 0)
         (tagcase x
           (e-var (n a b) (< (c-arity (symbol->string n)) 0)) (e-int (n a b) #t) (e-bool (v a b) #t) (e-char (v a b) #t)
           (e-sym (v a b) #t) (e-unit (a b) #t) (e-str (v a b) #t)
           (else y #f)))))

;; A constant's cell.
(define r-const-cell (subr pure (rconst) wcell)
  (lambda (c) (tagcase c (rc-int (n) (wcell-int n)) (rc-bool (v) (wcell-bool v)) (rc-char (v) (wcell-char v)) (rc-nil () (wcell-nil)) (rc-data (w) w))))
;; Constants' cells, in order.
(define r-const-cells (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof rconst @k)) (listof wcell @k))
  (lambda (cs) (if (null? cs) nil (cons (r-const-cell (car cs)) (r-const-cells (cdr cs))))))
;; Whether a constant is #f.
(define r-const-false? (subr pure (rconst) bool)
  (lambda (c) (tagcase c (rc-bool (v) (not v)) (else y #f))))
;; An integer under 2^30 in size, in a list, if `c` is one.
(define r-const-small (subr (alloc @k) (rconst) (listof int @k))
  (lambda (c)
    (tagcase c
      (rc-int (n) (if (and (< n 1073741824) (> n -1073741824)) (the (listof int @k) (cons n nil)) nil))
      (else y nil))))
;; Whether constant `c` (in a list) is `when` (true: anything but #f).
(define r-holds? (subr (maxeff (read @globals) (read @k)) ((listof rconst @k) bool) bool)
  (lambda (c when) (if (r-const-false? (car c)) (not when) when)))

(define r-this-name? (subr (read @k) ((listof c-this @k) symbol int) bool)
  (lambda (this n nargs)
    (and (not (null? this)) (and (symbol=? n (extract (car this) 1)) (= (+ (extract (car this) 4) nargs) (extract (car this) 3))))))
;; How many of the running procedure's parameters, first, a lifting added.
(define r-this-added (subr (read @k) (rgen) int)
  (lambda (g) (let ((this (extract g this))) (if (null? this) 0 (extract (car this) 4)))))
;; The members' `c-lifts` indices, in a list of one, if the `letrec` at
;; `a`–`b` was lifted by its stack code (`c-lift`); none if not, or if it
;; is in a body inlined or specialized here, which another program's text
;; may have spans in common with.
(define r-lifted (subr (maxeff (read @globals) (read @k)) (int int) (listof (listof int @k) @k))
  (lambda (a b)
    (if (and (null? (get c-inlining)) (null? (get c-spec-now)))
        (table-ref (get c-lifted) (c-span-key a b) (the (listof (listof int @k) @k) nil))
        nil)))
;; `bs`' names bound to the lifted procedures `ks`, onto `env`.
(define r-bind-lifted (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof int @k) renv) renv)
  (lambda (bs ks env)
    (if (null? bs) env (r-bind-lifted (cdr bs) (cdr ks) (the renv (cons (cons (extract (car bs) 1) (rl-lifted (car ks))) env))))))
;; The index in `c-lifts` of the procedure `f` names, if a lifted one; else -1.
(define r-lifted-at (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp) int)
  (lambda (env f)
    (tagcase f
      (e-var (n a b) (let ((l (r-where env n))) (if (null? l) -1 (tagcase (car l) (rl-lifted (k) k) (else y -1)))))
      (else y -1))))
;; `names` as arguments, their values wherever they are, then `rest`.
(define r-name-args (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms rargs) rargs)
  (lambda (names rest) (if (null? names) rest (the rargs (cons (a-name (car names)) (r-name-args (cdr names) rest))))))
;;; Register moves: (source, destination), source 0 being RESULT.
(define-type rmoves (listof (pairof int int @k) @k))
;; Whether a move of `ms` but the `k`th reads register `d`.
(define r-read-by-other? (subr (maxeff (read @globals) (read @k) spin) (rmoves int int int) bool)
  (lambda (ms d k i)
    (cond ((null? ms) #f)
          ((and (not (= i k)) (= (car (car ms)) d)) #t)
          (else (r-read-by-other? (cdr ms) d k (+ i 1))))))
;; The index of the first move of `ms` (from the `k`th of `all`) whose
;; destination no other move reads; -1 if none.
(define r-free-move (subr (maxeff (read @globals) (read @k) spin) (rmoves rmoves int) int)
  (lambda (all ms k)
    (cond ((null? ms) -1)
          ((r-read-by-other? all (cdr (car ms)) k 0) (r-free-move all (cdr ms) (+ k 1)))
          (else k))))
(define r-nth-move (subr (maxeff (read @globals) (read @k) spin) (rmoves int) (pairof int int @k))
  (lambda (ms k) (if (= k 0) (car ms) (r-nth-move (cdr ms) (- k 1)))))
(define r-drop-move (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (rmoves int int) rmoves)
  (lambda (ms k i) (cond ((null? ms) nil) ((= i k) (cdr ms)) (else (cons (car ms) (r-drop-move (cdr ms) k (+ i 1)))))))
;; `ms`, those reading register `d` reading RESULT instead.
(define r-reread (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (rmoves int) rmoves)
  (lambda (ms d)
    (if (null? ms)
        nil
        (cons (if (= (car (car ms)) d) (the (pairof int int @k) (cons 0 (cdr (car ms)))) (car ms)) (r-reread (cdr ms) d)))))
;; Register moves made so that none overwrites what another has yet to
;; read, as the Rust compiler's `r_par_moves`: the first whose destination
;; no other reads, in order; else, the rest a cycle, the first's
;; destination kept in RESULT, and read from there.
(define r-par-moves (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (rgen rmoves) unit)
  (lambda (g ms)
    (if (null? ms)
        #u
        (let ((k (r-free-move ms ms 0)))
          (if (>= k 0)
              (let ((m (r-nth-move ms k)))
                (begin (if (= (car m) 0) (r-opn g rop-setreg (cdr m)) (r-opnn g rop-movereg (car m) (cdr m)))
                       (r-par-moves g (r-drop-move ms k 0))))
              (let ((d (cdr (car ms))))
                (begin (r-opn g rop-reg d) (r-par-moves g (r-reread ms d)))))))))
;; The moves of each free value of `fv` (from the `j`th) in a register into
;; REGj+1, where it is not there already.
(define r-reg-moves (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (syms renv int) rmoves)
  (lambda (fv env j)
    (if (null? fv)
        nil
        (let ((l (r-where env (car fv))) (rest (r-reg-moves (cdr fv) env (+ j 1))))
          (if (null? l)
              rest
              (tagcase (car l)
                (rl-reg (r) (if (= r (+ j 1)) rest (cons (the (pairof int int @k) (cons r (+ j 1))) rest)))
                (else y rest)))))))

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
            ((or (is "=" 2) (or (is "char=?" 2) (or (is "symbol=?" 2) (is "wglobal=?" 2)))) (s-op2 routine-eq #f #f))
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
            ((or (string=? name "modulo") (string=? name "quotient")
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
;; Whether `e` is a `+` or `-` of two.
(define r-adds? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp) bool)
  (lambda (env e)
    (tagcase e
      (e-app (f args a b)
        (and (= (c-count-exps args) 2)
             (let ((n (r-standard-name env f))) (or (string=? n "+") (string=? n "-")))))
      (else y #f))))
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
  ;; `x`'s value, if it is a constant that needs no allocation when it
  ;; runs, as the Rust compiler's `r_const` says: a literal, a name bound to
  ;; one, `nil`, a standard operation on constants folded (`+` and `-` on
  ;; integers under 2^30 in size, which cannot overflow; comparisons; `not`;
  ;; `null?`; `char=?`), or a sum or product of constants, made now, once.
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
        (e-sum (t v a b)
          (let ((c (r-known env v)))
            (if (null? c) nil (the (listof rconst @k) (cons (rc-data (wcell-sum t (r-const-cell (car c)))) nil)))))
        (e-product (fs a b)
          (let ((vs (r-known-fields env fs nil)))
            (if (null? vs) nil (the (listof rconst @k) (cons (rc-data (wcell-product (r-const-cells (car vs)))) nil)))))
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
  (r-knowns (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv (listof exp acyclic) (listof rconst @k)) (listof (listof rconst @k) @k))
    (lambda (env es acc)
      (if (null? es)
          (the (listof (listof rconst @k) @k) (cons (r-rev-consts acc nil) nil))
          (let ((c (r-known env (car es))))
            (if (null? c) nil (r-knowns env (cdr es) (cons (car c) acc)))))))
  ;; The same for a product's fields.
  (r-known-fields (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv (listof (productof (1 symbol) (2 exp)) acyclic) (listof rconst @k)) (listof (listof rconst @k) @k))
    (lambda (env fs acc)
      (if (null? fs)
          (the (listof (listof rconst @k) @k) (cons (r-rev-consts acc nil) nil))
          (let ((c (r-known env (extract (car fs) 2))))
            (if (null? c) nil (r-known-fields env (cdr fs) (cons (car c) acc))))))))


;; Whether `a` and `b` are the same expression: where they are.
(define r-same-exp? (subr (read (globals exp-end exp-start)) (exp exp) bool)
  (lambda (a b) (and (= (exp-start a) (exp-start b)) (= (exp-end a) (exp-end b)))))
(define-rec
  ;; `x` as `core + k`: `core` the one operand of a chain of `+`, and of `-`
  ;; of constants, that is not a constant (none if all are), and `k` the
  ;; constants' sum, under 2^30 in size; else `x` itself and 0.
  (r-split (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp) (productof (1 (listof exp @k)) (2 int)))
    (lambda (env x)
      (let* ((c (r-known env x))
             (small (if (null? c) (the (listof int @k) nil) (r-const-small (car c)))))
        (if (not (null? small))
            (product (1 (the (listof exp @k) nil)) (2 (car small)))
            (let ((s (tagcase x
                       (e-app (f args a b)
                         (let ((name (r-standard-name env f))) (if (string=? name "") (the (listof (productof (1 (listof exp @k)) (2 int)) @k) nil) (r-split-app env name args))))
                       (else y (the (listof (productof (1 (listof exp @k)) (2 int)) @k) nil)))))
              (if (null? s) (product (1 (the (listof exp @k) (cons x nil))) (2 0)) (car s)))))))
  ;; The same for standard operation `name` applied to `args`, if it is
  ;; such a chain.
  (r-split-app (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv string (listof exp acyclic)) (listof (productof (1 (listof exp @k)) (2 int)) @k))
    (lambda (env name args)
      (if (or (not (= (c-count-exps args) 2)) (not (or (string=? name "+") (string=? name "-"))))
          (the (listof (productof (1 (listof exp @k)) (2 int)) @k) nil)
          (let* ((sa (r-split env (car args))) (sb (r-split env (car (cdr args))))
                 (pa (extract sa 1)) (pb (extract sb 1))
                 (plus (string=? name "+"))
                 (k (if plus (+ (extract sa 2) (extract sb 2)) (- (extract sa 2) (extract sb 2)))))
            (cond ((and plus (and (not (null? pa)) (not (null? pb)))) nil)
                  ((and (not plus) (not (null? pb))) nil)
                  ((not (and (< k 1073741824) (> k -1073741824))) nil)
                  (else (the (listof (productof (1 (listof exp @k)) (2 int)) @k) (cons (product (1 (if (null? pa) pb pa)) (2 k)) nil)))))))))

;;; ---------------------------------------------------------------- lists

(define r-count-args (subr (maxeff (read @globals) (read @k) spin) (rargs) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (r-count-args (cdr xs))))))
(define r-exp-args (subr (maxeff (read @globals) (alloc @k)) ((listof exp acyclic)) rargs)
  (lambda (es) (if (null? es) nil (cons (a-e (car es)) (r-exp-args (cdr es))))))
(define r-arg-simple? (subr (maxeff (read @globals) (read @k)) (rarg) bool)
  (lambda (a) (tagcase a (a-e (x) (r-simple? x)) (a-thunk (b) #f) (a-as-is (x) #f) (else y #t))))
;; The last argument that is not simple, or -1.
(define r-last-hard (subr (maxeff (read @globals) (read @k) spin) (rargs int int) int)
  (lambda (xs i found)
    (if (null? xs) found (r-last-hard (cdr xs) (+ i 1) (if (r-arg-simple? (car xs)) found i)))))
(define r-nth-arg (subr (maxeff (read @globals) (read @k) spin) (rargs int) rarg)
  (lambda (xs i) (if (= i 0) (car xs) (r-nth-arg (cdr xs) (- i 1)))))
(define r-in-reg? (subr (read @k) ((listof rloc @k)) bool)
  (lambda (l) (and (not (null? l)) (tagcase (car l) (rl-reg (r) #t) (else y #f)))))
;; Whether an argument may wait until its value is needed, as
;; `r-arg-simple?` says; past `register-regs`, a list of the rest is made
;; first, which may collect, so then not one in a register.
(define r-arg-simple-here? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (rarg renv bool) bool)
  (lambda (a env many)
    (and (r-arg-simple? a)
         (or (not many)
             (tagcase a
               (a-e (x) (tagcase x (e-var (n p q) (not (and (< (c-conversion-at x) 0) (r-in-reg? (r-where env n))))) (else y #t)))
               (a-name (n) (not (r-in-reg? (r-where env n))))
               (else y #t))))))
;; A lifted procedure's added name's value into RESULT: a value in a place.
(define r-name (subr (maxeff compiles spin) (rgen symbol renv) unit)
  (lambda (g n env)
    (let ((l (r-where env n)))
      (if (null? l)
          (r-decline)
          (tagcase (car l)
            (rl-slot (s) (r-opn g rop-stack s))
            (rl-reg (r) (r-opn g rop-reg r))
            (rl-free (j) (r-opn g rop-lexical j))
            (rl-const (c) (r-op1 g rop-const (r-const-cell c)))
            (else y (r-decline)))))))
(define r-nth-int (subr (maxeff (read @globals) (read @k) spin) ((listof int @k) int) int)
  (lambda (xs i) (if (= i 0) (car xs) (r-nth-int (cdr xs) (- i 1)))))
(define r-nth-exp (subr (read @globals) ((listof exp acyclic) int) exp)
  (lambda (es i) (if (= i 0) (car es) (r-nth-exp (cdr es) (- i 1)))))
