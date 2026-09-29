;;; Register code, in FX-26: expressions, their helpers, and whether one
;;; may collect. `regcode.fx` first (PLAN.md 13h′).

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
(define r-special-named (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof c-special acyclic) symbol int) (listof c-special @k))
  (lambda (xs n k)
    (cond ((null? xs) nil)
          ((and (symbol=? (extract (car xs) 1) n) (= (c-count-params (extract (car xs) 3)) k))
           (the (listof c-special @k) (cons (car xs) nil)))
          (else (r-special-named (cdr xs) n k)))))
;; Parameter `k` of `ps`.
(define r-nth-param (subr (read @globals) ((listof (productof (1 symbol) (2 syns-a)) acyclic) int) symbol)
  (lambda (ps k) (if (= k 0) (extract (car ps) 1) (r-nth-param (cdr ps) (- k 1)))))
;; Which of `c-specials`, its global, and the lambda argument, when `f`
;; names one of them and the argument at its parameter is a lambda small
;; enough to inline, taking as many arguments as it is called with; not
;; while a procedure is being specialized.
(define r-specialized
  (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp (listof exp acyclic)) (listof (productof (1 c-special) (2 wglobal) (3 exp)) @k))
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
(define r-spec-self? (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp (listof exp acyclic)) bool)
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
(define r-repeat (subr (maxeff (read @globals) (alloc @k) spin) (bool int (listof bool acyclic)) (listof bool acyclic))
  (lambda (b n acc) (if (= n 0) acc (r-repeat b (- n 1) (cons b acc)))))
;; Those flagged, while fewer than half the registers are taken from `next`.
(define r-budget (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof bool acyclic) int) (listof bool acyclic))
  (lambda (fs next)
    (cond ((null? fs) nil)
          ((and (car fs) (< next (quotient register-regs 2))) (cons #t (r-budget (cdr fs) (+ next 1))))
          (else (cons #f (r-budget (cdr fs) next))))))
;; `te` with each of `bs`' names bound, as `let`s are to the cellular
;; compiler.
(define r-local-names (subr (maxeff (read @globals) (alloc @k)) (cenv (listof (productof (1 symbol) (2 exp)) acyclic)) cenv)
  (lambda (te bs) (if (null? bs) te (r-local-names (r-local te (extract (car bs) 1)) (cdr bs)))))
;; A `let`'s inits, in order.
(define r-let-inits (subr (maxeff (read @globals) (alloc @k) spin) ((listof (productof (1 symbol) (2 exp)) acyclic)) (listof exp acyclic))
  (lambda (bs) (if (null? bs) nil (the (listof exp acyclic) (cons (extract (car bs) 2) (r-let-inits (cdr bs)))))))
;; `te` with parameters, or names, bound as `let`s are.
(define r-local-params (subr (maxeff (read @globals) (alloc @k)) (cenv (listof (productof (1 symbol) (2 syns-a)) acyclic)) cenv)
  (lambda (te ps) (if (null? ps) te (r-local-params (r-local te (extract (car ps) 1)) (cdr ps)))))
(define r-local-syms (subr (maxeff (read @globals) (read @k) (alloc @k)) (cenv syms) cenv)
  (lambda (te ns) (if (null? ns) te (r-local-syms (r-local te (car ns)) (cdr ns)))))
;; `fs` without its first `n`.
(define r-drop-bools (subr (maxeff (read @globals) (read @k)) ((listof bool acyclic) int) (listof bool acyclic))
  (lambda (fs n) (if (= n 0) fs (r-drop-bools (cdr fs) (- n 1)))))
;; In a top-level definition's procedure: its name, its word, its arity, and
;; the label at the body's start (`r-self-guarded`), in a list.
(define r-own-now (ref (listof (productof (1 symbol) (2 tword) (3 int) (4 int)) @k) @k) (new nil))
;; The global `f` names, in a list, when it is the procedure's own, called
;; with its arity, and not from an inlined body, whose names may be an
;; older global's.
(define r-own-self (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp (listof exp acyclic)) (listof wglobal @k))
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
;; The flags from `rest`, the `i`th binding of `bs` on.
(define r-join-flags-from
  (subr (maxeff (read @globals) (read @k) (alloc @k) spin)
        ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp bool int)
        (listof bool acyclic))
  (lambda (bs rest body tail i)
    (if (null? rest) nil (cons (and tail (c-join-ok? bs body i)) (r-join-flags-from bs (cdr rest) body tail (+ i 1))))))
(define r-binding-names (subr (maxeff (read @globals) (alloc @k)) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) syms)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 1) (r-binding-names (cdr bs))))))
(define r-same-syms? (subr (maxeff (read @globals) (read @k)) (syms syms) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          (else (and (symbol=? (car a) (car b)) (r-same-syms? (cdr a) (cdr b)))))))
;; Each binding of `bs`: whether it is a join point (in tail position).
;; Remembered per `letrec` (`c-join-memo`), where it is in tail position.
(define r-join-flags (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) exp bool) (listof bool acyclic))
  (lambda (bs body tail)
    (if (not tail)
        (r-join-flags-from bs bs body tail 0)
        (let* ((names (r-binding-names bs))
               (known (table-ref (get c-join-memo) (exp-start body) (the c-join-answer (product (1 -1) (2 (the syms nil)) (3 (the (listof bool acyclic) nil)))))))
          (if (and (= (extract known 1) (exp-end body)) (r-same-syms? (extract known 2) names))
              (extract known 3)
              (let ((flags (r-join-flags-from bs bs body tail 0)))
                (begin (table-set! (get c-join-memo) (exp-start body) (the c-join-answer (product (1 (exp-end body)) (2 names) (3 flags))))
                       flags)))))))
(define r-all? (subr (maxeff (read @globals) (read @k)) ((listof bool acyclic)) bool)
  (lambda (fs) (or (null? fs) (and (car fs) (r-all? (cdr fs))))))
;; `te` with each of `bs`' names a loop, as join points' are.
(define r-loop-names (subr (maxeff (read @globals) (alloc @k)) (cenv (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic)) cenv)
  (lambda (te bs) (if (null? bs) te (r-loop-names (the cenv (cons (cons (extract (car bs) 1) (at-loop 0)) te)) (cdr bs)))))
;; Where local `n` is, in a list; none if it is not a local.
(define r-local-loc (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv symbol) (listof rloc @k))
  (lambda (env n)
    (cond ((null? env) nil)
          ((symbol=? (car (car env)) n) (the (listof rloc @k) (cons (cdr (car env)) nil)))
          (else (r-local-loc (cdr env) n)))))
;; The join point `f` names, in a list, if it names one: a local, so only
;; the locals are searched, not the globals, which every call would search.
(define r-join-of (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv exp) (listof rloc @k))
  (lambda (env f)
    (tagcase f
      (e-var (m a b)
        (let ((l (r-local-loc env m)))
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
(define r-param-places (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (rgen (listof (productof (1 symbol) (2 syns-a)) acyclic) bool) (listof rloc @k))
  (lambda (g ps regs)
    (if (null? ps)
        nil
        (let ((l (if regs (rl-reg (r-reg g)) (rl-slot (r-slot g)))))
          (cons l (r-param-places g (cdr ps) regs))))))
;; `env` with each parameter at its place.
(define r-bind-places (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (renv (listof (productof (1 symbol) (2 syns-a)) acyclic) (listof rloc @k)) renv)
  (lambda (env ps ls)
    (if (or (null? ps) (null? ls)) env (r-bind-places (the renv (cons (cons (extract (car ps) 1) (car ls)) env)) (cdr ps) (cdr ls)))))
;; A frame slot for each binding that is no join point; -1 for one that is.
(define r-letrec-slots-j (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (rgen (listof bool acyclic)) (listof int @k))
  (lambda (g joins) (if (null? joins) nil (let ((s (if (car joins) -1 (r-slot g)))) (cons s (r-letrec-slots-j g (cdr joins)))))))
;; While a body's fast version is compiled (`r-register-code`): whether, and
;; the globals it assumes hold what they held and what that was, newest
;; first, each once.
(define-type r-assumptions (listof (pairof wglobal tword @k) acyclic))
(define r-assuming (ref bool @k) (new #f))
;; Whether a call of itself through its global was made a loop, in the body
;; being compiled's fast version.
(define r-looped (ref bool @k) (new #f))
(define r-assumed (ref r-assumptions @k) (new nil))
(define r-assumed-has? (subr (maxeff (read @globals) (read @k)) (r-assumptions wglobal) bool)
  (lambda (xs cell) (and (not (null? xs)) (or (wglobal=? (car (car xs)) cell) (r-assumed-has? (cdr xs) cell)))))
;; Whether the body being compiled is its fast version, which assumes what
;; the guard would test: if so, the assumption noted, for its guard at the
;; start.
(define r-assume (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k)) (wglobal tword) bool)
  (lambda (cell word)
    (if (get r-assuming)
        (begin (if (r-assumed-has? (get r-assumed) cell)
                   #u
                   (set r-assumed (the r-assumptions (cons (the (pairof wglobal tword @k) (cons cell word)) (get r-assumed)))))
               #t)
        #f)))
;; The top-level definition whose body is being compiled: its name and
;; arity, in a list.
(define r-own-name (ref (listof (pairof symbol int @k) @k) @k) (new nil))
(define r-own-is? (subr (maxeff (read @globals) (read @k)) (symbol int) bool)
  (lambda (name n)
    (and (not (null? (get r-own-name)))
         (and (symbol=? (car (car (get r-own-name))) name) (= (cdr (car (get r-own-name))) n)))))
;; Each value made for a jump back to the start into its parameter's place:
;; a register's into REGi+1, a slot's into slot i.
(define r-self-moves (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) (rgen (listof rloc @k) int) unit)
  (lambda (g made i)
    (if (null? made)
        #u
        (begin
          (tagcase (car made)
            (rl-reg (r) (r-opnn g rop-movereg r (+ i 1)))
            (rl-slot (s) (begin (r-opn g rop-stack s) (r-opn g rop-setstk i)))
            (else y (r-decline)))
          (r-self-moves g (cdr made) (+ i 1))))))
;; Frame slots as call-out operands; anything else, declined.
(define r-slot-args-of (subr (maxeff (read @globals) (read @k) (write @k) (alloc @k) spin) ((listof rloc @k)) rargs)
  (lambda (ls)
    (if (null? ls)
        nil
        (the rargs (cons (tagcase (car ls) (rl-slot (s) (a-slot s)) (else y (begin (r-decline) (a-slot 0))))
                         (r-slot-args-of (cdr ls)))))))
;; A list of cells' length, and two appended.
(define r-cells-length (subr (maxeff (read @globals) (read @k) spin) ((listof wcell @k) int) int)
  (lambda (cs n) (if (null? cs) n (r-cells-length (cdr cs) (+ n 1)))))
(define r-rev-cells (subr (maxeff (read @globals) (read @k) (alloc @k) spin) ((listof wcell @k) (listof wcell @k)) (listof wcell @k))
  (lambda (cs acc) (if (null? cs) acc (r-rev-cells (cdr cs) (cons (car cs) acc)))))
(define r-rev-assumptions (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (r-assumptions r-assumptions) r-assumptions)
  (lambda (xs acc) (if (null? xs) acc (r-rev-assumptions (cdr xs) (the r-assumptions (cons (car xs) acc))))))
(define r-assumptions-length (subr (maxeff (read @globals) (read @k) spin) (r-assumptions int) int)
  (lambda (xs n) (if (null? xs) n (r-assumptions-length (cdr xs) (+ n 1)))))
;; The guards, in order, from cell `at`, each to `plain-at` where it fails,
;; onto `rest`.
(define r-guard-cells (subr (maxeff (read @globals) (read @k) (alloc @k) spin) (r-assumptions int int (listof wcell @k)) (listof wcell @k))
  (lambda (xs at plain-at rest)
    (if (null? xs)
        rest
        (cons (wcell-int rop-global-guard)
              (cons (wcell-global (car (car xs)))
                    (cons (wcell-word (cdr (car xs)))
                          (cons (wcell-int (- plain-at (+ at 4)))
                                (r-guard-cells (cdr xs) (+ at 4) plain-at rest))))))))
;; The one of `c-inlines` that `n`, taking `k` arguments, names, if any.
(define r-inline-named (subr (maxeff (read @globals) (read @k) (alloc @k)) ((listof c-inline acyclic) symbol int) (listof c-inline acyclic))
  (lambda (xs n k)
    (cond ((null? xs) nil)
          ((and (symbol=? (extract (car xs) 1) n) (= (c-count-params (extract (car xs) 3)) k))
           (the (listof c-inline acyclic) (cons (car xs) nil)))
          (else (r-inline-named (cdr xs) n k)))))
;; A standard operation as a value, into RESULT: its closure, of the word
;; the stack code makes for it (`c-standard-value`), and that word's
;; register code. A leaf makes it only in tail position.
(define r-standard-value (subr (maxeff compiles spin) (rgen string bool) unit)
  (lambda (g name tail)
    (if (and (extract g leaf) (not tail))
        (r-decline)
        (let ((made (the code (new nil))))
          (begin
            (c-standard-value name made)
            (let ((items (get made)))
              (if (or (null? items) (null? (cdr items)))
                  (r-decline)
                  (tagcase (car (cdr items))
                    (i-cell (w) (r-op2 g rop-lambda w (wcell-int 0)))
                    (else y (r-decline))))))))))
;; Whether `n`, not bound in `e`, is a standard operation as a value: a
;; closure made.
(define r-standard-value? (subr (maxeff compiles spin) (cenv symbol) bool)
  (lambda (e n) (and (null? (c-where e n)) (>= (c-arity (symbol->string n)) 0))))
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
  ;; Whether evaluating `x` may call or call out, and so collect: a
  ;; conversion calls out.
  (r-collects (subr (maxeff compiles spin) (exp cenv (listof c-this @k) bool) bool)
    (lambda (x e this tail)
      (or (>= (c-conversion-at x) 0) (r-collects-as-is x e this tail))))
  ;; Whether evaluating `x` may call or call out, and so collect. Loops do
  ;; not; declined forms are said to, which does not matter.
  (r-collects-as-is (subr (maxeff compiles spin) (exp cenv (listof c-this @k) bool) bool)
    (lambda (x e this tail)
      (tagcase x
        (e-var (n a b) (and (r-standard-value? e n) (not tail))) (e-int (n a b) #f) (e-bool (v a b) #f) (e-str (v a b) #f) (e-char (v a b) #f)
        ;; Join points only: no closure made, and their calls are jumps.
        (e-letrec (bs body a b)
          (if (and tail (r-all? (r-join-flags bs body #t)))
              (let ((inner (r-loop-names e bs)))
                (or (r-collects body inner this tail) (r-collects-joins bs inner this)))
              #t))
        (e-sym (v a b) #f) (e-unit (a b) #f)
        ;; A closure made as the value: its call-out may collect, but nothing
        ;; is used after it (`r-lambda`).
        (e-lambda (ps body a b) (not tail))
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
            (or args-collect (not (or loop-call (or inline (r-call-is-free? f (c-count-exps args) e tail)))))))
        (else y #t))))
  (r-collects-all (subr (maxeff compiles spin) ((listof exp acyclic) cenv (listof c-this @k)) bool)
    (lambda (es e this) (and (not (null? es)) (or (r-collects (car es) e this #f) (r-collects-all (cdr es) e this)))))
  (r-collects-let (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 exp)) acyclic) cenv (listof c-this @k)) bool)
    (lambda (bs e this) (and (not (null? bs)) (or (r-collects (extract (car bs) 2) e this #f) (r-collects-let (cdr bs) e this)))))
  (r-collects-begin (subr (maxeff compiles spin) ((listof exp acyclic) cenv (listof c-this @k) bool) bool)
    (lambda (es e this tail)
      (cond ((null? es) #f)
            ((null? (cdr es)) (r-collects (car es) e this tail))
            (else (or (r-collects (car es) e this #f) (r-collects-begin (cdr es) e this tail))))))
  (r-collects-arms (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic) cenv (listof c-this @k) bool) bool)
    (lambda (arms e this tail)
      (and (not (null? arms)) (or (r-collects (extract (car arms) 4) e this tail) (r-collects-arms (cdr arms) e this tail)))))
  (r-collects-else (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 exp)) acyclic) cenv (listof c-this @k) bool) bool)
    (lambda (els e this tail) (and (not (null? els)) (r-collects (extract (car els) 2) e this tail))))
  ;; Whether a call of global `f` with `n` arguments, in a body's fast
  ;; version (`r-register-code`), is no call: its own in tail position, a
  ;; loop; or one inlined, whose body makes none. As the Rust compiler's
  ;; `r_call_is_free`.
  (r-call-is-free? (subr (maxeff compiles spin) (exp int cenv bool) bool)
    (lambda (f n e tail)
      (and (get r-assuming)
           (tagcase f
             (e-var (name a b)
               (let ((l (c-where e name)))
                 (and (not (null? l))
                      (and (tagcase (car l) (at-global (c) #t) (else y #f))
                           (and (not (c-member? (get c-inlining) name))
                                (or (and tail (and (null? (get c-inlining)) (r-own-is? name n)))
                                    (let ((i (r-inline-named (get c-inlines) name n)))
                                      (and (not (null? i))
                                           (let ((outer-genv (get c-genv)) (outer-inlining (get c-inlining)))
                                             (begin
                                               (set c-genv (extract (car i) 5))
                                               (set c-inlining (cons name outer-inlining))
                                               (let ((collects (r-collects (extract (car i) 4) (r-local-params (the cenv nil) (extract (car i) 3)) (the (listof c-this @k) nil) tail)))
                                                 (begin (set c-inlining outer-inlining) (set c-genv outer-genv) (not collects)))))))))))))
             (else y #f)))))
  ;; Whether any of `bs`' lambdas' bodies, their parameters bound in `e`,
  ;; calls or calls out.
  (r-collects-joins (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) cenv (listof c-this @k)) bool)
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
               (r-collects-joins (cdr bs) e this))))))

;; Each of `inits`' flags, onto `after`: set where nothing after it calls;
;; and whether nothing from the first init on calls.
(define r-free-flags
  (subr (maxeff compiles spin) ((listof exp acyclic) cenv (listof c-this @k) bool (listof bool acyclic)) (pairof (listof bool acyclic) bool @k))
  (lambda (inits te this free after)
    (if (null? inits)
        (cons after free)
        (let* ((rest (r-free-flags (cdr inits) te this free after))
               (mine (cdr rest)))
          (cons (cons mine (car rest)) (and mine (not (r-collects (car inits) te this #f))))))))

;; For values bound in turn, the first made by `inits` in `te`, then `m`
;; more made without a call, and then seen by a body that calls or calls
;; out, or not (`body-collects`): whether each is kept in a register, as
;; the Rust compiler's `r_in_regs` says. In a leaf, each is. Else one is
;; where nothing after it calls or calls out, which is all that clobbers
;; registers or collects; so many, at most, as leave half the registers
;; for the operations' temporaries.
(define r-in-regs (subr (maxeff compiles spin) (rgen (listof exp acyclic) int cenv bool) (listof bool acyclic))
  (lambda (g inits m te body-collects)
    (if (extract g leaf)
        (r-repeat #t (+ (c-count-exps inits) m) nil)
        (r-budget (car (r-free-flags inits te (extract g this) (not body-collects) (r-repeat (not body-collects) m nil)))
                  (get (extract g nreg))))))

;; RESULT kept: in a register in a leaf, else in a frame slot.
(define r-place-value (subr compiles (rgen) rloc)
  (lambda (g)
    (if (extract g leaf)
        (let ((r (r-reg g))) (begin (r-opn g rop-setreg r) (rl-reg r)))
        (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) (rl-slot s))))))

(define r-get (subr compiles (rgen rloc) unit)
  (lambda (g l) (tagcase l (rl-reg (r) (r-opn g rop-reg r)) (rl-slot (s) (r-opn g rop-stack s)) (else y #u))))

(define r-reverse-env (subr (maxeff compiles spin) (renv renv) renv)
  (lambda (xs acc) (if (null? xs) acc (r-reverse-env (cdr xs) (cons (car xs) acc)))))

;; A product's members, each kept, newest first.
(define r-members (subr (maxeff compiles spin) (rgen rloc names int renv) renv)
  (lambda (g sc xs j acc)
    (if (null? xs)
        acc
        (begin (r-get g sc) (r-opn g rop-field 3) (r-opn g rop-field (+ j 2))
               (let ((l (r-place-value g)))
                 (r-members g sc (cdr xs) (+ j 1) (the renv (cons (cons (car xs) l) acc))))))))

(define r-local-all (subr (maxeff compiles spin) (renv cenv) cenv)
  (lambda (bound te) (if (null? bound) te (r-local-all (cdr bound) (r-local te (car (car bound)))))))

(define r-bind-all (subr (maxeff compiles spin) (renv renv) renv)
  (lambda (bound env) (if (null? bound) env (r-bind-all (cdr bound) (cons (car bound) env)))))

;; Each value the lambda's closure captured, from the parameter's value at
;; `at`, field `j` on, kept, in order, onto `env` and `te`.
(define r-spec-free (subr (maxeff compiles spin) (rgen rloc syms int renv cenv (listof bool acyclic)) (productof (1 renv) (2 cenv)))
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

(define r-loop-move (subr (maxeff compiles spin) (rgen (listof int @k) int) unit)
  (lambda (g made i)
    (if (null? made)
        #u
        (begin
          (if (extract g leaf)
              (r-opnn g rop-movereg (car made) (+ (+ (r-this-added g) i) 1))
              (begin (r-opn g rop-stack (car made)) (r-opn g rop-setstk (+ (r-this-added g) i))))
          (r-loop-move g (cdr made) (+ i 1))))))

(define r-field-args (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 exp)) acyclic)) rargs)
  (lambda (fs) (if (null? fs) nil (cons (a-e (extract (car fs) 2)) (r-field-args (cdr fs))))))

;; Each sibling where the closure being made sees it: a loop, if it is this
;; one and only called so in its body; else the slot it will be in.
(define r-sibling-env
  (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof int @k) int int exp int renv cenv)
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

(define r-append-arg (subr (maxeff compiles spin) (rargs rarg) rargs)
  (lambda (xs x) (if (null? xs) (cons x nil) (cons (car xs) (r-append-arg (cdr xs) x)))))

;; The same, as a call-out's operands.
(define r-free-args (subr (maxeff compiles spin) (syms renv int) (productof (1 rargs) (2 patches)))
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

;; Each free value into REGj+1, as `lambda` wants them; a sibling not made
;; yet as `#f`, to be patched.
(define r-free-regs (subr (maxeff compiles spin) (rgen syms renv int) patches)
  (lambda (g fv env j)
    (if (null? fv)
        nil
        (let ((l (r-where env (car fv))))
          (if (null? l)
              (begin (r-decline) (the patches nil))
              (tagcase (car l)
                ;; (Moved already, `r-reg-moves`.)
                (rl-reg (r) (r-free-regs g (cdr fv) env (+ j 1)))
                (rl-slot (s) (begin (r-opnn g rop-load (+ j 1) s) (r-free-regs g (cdr fv) env (+ j 1))))
                (rl-free (i) (begin (r-opn g rop-lexical i) (r-opn g rop-setreg (+ j 1)) (r-free-regs g (cdr fv) env (+ j 1))))
                (rl-pending (s)
                  (begin (r-op1 g rop-const (wcell-bool #f)) (r-opn g rop-setreg (+ j 1))
                         (cons (cons j s) (r-free-regs g (cdr fv) env (+ j 1)))))
                (rl-const (c)
                  (begin (r-op1 g rop-const (r-const-cell c)) (r-opn g rop-setreg (+ j 1)) (r-free-regs g (cdr fv) env (+ j 1))))
                (else y (begin (r-decline) (the patches nil)))))))))

;; Each join point's place: its parameters' places and its label, in a
;; list; none for a binding that is not one.
(define r-join-places
  (subr (maxeff compiles spin) (rgen (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof bool acyclic) cenv)
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

;; The same to the cellular compiler: a join point a loop.
(define r-letrec-te-j (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof bool acyclic) cenv) cenv)
  (lambda (bs joins te)
    (if (null? bs)
        te
        (r-letrec-te-j (cdr bs) (cdr joins)
                       (if (car joins) (the cenv (cons (cons (extract (car bs) 1) (at-loop 0)) te)) (r-local te (extract (car bs) 1)))))))

(define r-patch-one (subr (maxeff compiles spin) (rgen patches int) unit)
  (lambda (g ps slot)
    (if (null? ps)
        #u
        (begin
          (r-opnn g rop-load 1 (cdr (car ps)))
          (r-opn g rop-stack slot)
          (r-opnn g rop-setfield (+ cellular-closure-free0 (car (car ps))) 1)
          (r-patch-one g (cdr ps) slot)))))

(define r-letrec-patch (subr (maxeff compiles spin) (rgen (listof patches @k) (listof int @k)) unit)
  (lambda (g made at)
    (if (null? made)
        #u
        (begin
          (r-patch-one g (car made) (car at))
          (r-letrec-patch g (cdr made) (cdr at))))))

;; The `letrec`'s names where its body sees them: a join point as itself,
;; any other in its slot.
(define r-letrec-env-j
  (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof int @k) (listof (listof (pairof (listof rloc @k) int @k) @k) @k) renv) renv)
  (lambda (bs at places env)
    (if (null? bs)
        env
        (r-letrec-env-j (cdr bs) (cdr at) (cdr places)
                        (the renv (cons (cons (extract (car bs) 1)
                                              (if (null? (car places))
                                                  (rl-slot (car at))
                                                  (rl-join (car (car (car places))) (cdr (car (car places))))))
                                        env))))))

(define r-letrec-env (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) (listof int @k) renv) renv)
  (lambda (bs at env)
    (if (null? bs) env (r-letrec-env (cdr bs) (cdr at) (the renv (cons (cons (extract (car bs) 1) (rl-slot (car at))) env))))))

(define r-letrec-te (subr (maxeff compiles spin) ((listof (productof (1 symbol) (2 syn) (3 exp)) acyclic) cenv) cenv)
  (lambda (bs te) (if (null? bs) te (r-letrec-te (cdr bs) (r-local te (extract (car bs) 1))))))
