;;; Register code, in FX-26: expressions, their helpers, and whether one
;;; may collect. `regcode.fx` first (PLAN.md 13h′).

;;; ---------------------------------------------------------- expressions

;; In a procedure specialized at a lambda (`c-spec-now`): where the
;; parameter the lambda is, in a list, and the label at the body's start.
(define r-spec-at (ref rlocs @k) (new nil))
(define r-spec-start (ref int @k) (new 0))
;; Whether two places for a value are the same register or frame slot.
(define r-same-loc? (subr pure (rloc rloc) bool)
  (lambda (a b)
    (tagcase a
      (rl-reg (i) (tagcase b (rl-reg (j) (= i j)) (else y #f)))
      (rl-slot (i) (tagcase b (rl-slot (j) (= i j)) (else y #f)))
      (else y #f))))
;; Whether a place, in a list, is there and is `at`.
(define r-at? (subr rreads (rlocs rloc) bool)
  (lambda (l at) (and (not (null? l)) (r-same-loc? (car l) at))))
;; The guard of an inlined or specialized call: to `call` unless the global
;; `cell` holds a closure of `word`.
(define r-guard (subr emits (rgen wglobal tword int) unit)
  (lambda (g cell word call) (r-emit g (r-guard-to (wcell-global cell) (wcell-word word) call))))
;; `n` arguments in registers, the procedure in RESULT: called, or in tail
;; position, the frame left first.
(define r-invoke (subr emits (rgen int bool) unit)
  (lambda (g n tail)
    (if tail (begin (r-leave g) (r-opn g rop-tailinvoke n)) (r-opn g rop-invoke n))))
;; RESULT kept in a new register, or a new frame slot: which.
(define r-keep-in-reg (subr emits (rgen) int)
  (lambda (g) (let ((r (r-reg g))) (begin (r-opn g rop-setreg r) r))))
(define r-keep-in-slot (subr emits (rgen) int)
  (lambda (g) (let ((s (r-slot g))) (begin (r-opn g rop-setstk s) s))))
;; RESULT kept where a `let` keeps a value: a register (`reg`), else a
;; frame slot.
(define r-keep (subr emits (rgen bool) rloc)
  (lambda (g reg) (if reg (rl-reg (r-keep-in-reg g)) (rl-slot (r-keep-in-slot g)))))
;; Frame slot `from`'s value into frame slot `to`, by way of RESULT.
(define r-slot-move (subr emits (rgen int int) unit)
  (lambda (g from to) (begin (r-opn g rop-stack from) (r-opn g rop-setstk to))))
;; Constant `w`, or free value `i` of the closure running, into REGk.
(define r-const-into (subr emits (rgen wcell int) unit)
  (lambda (g w k) (begin (r-op1 g rop-const w) (r-opn g rop-setreg k))))
(define r-lexical-into (subr emits (rgen int int) unit)
  (lambda (g i k) (begin (r-opn g rop-lexical i) (r-opn g rop-setreg k))))
;; The one of `c-specials` that `n`, taking `k` arguments, names, if any.
(define r-special-named
  (subr (maxeff rreads (alloc @k)) ((listof c-special acyclic) symbol int) (listof c-special @k))
  (lambda (xs n k)
    (cond ((null? xs) nil)
          ((and (symbol=? (extract (car xs) 1) n) (= (c-count-params (extract (car xs) 3)) k))
           (the (listof c-special @k) (cons (car xs) nil)))
          (else (r-special-named (cdr xs) n k)))))
;; Parameter `k` of `ps`.
(define r-nth-param (subr (read @globals) (exp-params int) symbol)
  (lambda (ps k) (if (= k 0) (extract (car ps) 1) (r-nth-param (cdr ps) (- k 1)))))
;; Whether `body` is small enough to inline (`c-inline-limit`).
(define r-inlinable? (subr (maxeff (read @globals) spin) (exp) bool)
  (lambda (body) (>= (c-inline-room body c-inline-limit) 0)))
;; A specialized call: which of `c-specials`, its global, and the lambda.
(define-type rspecial (productof (1 c-special) (2 wglobal) (3 exp)))
;; `sp`, its global `cell`, and the lambda argument, in a list, when the
;; argument at its parameter is a lambda small enough to inline, taking as
;; many arguments as it is called with.
(define r-special-lambda (subr rbuilds (c-special wglobal exps) (listof rspecial @k))
  (lambda (sp cell args)
    (let ((lam (c-nth args (extract sp 6))))
      (tagcase lam
        (e-lambda (ps body la lb)
          (if (and (= (c-count-params ps) (extract sp 7)) (r-inlinable? body))
              (the (listof rspecial @k) (cons (product (1 sp) (2 cell) (3 lam)) nil))
              nil))
        (else y nil)))))
;; Which of `c-specials`, its global, and the lambda argument, when `f`
;; names one of them and the argument at its parameter is a lambda small
;; enough to inline, taking as many arguments as it is called with; not
;; while a procedure is being specialized.
(define r-specialized (subr rbuilds (renv exp exps) (listof rspecial @k))
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
                        (if (null? sp) nil (r-special-lambda (car sp) cell args))))
                    (else y nil)))))
          (else y nil)))))
;; Whether `x` is the parameter a procedure being specialized has the lambda
;; at, where it is.
(define r-spec-param? (subr rbuilds (renv exp) bool)
  (lambda (env x)
    (and (not (null? (get c-spec-now)))
         (and (not (null? (get r-spec-at)))
              (tagcase x
                (e-var (m a b)
                  (and (symbol=? m (extract (car (get c-spec-now)) 5))
                       (r-at? (r-where env m) (car (get r-spec-at)))))
                (else y #f))))))
;; Whether `f` is, in a procedure being specialized, its own global: in an
;; inlined body, or the lambda's, the parameter is not in scope.
(define r-spec-self? (subr rbuilds (renv exp exps) bool)
  (lambda (env f args)
    (and (not (null? (get c-spec-now)))
         (and (not (null? (get r-spec-at)))
              (let ((sp (car (get c-spec-now))))
                (and (tagcase f
                       (e-var (n a b)
                         (and (symbol=? n (extract sp 1)) (not (null? (r-var-global env f)))))
                       (else y #f))
                     (and (= (c-count-exps args) (extract sp 6))
                          (r-spec-param? env (c-nth args (extract sp 4))))))))))
;; Each of `made` into parameter slot `i` on.
(define r-spec-moves (subr (maxeff emits spin) (rgen (listof int @k) int) unit)
  (lambda (g made i)
    (if (null? made)
        #u
        (begin (r-slot-move g (car made) i) (r-spec-moves g (cdr made) (+ i 1))))))
;; Frame slots as call-out operands.
(define r-slot-args (subr rbuilds ((listof int @k)) rargs)
  (lambda (ss)
    (if (null? ss) nil (the rargs (cons (a-slot (car ss)) (r-slot-args (cdr ss)))))))
;; `n` of `b`, onto `acc`.
(define r-repeat (subr (maxeff (read @globals) (alloc @k) spin) (bool int bools) bools)
  (lambda (b n acc) (if (= n 0) acc (r-repeat b (- n 1) (cons b acc)))))
;; Half the registers: the most that values are kept in where a call may
;; come after, leaving the rest for the operations' temporaries.
(define r-half-regs int (quotient register-regs 2))
;; Those flagged, while fewer than half the registers are taken from `next`.
(define r-budget (subr (maxeff rreads (alloc @k)) (bools int) bools)
  (lambda (fs next)
    (cond ((null? fs) nil)
          ((and (car fs) (< next r-half-regs)) (cons #t (r-budget (cdr fs) (+ next 1))))
          (else (cons #f (r-budget (cdr fs) next))))))
;; `te` with each of `bs`' names bound, as `let`s are to the cellular
;; compiler.
(define r-local-names (subr (maxeff (read @globals) (alloc @k)) (cenv exp-let-bs) cenv)
  (lambda (te bs) (if (null? bs) te (r-local-names (r-local te (extract (car bs) 1)) (cdr bs)))))
;; A `let`'s inits, in order.
(define r-let-inits (subr (maxeff (read @globals) (alloc @k) spin) (exp-let-bs) exps)
  (lambda (bs) (if (null? bs) nil (the exps (cons (extract (car bs) 2) (r-let-inits (cdr bs)))))))
;; `te` with parameters, or names, bound as `let`s are.
(define r-local-params (subr (maxeff (read @globals) (alloc @k)) (cenv exp-params) cenv)
  (lambda (te ps) (if (null? ps) te (r-local-params (r-local te (extract (car ps) 1)) (cdr ps)))))
(define r-local-syms (subr (maxeff rreads (alloc @k)) (cenv syms) cenv)
  (lambda (te ns) (if (null? ns) te (r-local-syms (r-local te (car ns)) (cdr ns)))))
;; `fs` without its first `n`.
(define r-drop-bools (subr rreads (bools int) bools)
  (lambda (fs n) (if (= n 0) fs (r-drop-bools (cdr fs) (- n 1)))))
;; In a top-level definition's procedure: its name, its word, its arity, and
;; the label at the body's start (`r-self-guarded`), in a list.
(define-type rown (productof (1 symbol) (2 tword) (3 int) (4 int)))
(define r-own-now (ref (listof rown @k) @k) (new nil))
;; The global `f` names, in a list, when it is the procedure's own, called
;; with its arity, and not from an inlined body, whose names may be an
;; older global's.
(define r-own-self (subr rbuilds (renv exp exps) (listof wglobal @k))
  (lambda (env f args)
    (if (or (null? (get r-own-now)) (not (null? (get c-inlining))))
        nil
        (let ((o (car (get r-own-now))))
          (if (not (= (c-count-exps args) (extract o 3)))
              nil
              (tagcase f
                (e-var (m a b) (if (symbol=? m (extract o 1)) (r-var-global env f) nil))
                (else y nil)))))))
;; The flags from `rest`, the `i`th binding of `bs` on.
(define r-join-flags-from (subr rbuilds (exp-letrec-bs exp-letrec-bs exp bool int) bools)
  (lambda (bs rest body tail i)
    (if (null? rest)
        nil
        (let ((join (and tail (c-join-ok? bs body i))))
          (cons join (r-join-flags-from bs (cdr rest) body tail (+ i 1)))))))
(define r-binding-names (subr (maxeff (read @globals) (alloc @k)) (exp-letrec-bs) syms)
  (lambda (bs) (if (null? bs) nil (cons (extract (car bs) 1) (r-binding-names (cdr bs))))))
(define r-same-syms? (subr rreads (syms syms) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          (else (and (symbol=? (car a) (car b)) (r-same-syms? (cdr a) (cdr b)))))))
;; `flags` remembered for the `letrec` of `names` whose body is `body`.
(define r-join-remember (subr (maxeff emits spin) (exp syms bools) unit)
  (lambda (body names flags)
    (table-set! (get c-join-memo) (exp-start body)
                (the c-join-answer (product (1 (exp-end body)) (2 names) (3 flags))))))
;; Each binding of `bs`: whether it is a join point (in tail position).
;; Remembered per `letrec` (`c-join-memo`), where it is in tail position.
(define r-join-flags (subr (maxeff emits spin) (exp-letrec-bs exp bool) bools)
  (lambda (bs body tail)
    (if (not tail)
        (r-join-flags-from bs bs body tail 0)
        (let* ((names (r-binding-names bs))
               (none (the c-join-answer (product (1 -1) (2 (the syms nil)) (3 (the bools nil)))))
               (known (table-ref (get c-join-memo) (exp-start body) none)))
          (if (and (= (extract known 1) (exp-end body)) (r-same-syms? (extract known 2) names))
              (extract known 3)
              (let ((flags (r-join-flags-from bs bs body tail 0)))
                (begin (r-join-remember body names flags) flags)))))))
(define r-all? (subr rreads (bools) bool)
  (lambda (fs) (or (null? fs) (and (car fs) (r-all? (cdr fs))))))
;; `te` with `n` a loop, as a join point is to the cellular compiler.
(define r-local-loop (subr (maxeff (read @globals) (alloc @k)) (cenv symbol) cenv)
  (lambda (te n) (the cenv (cons (cons n (at-loop 0)) te))))
;; `te` with each of `bs`' names a loop, as join points' are.
(define r-loop-names (subr (maxeff (read @globals) (alloc @k)) (cenv exp-letrec-bs) cenv)
  (lambda (te bs)
    (if (null? bs) te (r-loop-names (r-local-loop te (extract (car bs) 1)) (cdr bs)))))
;; Where local `n` is, in a list; none if it is not a local.
(define r-local-loc (subr rbuilds (renv symbol) rlocs)
  (lambda (env n)
    (cond ((null? env) nil)
          ((symbol=? (car (car env)) n) (the rlocs (cons (cdr (car env)) nil)))
          (else (r-local-loc (cdr env) n)))))
;; The join point `f` names, in a list, if it names one: a local, so only
;; the locals are searched, not the globals, which every call would search.
(define r-join-of (subr rbuilds (renv exp) rlocs)
  (lambda (env f)
    (tagcase f
      (e-var (m a b)
        (let ((l (r-local-loc env m)))
          (if (null? l) nil (tagcase (car l) (rl-join (ps label) l) (else y nil)))))
      (else y nil))))
(define c-length-locs (subr rscans (rlocs) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (c-length-locs (cdr xs))))))
;; Each value made for a jump into its parameter's place.
(define r-jump-moves (subr (maxeff emits spin) (rgen rlocs rlocs) unit)
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
                (rl-slot (b) (r-slot-move g a b))
                (else y (r-decline))))
            (else y (r-decline)))
          (r-jump-moves g (cdr made) (cdr params))))))
;; A join point's parameters' places: registers in a leaf, else frame slots.
(define r-param-places (subr (maxeff emits spin) (rgen exp-params bool) rlocs)
  (lambda (g ps regs)
    (if (null? ps)
        nil
        (let ((l (if regs (rl-reg (r-reg g)) (rl-slot (r-slot g)))))
          (cons l (r-param-places g (cdr ps) regs))))))
;; `env` with each parameter at its place.
(define r-bind-places (subr rbuilds (renv exp-params rlocs) renv)
  (lambda (env ps ls)
    (if (or (null? ps) (null? ls))
        env
        (r-bind-places (r-bind (extract (car ps) 1) (car ls) env) (cdr ps) (cdr ls)))))
;; A frame slot for each binding that is no join point; -1 for one that is.
(define r-letrec-slots-j (subr (maxeff emits spin) (rgen bools) (listof int @k))
  (lambda (g joins)
    (if (null? joins)
        nil
        (let ((s (if (car joins) -1 (r-slot g)))) (cons s (r-letrec-slots-j g (cdr joins)))))))
;; While a body's fast version is compiled (`r-register-code`): whether, and
;; the globals it assumes hold what they held and what that was, newest
;; first, each once.
(define-type r-assumption (pairof wglobal tword @k))
(define-type r-assumptions (listof r-assumption acyclic))
(define r-assuming (ref bool @k) (new #f))
;; Whether a call of itself through its global was made a loop, in the body
;; being compiled's fast version.
(define r-looped (ref bool @k) (new #f))
(define r-assumed (ref r-assumptions @k) (new nil))
(define r-assumed-has? (subr rreads (r-assumptions wglobal) bool)
  (lambda (xs cell)
    (and (not (null? xs)) (or (wglobal=? (car (car xs)) cell) (r-assumed-has? (cdr xs) cell)))))
;; That global `cell` holds a closure of `word`, assumed: noted.
(define r-note-assumed (subr emits (wglobal tword) unit)
  (lambda (cell word)
    (set r-assumed (the r-assumptions (cons (the r-assumption (cons cell word)) (get r-assumed))))))
;; Whether the body being compiled is its fast version, which assumes what
;; the guard would test: if so, the assumption noted, for its guard at the
;; start.
(define r-assume (subr emits (wglobal tword) bool)
  (lambda (cell word)
    (if (get r-assuming)
        (begin (if (r-assumed-has? (get r-assumed) cell) #u (r-note-assumed cell word))
               #t)
        #f)))
;; The top-level definition whose body is being compiled: its name and
;; arity, in a list.
(define-type rown-name (pairof symbol int @k))
(define r-own-name (ref (listof rown-name @k) @k) (new nil))
(define r-own-is? (subr rreads (symbol int) bool)
  (lambda (name n)
    (and (not (null? (get r-own-name)))
         (and (symbol=? (car (car (get r-own-name))) name) (= (cdr (car (get r-own-name))) n)))))
;; Each value made for a jump back to the start into its parameter's place:
;; a register's into REGi+1, a slot's into slot i.
(define r-self-moves (subr (maxeff emits spin) (rgen rlocs int) unit)
  (lambda (g made i)
    (if (null? made)
        #u
        (begin
          (tagcase (car made)
            (rl-reg (r) (r-opnn g rop-movereg r (+ i 1)))
            (rl-slot (s) (r-slot-move g s i))
            (else y (r-decline)))
          (r-self-moves g (cdr made) (+ i 1))))))
;; A frame slot as a call-out operand; anything else, declined.
(define r-slot-arg (subr emits (rloc) rarg)
  (lambda (l) (tagcase l (rl-slot (s) (a-slot s)) (else y (begin (r-decline) (a-slot 0))))))
;; Frame slots as call-out operands; anything else, declined.
(define r-slot-args-of (subr (maxeff emits spin) (rlocs) rargs)
  (lambda (ls)
    (if (null? ls) nil (the rargs (cons (r-slot-arg (car ls)) (r-slot-args-of (cdr ls)))))))
;; A list of cells' length, and two appended.
(define r-cells-length (subr rscans (wcells int) int)
  (lambda (cs n) (if (null? cs) n (r-cells-length (cdr cs) (+ n 1)))))
(define r-rev-cells (subr rbuilds (wcells wcells) wcells)
  (lambda (cs acc) (if (null? cs) acc (r-rev-cells (cdr cs) (cons (car cs) acc)))))
(define r-rev-assumptions (subr rbuilds (r-assumptions r-assumptions) r-assumptions)
  (lambda (xs acc)
    (if (null? xs) acc (r-rev-assumptions (cdr xs) (the r-assumptions (cons (car xs) acc))))))
(define r-assumptions-length (subr rscans (r-assumptions int) int)
  (lambda (xs n) (if (null? xs) n (r-assumptions-length (cdr xs) (+ n 1)))))
;; The guards, in order, from cell `at`, each to `plain-at` where it fails,
;; onto `rest`.
(define r-guard-cells (subr rbuilds (r-assumptions int int wcells) wcells)
  (lambda (xs at plain-at rest)
    (if (null? xs)
        rest
        (cons (wcell-int rop-global-guard)
              (cons (wcell-global (car (car xs)))
                    (cons (wcell-word (cdr (car xs)))
                          (cons (wcell-int (- plain-at (+ at 4)))
                                (r-guard-cells (cdr xs) (+ at 4) plain-at rest))))))))
;; The one of `c-inlines` that `n`, taking `k` arguments, names, if any.
(define r-inline-named
  (subr (maxeff rreads (alloc @k)) ((listof c-inline acyclic) symbol int) (listof c-inline acyclic))
  (lambda (xs n k)
    (cond ((null? xs) nil)
          ((and (symbol=? (extract (car xs) 1) n) (= (c-count-params (extract (car xs) 3)) k))
           (the (listof c-inline acyclic) (cons (car xs) nil)))
          (else (r-inline-named (cdr xs) n k)))))
;; The item made second, of those made (newest first, at least two).
(define* r-next-to-oldest (subr (maxeff (read @k) spin) (items) item)
  (lambda (xs) (if (null? (cdr (cdr xs))) (car xs) (r-next-to-oldest (cdr xs)))))
;; A standard operation as a value, into RESULT: its closure, of the word
;; the stack code makes for it (`c-standard-value`), and that word's
;; register code. A leaf makes it only in tail position. `list`'s, a
;; `vsubr`, is then given to `%fx26-vlambda`, a call-out: never in a leaf.
(define r-standard-value (subr rcompiles (rgen string bool) unit)
  (lambda (g name tail)
    (if (and (extract g leaf) (or (not tail) (string=? name "list")))
        (r-decline)
        (let ((made (the code (new nil))))
          (begin
            (c-standard-value name made)
            (let ((items (get made)))
              (if (or (null? items) (null? (cdr items)))
                  (r-decline)
                  (tagcase (r-next-to-oldest items)
                    (i-cell (w)
                      (begin
                        (r-op2 g rop-lambda w (wcell-int 0))
                        (if (string=? name "list")
                            (begin (r-opn g rop-setreg 1)
                                   (r-opnn g rop-prim (runtime-primitive "%fx26-vlambda") 1))
                            #u)))
                    (else y (r-decline))))))))))
;; Whether `n`, not bound in `e`, is a standard operation as a value: a
;; closure made.
(define r-standard-value? (subr rcompiles (cenv symbol) bool)
  (lambda (e n) (and (null? (c-where e n)) (c-has-standard-value? (symbol->string n)))))
;; An inlined call: which of `c-inlines`, and its global.
(define-type rinline (pairof c-inline wglobal @k))
;; Which of `c-inlines`, and its global, when `f` names one of them, taking
;; `k` arguments, whose body is not being inlined already.
(define r-inlined (subr rbuilds (renv exp int) (listof rinline @k))
  (lambda (env f k)
    (tagcase f
      (e-var (n a b)
        (let ((l (r-where env n)))
          (if (or (null? l) (c-member? (get c-inlining) n))
              nil
              (tagcase (car l)
                (rl-global (cell)
                  (let ((i (r-inline-named (get c-inlines) n k)))
                    (if (null? i) nil (the (listof rinline @k) (cons (cons (car i) cell) nil)))))
                (else y nil)))))
      (else y nil))))
;; Whether `f`, applied to `args`, is the procedure itself: its own name, or
;; a loop's.
(define r-self-call? (subr rcompiles (exp exps cenv rthis) bool)
  (lambda (f args e this)
    (tagcase f
      (e-var (n a b)
        (or (r-this-name? this n (c-count-exps args))
            (let ((l (c-find e n))) (and (not (null? l)) (c-loop? (car l))))))
      (else y #f))))
;; Whether `f`, applied to `args`, is a standard operation done in line,
;; with no call-out.
(define r-inline-op? (subr rcompiles (exp exps cenv) bool)
  (lambda (f args e)
    (tagcase (r-operator f)
      (e-var (n a b)
        (and (null? (c-where e n))
             (tagcase (r-standard (symbol->string n) (c-count-exps args))
               (s-op1 (r) #t) (s-op2 (r w z) #t) (s-op2imm (r v) #t) (s-field (k) #t)
               (s-identity () #t) (s-set () #t) (else y #f))))
      (else y #f))))
;; Whether `name` is a global in `e`, and not one whose body is being
;; inlined.
(define r-global-callee? (subr rcompiles (cenv symbol) bool)
  (lambda (e name)
    (let ((l (c-where e name)))
      (and (not (null? l))
           (and (tagcase (car l) (at-global (c) #t) (else y #f))
                (not (c-member? (get c-inlining) name)))))))

(define-rec
  ;; Whether evaluating `x` may call or call out, and so collect: a
  ;; conversion calls out.
  (r-collects (subr rcompiles (exp cenv rthis bool) bool)
    (lambda (x e this tail)
      (or (>= (c-conversion-at x) 0) (r-collects-as-is x e this tail))))
  ;; Whether evaluating `x` may call or call out, and so collect. Loops do
  ;; not; declined forms are said to, which does not matter.
  (r-collects-as-is (subr rcompiles (exp cenv rthis bool) bool)
    (lambda (x e this tail)
      (tagcase x
        (e-var (n a b)
          (and (r-standard-value? e n) (or (not tail) (string=? (symbol->string n) "list"))))
        (e-int (n a b) #f) (e-bool (v a b) #f) (e-str (v a b) #f) (e-char (v a b) #f)
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
        (e-if (t th el a b)
          (or (r-collects t e this #f) (r-collects th e this tail) (r-collects el e this tail)))
        (e-let (bs body a b)
          (or (r-collects-all (r-let-inits bs) e this) (r-collects body e this tail)))
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
          (or (r-collects s e this #f)
              (or (r-collects-arms arms e this tail) (r-collects-else els e this tail))))
        (e-app (f args a b)
          (let* ((args-collect (r-collects-all args e this))
                 ;; A loop: a call of the procedure itself, in tail position.
                 (loop-call (and tail (r-self-call? f args e this)))
                 (inline (r-inline-op? f args e)))
            (or args-collect
                (not (or loop-call (or inline (r-call-is-free? f (c-count-exps args) e tail)))))))
        (else y #t))))
  (r-collects-all (subr rcompiles (exps cenv rthis) bool)
    (lambda (es e this)
      (and (not (null? es)) (or (r-collects (car es) e this #f) (r-collects-all (cdr es) e this)))))
  (r-collects-begin (subr rcompiles (exps cenv rthis bool) bool)
    (lambda (es e this tail)
      (cond ((null? es) #f)
            ((null? (cdr es)) (r-collects (car es) e this tail))
            (else (or (r-collects (car es) e this #f) (r-collects-begin (cdr es) e this tail))))))
  (r-collects-arms (subr rcompiles (exp-arms cenv rthis bool) bool)
    (lambda (arms e this tail)
      (and (not (null? arms))
           (let ((body (extract (car arms) 4)))
             (or (r-collects body e this tail) (r-collects-arms (cdr arms) e this tail))))))
  (r-collects-else (subr rcompiles (exp-let-bs cenv rthis bool) bool)
    (lambda (els e this tail)
      (and (not (null? els)) (r-collects (extract (car els) 2) e this tail))))
  ;; Whether a call of global `f` with `n` arguments, in a body's fast
  ;; version (`r-register-code`), is no call: its own in tail position, a
  ;; loop; or one inlined, whose body makes none. As the Rust compiler's
  ;; `r_call_is_free`.
  (r-call-is-free? (subr rcompiles (exp int cenv bool) bool)
    (lambda (f n e tail)
      (and (get r-assuming)
           (tagcase f
             (e-var (name a b)
               (and (r-global-callee? e name)
                    (or (and tail (and (null? (get c-inlining)) (r-own-is? name n)))
                        (let ((i (r-inline-named (get c-inlines) name n)))
                          (and (not (null? i)) (not (r-inlined-collects? (car i) name tail)))))))
             (else y #f)))))
  ;; Whether the body of `i`, inlined procedure `name`, calls or calls out,
  ;; compiled where `r-inline` compiles it: with the globals it saw, and
  ;; itself being inlined.
  (r-inlined-collects? (subr rcompiles (c-inline symbol bool) bool)
    (lambda (i name tail)
      (let ((outer-genv (get c-genv)) (outer-inlining (get c-inlining)))
        (begin
          (set c-genv (extract i 5))
          (set c-inlining (cons name outer-inlining))
          (let* ((inner (r-local-params (the cenv nil) (extract i 3)))
                 (collects (r-collects (extract i 4) inner (the rthis nil) tail)))
            (begin (set c-inlining outer-inlining) (set c-genv outer-genv) collects))))))
  ;; Whether lambda `l`'s body, its parameters bound in `e`, calls or calls
  ;; out; anything but a lambda is said to.
  (r-body-collects? (subr rcompiles (exp cenv rthis) bool)
    (lambda (l e this)
      (tagcase l
        (e-lambda (ps lbody la lb) (r-collects lbody (r-local-params e ps) this #t))
        (else y #t))))
  ;; Whether any of `bs`' lambdas' bodies, their parameters bound in `e`,
  ;; calls or calls out.
  (r-collects-joins (subr rcompiles (exp-letrec-bs cenv rthis) bool)
    (lambda (bs e this)
      (and (not (null? bs))
           (or (let ((lam (c-lambda-of (extract (car bs) 3))))
                 (if (null? lam)
                     #t
                     (tagcase (car lam)
                       (e-rlambda (r l la lb) (r-body-collects? l e this))
                       (else y (r-body-collects? (car lam) e this)))))
               (r-collects-joins (cdr bs) e this))))))

;; Each of `inits`' flags, onto `after`: set where nothing after it calls;
;; and whether nothing from the first init on calls.
(define r-free-flags (subr rcompiles (exps cenv rthis bool bools) (pairof bools bool @k))
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
(define r-in-regs (subr rcompiles (rgen exps int cenv bool) bools)
  (lambda (g inits m te body-collects)
    (if (extract g leaf)
        (r-repeat #t (+ (c-count-exps inits) m) nil)
        (let* ((free (not body-collects))
               (flags (r-free-flags inits te (extract g this) free (r-repeat free m nil))))
          (r-budget (car flags) (get (extract g nreg)))))))

;; RESULT kept: in a register in a leaf, else in a frame slot.
(define r-place-value (subr compiles (rgen) rloc)
  (lambda (g) (r-keep g (extract g leaf))))

(define r-get (subr compiles (rgen rloc) unit)
  (lambda (g l)
    (tagcase l (rl-reg (r) (r-opn g rop-reg r)) (rl-slot (s) (r-opn g rop-stack s)) (else y #u))))

(define r-reverse-env (subr rcompiles (renv renv) renv)
  (lambda (xs acc) (if (null? xs) acc (r-reverse-env (cdr xs) (cons (car xs) acc)))))

;; A product's members, each kept, newest first.
(define r-members (subr rcompiles (rgen rloc names int renv) renv)
  (lambda (g sc xs j acc)
    (if (null? xs)
        acc
        (begin (r-get g sc) (r-opn g rop-field 3) (r-opn g rop-field (+ j 2))
               (let ((l (r-place-value g)))
                 (r-members g sc (cdr xs) (+ j 1) (r-bind (car xs) l acc)))))))

(define r-local-all (subr rcompiles (renv cenv) cenv)
  (lambda (bound te)
    (if (null? bound) te (r-local-all (cdr bound) (r-local te (car (car bound)))))))

(define r-bind-all (subr rcompiles (renv renv) renv)
  (lambda (bound env) (if (null? bound) env (r-bind-all (cdr bound) (cons (car bound) env)))))

;; Where a body finds its names: in register code, and to the cellular
;; compiler.
(define-type rscope (productof (1 renv) (2 cenv)))

;; Each value the lambda's closure captured, from the parameter's value at
;; `at`, field `j` on, kept, in order, onto `env` and `te`.
(define r-spec-free (subr rcompiles (rgen rloc syms int renv cenv bools) rscope)
  (lambda (g at fv j env te flags)
    (if (null? fv)
        (product (1 env) (2 te))
        (begin
          (tagcase at
            (rl-reg (k) (r-opn g rop-reg k))
            (rl-slot (s) (r-opn g rop-stack s))
            (else y (r-decline)))
          (r-opn g rop-field (+ cellular-closure-free0 j))
          (let ((l (r-keep g (car flags))) (n (car fv)))
            (r-spec-free g at (cdr fv) (+ j 1) (r-bind n l env) (r-local te n) (cdr flags)))))))

(define r-loop-move (subr rcompiles (rgen (listof int @k) int) unit)
  (lambda (g made i)
    (if (null? made)
        #u
        (begin
          (let ((to (+ (r-this-added g) i)))
            (if (extract g leaf)
                (r-opnn g rop-movereg (car made) (+ to 1))
                (r-slot-move g (car made) to)))
          (r-loop-move g (cdr made) (+ i 1))))))

(define r-field-args (subr rcompiles (exp-let-bs) rargs)
  (lambda (fs) (if (null? fs) nil (cons (a-e (extract (car fs) 2)) (r-field-args (cdr fs))))))

;; Each sibling where the closure being made sees it: a loop, if it is this
;; one and only called so in its body; else the slot it will be in.
(define r-sibling-env
  (subr rcompiles (exp-letrec-bs (listof int @k) int int exp int renv cenv) rscope)
  (lambda (bs at i k lbody n env te)
    (if (null? bs)
        (product (1 env) (2 te))
        (let* ((sib (extract (car bs) 1))
               (loops (and (= k i) (c-loops-only lbody sib n #t)))
               (s (r-nth-int at k)))
          (r-sibling-env (cdr bs) at i (+ k 1) lbody n
                         (r-bind sib (if loops (rl-loop) (rl-pending s)) env)
                         (the cenv (cons (cons sib (if loops (at-loop 0) (at-pending s))) te)))))))

(define r-append-arg (subr rcompiles (rargs rarg) rargs)
  (lambda (xs x) (if (null? xs) (cons x nil) (cons (car xs) (r-append-arg (cdr xs) x)))))

;; A call-out's operands, and the patches for the siblings among them.
(define-type rarg-patches (productof (1 rargs) (2 patches)))
;; `rest`, operand `x` first.
(define r-arg-onto (subr rbuilds (rarg rarg-patches) rarg-patches)
  (lambda (x rest) (product (1 (the rargs (cons x (extract rest 1)))) (2 (extract rest 2)))))

;; The same, as a call-out's operands.
(define r-free-args (subr rcompiles (syms renv int) rarg-patches)
  (lambda (fv env j)
    (if (null? fv)
        (product (1 (the rargs nil)) (2 (the patches nil)))
        (let* ((rest (r-free-args (cdr fv) env (+ j 1))) (l (r-where env (car fv))))
          (if (null? l)
              (begin (r-decline) rest)
              (tagcase (car l)
                (rl-slot (s) (r-arg-onto (a-slot s) rest))
                (rl-free (i) (r-arg-onto (a-lexical i) rest))
                (rl-pending (s)
                  (product (1 (cons (a-v (wcell-bool #f)) (extract rest 1)))
                           (2 (cons (cons j s) (extract rest 2)))))
                (rl-const (c) (r-arg-onto (a-v (r-const-cell c)) rest))
                (else y (begin (r-decline) rest))))))))

;; Each free value into REGj+1, as `lambda` wants them; a sibling not made
;; yet as `#f`, to be patched.
(define r-free-regs (subr rcompiles (rgen syms renv int) patches)
  (lambda (g fv env j)
    (if (null? fv)
        nil
        (let ((l (r-where env (car fv))) (k (+ j 1)))
          (if (null? l)
              (begin (r-decline) (the patches nil))
              (tagcase (car l)
                ;; (Moved already, `r-reg-moves`.)
                (rl-reg (r) (r-free-regs g (cdr fv) env k))
                (rl-slot (s) (begin (r-opnn g rop-load k s) (r-free-regs g (cdr fv) env k)))
                (rl-free (i) (begin (r-lexical-into g i k) (r-free-regs g (cdr fv) env k)))
                (rl-pending (s)
                  (begin (r-const-into g (wcell-bool #f) k)
                         (cons (cons j s) (r-free-regs g (cdr fv) env k))))
                (rl-const (c)
                  (begin (r-const-into g (r-const-cell c) k) (r-free-regs g (cdr fv) env k)))
                (else y (begin (r-decline) (the patches nil)))))))))

;; A join point's place: its parameters' places and its label.
(define-type rplace (pairof rlocs int @k))
;; Each binding's place, in a list; none for one that is no join point.
(define-type rplaces (listof (listof rplace @k) @k))

;; Whether a join point's parameters `ps` are kept in registers: where its
;; body makes no call (or in a leaf), so many as leave half of them.
(define r-join-in-regs? (subr rcompiles (rgen exp-params exp cenv) bool)
  (lambda (g ps lbody named)
    (or (extract g leaf)
        (and (not (r-collects lbody (r-local-params named ps) (extract g this) #t))
             (<= (+ (get (extract g nreg)) (c-count-params ps)) r-half-regs)))))

;; The place of the join point whose lambda is `lam`, in a list.
(define r-join-place (subr rcompiles (rgen exp cenv) (listof rplace @k))
  (lambda (g lam named)
    (tagcase lam
      (e-lambda (ps lbody la lb)
        (let* ((locs (r-param-places g ps (r-join-in-regs? g ps lbody named)))
               (label (r-new-label g)))
          (the (listof rplace @k) (cons (the rplace (cons locs label)) nil))))
      (else y (the (listof rplace @k) nil)))))

;; Each join point's place: its parameters' places and its label, in a
;; list; none for a binding that is not one.
(define r-join-places (subr rcompiles (rgen exp-letrec-bs bools cenv) rplaces)
  (lambda (g bs joins named)
    (if (null? bs)
        nil
        (let* ((here (if (car joins)
                         (r-join-place g (car (c-lambda-of (extract (car bs) 3))) named)
                         (the (listof rplace @k) nil)))
               (rest (r-join-places g (cdr bs) (cdr joins) named)))
          (cons here rest)))))

;; The same to the cellular compiler: a join point a loop.
(define r-letrec-te-j (subr rcompiles (exp-letrec-bs bools cenv) cenv)
  (lambda (bs joins te)
    (if (null? bs)
        te
        (let* ((n (extract (car bs) 1))
               (inner (if (car joins) (r-local-loop te n) (r-local te n))))
          (r-letrec-te-j (cdr bs) (cdr joins) inner)))))

(define r-patch-one (subr rcompiles (rgen patches int) unit)
  (lambda (g ps slot)
    (if (null? ps)
        #u
        (begin
          (r-opnn g rop-load 1 (cdr (car ps)))
          (r-opn g rop-stack slot)
          (r-opnn g rop-setfield (+ cellular-closure-free0 (car (car ps))) 1)
          (r-patch-one g (cdr ps) slot)))))

(define r-letrec-patch (subr rcompiles (rgen (listof patches @k) (listof int @k)) unit)
  (lambda (g made at)
    (if (null? made)
        #u
        (begin
          (r-patch-one g (car made) (car at))
          (r-letrec-patch g (cdr made) (cdr at))))))

;; Where a `letrec`'s name is: a join point at its place (in a list), any
;; other in frame slot `s`.
(define r-letrec-loc (subr rbuilds (int (listof rplace @k)) rloc)
  (lambda (s place)
    (if (null? place) (rl-slot s) (rl-join (car (car place)) (cdr (car place))))))

;; The `letrec`'s names where its body sees them: a join point as itself,
;; any other in its slot.
(define r-letrec-env-j (subr rcompiles (exp-letrec-bs (listof int @k) rplaces renv) renv)
  (lambda (bs at places env)
    (if (null? bs)
        env
        (r-letrec-env-j (cdr bs) (cdr at) (cdr places)
                        (r-bind (extract (car bs) 1) (r-letrec-loc (car at) (car places)) env)))))

(define r-letrec-env (subr rcompiles (exp-letrec-bs (listof int @k) renv) renv)
  (lambda (bs at env)
    (if (null? bs)
        env
        (r-letrec-env (cdr bs) (cdr at) (r-bind (extract (car bs) 1) (rl-slot (car at)) env)))))

(define r-letrec-te (subr rcompiles (exp-letrec-bs cenv) cenv)
  (lambda (bs te) (if (null? bs) te (r-letrec-te (cdr bs) (r-local te (extract (car bs) 1))))))

;;; ------------------------------------------- helpers of the compiler proper

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
        (if (string=? (symbol->string n) "nil")
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
                           (string-append "@lambda@" (int->string (exp-start lbody))))
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
      (if (null? k) nil (the wcells (cons (r-const-cell (car k)) nil))))))
