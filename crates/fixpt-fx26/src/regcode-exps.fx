;;; Register code, in FX-26: expressions, their helpers, and whether one
;;; may collect. `regcode.fx` first (PLAN.md 13h′).

;;; ---------------------------------------------------------- expressions

;; Its types (`regcode-exps-types.fx`), loaded before the module so that they are
;; not among its values; the module names what it uses of them.
(define regcode-exps-types (load-module "fx26:regcode-exps-types.fx"))
;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define regcode-exps-module (module
(define-type rspecial (select regcode-exps-types rspecial))
(define-type rown (select regcode-exps-types rown))
(define-type r-assumptions (select regcode-exps-types r-assumptions))
(define-type c-write (select regcode-exps-types c-write))
(define-type c-globals (select regcode-exps-types c-globals))
(define-type c-write-table (select regcode-exps-types c-write-table))
(define-type rown-name (select regcode-exps-types rown-name))
(define-type rinline (select regcode-exps-types rinline))
(define-type rscope (select regcode-exps-types rscope))
(define-type rarg-patches (select regcode-exps-types rarg-patches))
(define-type rplace (select regcode-exps-types rplace))
(define-type rplaces (select regcode-exps-types rplaces))

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
;; `cell` has not been written since.
(define r-guard (subr (maxeff emits spin) (rgen wglobal int) unit)
  (lambda (g cell call)
    (r-emit g (r-guard-to (wcell-global cell) (wcell-int (c-writes-expected cell)) call))))
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
  (subr (maxeff rreads (alloc @k)) ((listof c-special acyclic) symbol int int)
        (listof c-special @k))
  (lambda (xs n k lim)
    (cond ((null? xs) nil)
          ((and (symbol=? (extract (car xs) 1) n) (= (c-count-params (extract (car xs) 3)) k)
                (c-sees? lim (extract (car xs) 5)))
           (the (listof c-special @k) (cons (car xs) nil)))
          (else (r-special-named (cdr xs) n k lim)))))
;; Parameter `k` of `ps`.
(define r-nth-param (subr (read @globals) (exp-params int) symbol)
  (lambda (ps k) (if (= k 0) (extract (car ps) 1) (r-nth-param (cdr ps) (- k 1)))))
;; Whether `body` is small enough to inline (`c-inline-limit`).
(define r-inlinable? (subr (maxeff (read @globals) spin) (exp) bool)
  (lambda (body) (>= (c-inline-room body c-inline-limit) 0)))
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
                      (let ((sp (r-special-named (get c-specials) n (c-count-exps args)
                                                 (get c-genv))))
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
(define r-assuming (ref bool @k) (new #f))
;; While deciding whether a body is a leaf: whether a plain call in tail
;; position, its arguments collecting nothing, counts as no call
;; (`r-leaf-tail-call`). As the Rust compiler's `tail_calls_leave`.
(define r-tail-calls-leave (ref bool @k) (new #f))
;; Whether a call of itself through its global was made a loop, in the body
;; being compiled's fast version.
(define r-looped (ref bool @k) (new #f))
(define r-assumed (ref r-assumptions @k) (new nil))
(define c-writes (ref c-write-table @k) (new (make-table symbol-hash symbol=?)))
(define c-writes-of (subr rreads (wglobal) (listof c-write @k))
  (lambda (g) (table-ref (get c-writes) (wglobal-name g) (the (listof c-write @k) nil))))
(define c-form-writes (ref c-globals @k) (new nil))
(define c-writes-in (subr rscans ((listof c-write @k) wglobal) int)
  (lambda (xs g)
    (cond ((null? xs) (wglobal-writes g))
          ((wglobal=? (car (car xs)) g) (cdr (car xs)))
          (else (c-writes-in (cdr xs) g)))))
(define c-count-in (subr rscans (c-globals wglobal int) int)
  (lambda (xs g n) (if (null? xs) n (c-count-in (cdr xs) g (if (wglobal=? (car xs) g) (+ n 1) n)))))
;; What a `global-guard` of `g` made now expects: how many times `g` has
;; been written once the form being compiled has run, its own writes too.
;; As the Rust compiler's `writes_expected`.
(define c-writes-expected (subr rscans (wglobal) int)
  (lambda (g) (c-count-in (get c-form-writes) g (c-writes-in (c-writes-of g) g))))
(define c-without-one (subr rbuilds (c-globals wglobal) c-globals)
  (lambda (xs g)
    (cond ((null? xs) xs)
          ((wglobal=? (car xs) g) (cdr xs))
          (else (the c-globals (cons (car xs) (c-without-one (cdr xs) g)))))))
;; A `global!` of `g` emitted: once it runs, `g` written once more.
(define c-wrote! (subr (maxeff emits spin) (wglobal) unit)
  (lambda (g)
    (let* ((ws (c-writes-of g)) (n (+ (c-writes-in ws g) 1)))
      (begin
        (table-set! (get c-writes) (wglobal-name g)
                    (the (listof c-write @k) (cons (the c-write (cons g n)) ws)))
        (set c-form-writes (c-without-one (get c-form-writes) g))))))
(define r-assumed-has? (subr rreads (r-assumptions wglobal) bool)
  (lambda (xs cell)
    (and (not (null? xs)) (or (wglobal=? (car xs) cell) (r-assumed-has? (cdr xs) cell)))))
;; Whether the body being compiled is its fast version, which assumes what
;; the guard would test: if so, the assumption noted, for its guard at the
;; start.
(define r-assume (subr emits (wglobal) bool)
  (lambda (cell)
    (if (get r-assuming)
        (begin (if (r-assumed-has? (get r-assumed) cell)
                   #u
                   (set r-assumed (the r-assumptions (cons cell (get r-assumed)))))
               #t)
        #f)))
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
        (let ((rest (the wcells (cons (wcell-int (- plain-at (+ at 4)))
                                      (r-guard-cells (cdr xs) (+ at 4) plain-at rest))))
              (c (wcell-global (car xs)))
              (n (wcell-int (c-writes-expected (car xs)))))
          (the wcells (cons (wcell-int rop-global-guard) (cons c (cons n rest))))))))
;; The names `e` binds, in order.
(define r-cenv-names (subr rbuilds (cenv) syms)
  (lambda (e) (if (null? e) nil (cons (car (car e)) (r-cenv-names (cdr e))))))
;; The constant globals `body` names, in its free names' order (`c-free`),
;; each cell and value: what a fast version folds, assuming each holds its
;; value still. As the Rust compiler's `r_consts_named`.
(define r-consts-named (subr rbuilds (exp cenv) r-const-list)
  (lambda (body inner)
    (letrec ((go (subr rbuilds (syms r-const-list) r-const-list)
                   (lambda (ns acc)
                     (if (null? ns)
                         (r-rev-consts-list acc nil)
                         (let ((l (c-where (the cenv nil) (car ns))))
                           (go (cdr ns)
                               (if (null? l)
                                   acc
                                   (tagcase (car l)
                                     (at-global (g)
                                       (let ((k (r-const-in (get r-const-globals) g)))
                                         (if (or (null? k) (not (null? (r-const-in acc g))))
                                             acc
                                             (the r-const-list (cons (cons g (car k)) acc)))))
                                     (else y acc)))))))))
      (go (c-free body (r-cenv-names inner) nil) nil))))
(define r-rev-consts-list (subr rbuilds (r-const-list r-const-list) r-const-list)
  (lambda (xs acc)
    (if (null? xs) acc (r-rev-consts-list (cdr xs) (the r-const-list (cons (car xs) acc))))))
;; Constants `cs` as assumptions, newest first: onto `acc`, the last first.
(define r-consts-assumed (subr rbuilds (r-const-list r-assumptions) r-assumptions)
  (lambda (cs acc)
    (if (null? cs)
        acc
        (r-consts-assumed (cdr cs) (the r-assumptions (cons (car (car cs)) acc))))))
;; The one of `c-inlines` that `n`, taking `k` arguments, names, if any.
(define r-inline-named
  (subr (maxeff rreads (alloc @k)) ((listof c-inline acyclic) symbol int int)
        (listof c-inline acyclic))
  (lambda (xs n k lim)
    (cond ((null? xs) nil)
          ((and (symbol=? (extract (car xs) 1) n) (= (c-count-params (extract (car xs) 3)) k)
                (c-sees? lim (extract (car xs) 5)))
           (the (listof c-inline acyclic) (cons (car xs) nil)))
          (else (r-inline-named (cdr xs) n k lim)))))
;; A standard operation as a value, into RESULT: its closure, of the word
;; the stack code made for it (`c-standard-word`), and that word's
;; register code. A leaf makes it only in tail position. `list`'s, a
;; `vsubr`, is then given to `%fx26-vlambda`, a call-out: never in a leaf.
(define r-standard-value (subr rcompiles (rgen string bool) unit)
  (lambda (g name tail)
    (let ((found (c-standard-word-of name)))
      (if (or (null? found) (and (extract g leaf) (or (not tail) (string=? name "list"))))
          (r-decline)
          (begin
            (r-op2 g rop-lambda (wcell-word (car found)) (wcell-int 0))
            (if (string=? name "list")
                (begin (r-opn g rop-setreg 1)
                       (r-opnn g rop-prim (runtime-primitive "%fx26-vlambda") 1))
                #u))))))
;; Whether `n`, not bound in `e`, is a standard operation as a value: a
;; closure made.
(define r-standard-value? (subr rcompiles (cenv symbol) bool)
  (lambda (e n) (and (null? (c-where e n)) (c-has-standard-value? (symbol->string n)))))
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
                  (let ((i (r-inline-named (c-inlines-of n) n k (get c-genv))))
                    (if (null? i) nil (the (listof rinline @k) (cons (cons (car i) cell) nil)))))
                (else y nil)))))
      (else y nil))))
;; The global `f` names here, in a list; none if it names none.
(define r-global-of (subr rbuilds (renv exp) (listof wglobal @k))
  (lambda (env f)
    (tagcase f
      (e-var (n fa fb)
        (let ((l (r-where env n)))
          (if (null? l)
              nil
              (tagcase (car l)
                (rl-global (cell) (the (listof wglobal @k) (cons cell nil)))
                (else y nil)))))
      (else y nil))))
;; Call `f` at `a`-`b`: the small procedure it is inlined as, and its
;; global, as the plan decided (step 3), in a planned lambda's own code;
;; else as `r-inlined` decides here, in an inlined body or a copy.
(define r-inline-of (subr rbuilds (int int renv exp int) (listof rinline @k))
  (lambda (a b env f k)
    (let ((p (c-planned-call a b)))
      (if (null? p)
          (r-inlined env f k)
          (let ((i (extract (car p) 1)) (g (r-global-of env f)))
            (if (or (null? i) (null? g))
                nil
                (the (listof rinline @k) (cons (cons (car i) (car g)) nil))))))))
;; The same for the procedure it is specialized as, with the lambda.
(define r-special-of (subr rbuilds (int int renv exp exps) (listof rspecial @k))
  (lambda (a b env f args)
    (let ((p (c-planned-call a b)))
      (if (null? p)
          (r-specialized env f args)
          (let ((s (extract (car p) 2)) (g (r-global-of env f)))
            (if (or (null? s) (null? g))
                nil
                (the (listof rspecial @k)
                     (cons (product (1 (extract (car s) 1)) (2 (car g)) (3 (extract (car s) 2)))
                           nil))))))))
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
               (s-identity () #t) (s-set () #t) (s-pure (p) #t) (else y #f))))
      (else y #f))))
;; Whether `name` is a global in `e`, and not one whose body is being
;; inlined.
(define r-global-callee? (subr rcompiles (cenv symbol) bool)
  (lambda (e name)
    (let ((l (c-where e name)))
      (and (not (null? l))
           (and (tagcase (car l) (at-global (c) #t) (else y #f))
                (not (c-member? (get c-inlining) name)))))))

;; Whether a call of `f` with `n` arguments is a plain `invoke`: not a
;; standard operation, an inlined or specialized global's, or a lifted
;; procedure's, each compiled its own way. As `r_plain_callee`.
(define r-plain-callee? (subr rcompiles (exp int cenv) bool)
  (lambda (f n e)
    (tagcase f
      (e-var (name a b)
        (let ((l (c-where e name)))
          (and (not (null? l))
               (tagcase (car l)
                 (at-global (c)
                   (and (null? (r-inline-named (c-inlines-of name) name n (get c-genv)))
                        (null? (r-special-named (get c-specials) name n (get c-genv)))))
                 (at-slot (i) #t)
                 (at-free (i) #t)
                 (else y #f)))))
      (else y #t))))

(define-rec
  ;; Whether evaluating `x` may call or call out, and so collect: a
  ;; conversion calls out.
  (r-collects (subr rcompiles (exp cenv rthis bool) bool)
    (lambda (x e this tail)
      (or (c-changed? x) (r-collects-as-is x e this tail))))
  ;; Whether evaluating `x` may call or call out, and so collect. Loops do
  ;; not; declined forms are said to, which does not matter.
  (r-collects-as-is (subr rcompiles (exp cenv rthis bool) bool)
    (lambda (x e this tail)
      (tagcase x
        (e-var (n a b)
          (and (r-standard-value? e n) (or (not tail) (string=? (symbol->string n) "list"))))
        (e-int (n a b) #f) (e-bool (v a b) #f) (e-str (v a b) #f) (e-char (v a b) #f)
        (e-float (v a b) #f)
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
                 (inline (r-inline-op? f args e))
                 (n (c-count-exps args))
                 ;; A plain call in tail position, deciding a leaf: nothing
                 ;; is used after it, so it needs no frame.
                 (leaves (and (get r-tail-calls-leave)
                              (and tail
                                   (and (< n register-regs)
                                        (and (r-plain-callee? f n e)
                                             (not (r-collects f e this #f))))))))
            (or args-collect
                (not (or loop-call (or inline (or leaves (r-call-is-free? f n e tail))))))))
        ;; A `with` only loads fields (`r-with`): as its body. `(with #%fx n)`:
        ;; as the standard `n` as a value.
        (e-with (m body a b)
          (let ((ns (c-with-at a b)) (n (c-fx-name m body)))
            (if (string=? n "")
                (r-collects body (if (null? ns) e (r-local-syms e (car ns))) this tail)
                (and (c-has-standard-value? n) (or (not tail) (string=? n "list"))))))
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
                        (let ((i (r-inline-named (c-inlines-of name) name n (get c-genv))))
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
               (r-collects-joins (cdr bs) e this))))))))

(define r-spec-at (with regcode-exps-module r-spec-at))
(define r-spec-start (with regcode-exps-module r-spec-start))
(define r-guard (with regcode-exps-module r-guard))
(define r-invoke (with regcode-exps-module r-invoke))
(define r-keep-in-reg (with regcode-exps-module r-keep-in-reg))
(define r-keep-in-slot (with regcode-exps-module r-keep-in-slot))
(define r-keep (with regcode-exps-module r-keep))
(define r-const-into (with regcode-exps-module r-const-into))
(define r-lexical-into (with regcode-exps-module r-lexical-into))
(define r-nth-param (with regcode-exps-module r-nth-param))
(define r-specialized (with regcode-exps-module r-specialized))
(define r-spec-param? (with regcode-exps-module r-spec-param?))
(define r-spec-self? (with regcode-exps-module r-spec-self?))
(define r-local-names (with regcode-exps-module r-local-names))
(define r-let-inits (with regcode-exps-module r-let-inits))
(define r-local-params (with regcode-exps-module r-local-params))
(define r-local-syms (with regcode-exps-module r-local-syms))
(define r-drop-bools (with regcode-exps-module r-drop-bools))
(define-type rown (select regcode-exps-module rown))
(define r-own-now (with regcode-exps-module r-own-now))
(define r-own-self (with regcode-exps-module r-own-self))
(define r-join-flags (with regcode-exps-module r-join-flags))
(define r-all? (with regcode-exps-module r-all?))
(define r-join-of (with regcode-exps-module r-join-of))
(define c-length-locs (with regcode-exps-module c-length-locs))
(define r-jump-moves (with regcode-exps-module r-jump-moves))
(define r-bind-places (with regcode-exps-module r-bind-places))
(define r-letrec-slots-j (with regcode-exps-module r-letrec-slots-j))
(define-type r-assumptions (select regcode-exps-module r-assumptions))
(define r-assuming (with regcode-exps-module r-assuming))
(define r-tail-calls-leave (with regcode-exps-module r-tail-calls-leave))
(define r-looped (with regcode-exps-module r-looped))
(define r-assumed (with regcode-exps-module r-assumed))
(define r-assume (with regcode-exps-module r-assume))
(define c-writes (with regcode-exps-module c-writes))
(define c-form-writes (with regcode-exps-module c-form-writes))
(define c-writes-expected (with regcode-exps-module c-writes-expected))
(define c-wrote! (with regcode-exps-module c-wrote!))
(define-type rown-name (select regcode-exps-module rown-name))
(define r-own-name (with regcode-exps-module r-own-name))
(define r-self-moves (with regcode-exps-module r-self-moves))
(define r-slot-args-of (with regcode-exps-module r-slot-args-of))
(define r-cells-length (with regcode-exps-module r-cells-length))
(define r-rev-cells (with regcode-exps-module r-rev-cells))
(define r-rev-assumptions (with regcode-exps-module r-rev-assumptions))
(define r-assumptions-length (with regcode-exps-module r-assumptions-length))
(define r-guard-cells (with regcode-exps-module r-guard-cells))
(define r-consts-named (with regcode-exps-module r-consts-named))
(define r-consts-assumed (with regcode-exps-module r-consts-assumed))
(define r-standard-value (with regcode-exps-module r-standard-value))
(define r-inlined (with regcode-exps-module r-inlined))
(define r-collects (with regcode-exps-module r-collects))
(define-type rscope (select regcode-exps-module rscope))
(define-type rplaces (select regcode-exps-module rplaces))
(define-type rinline (select regcode-exps-module rinline))
(define r-inline-of (with regcode-exps-module r-inline-of))
(define r-inline-named (with regcode-exps-module r-inline-named))
(define r-special-of (with regcode-exps-module r-special-of))
(define r-budget (with regcode-exps-module r-budget))
(define r-half-regs (with regcode-exps-module r-half-regs))
(define r-local-loop (with regcode-exps-module r-local-loop))
(define r-param-places (with regcode-exps-module r-param-places))
(define r-repeat (with regcode-exps-module r-repeat))
(define r-slot-move (with regcode-exps-module r-slot-move))
