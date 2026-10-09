;;; Register code, in FX-26: specialized procedures' temporaries, and the
;;; entry. After `regcode-core.fx`.

;; Its types (`regcode-entry-types.fx`), loaded before the module so that they are
;; not among its values; the module names what it uses of them.
(define regcode-entry-types (load-module "fx26:regcode-entry-types.fx"))
;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define regcode-entry-module (module
(define-type rowner (select regcode-entry-types rowner))
(define-type rgens (select regcode-entry-types rgens))

;; Each argument into a frame slot of its own, in order: the slots.
(define r-spec-temps (subr rcompiles (rgen exps renv cenv) rints)
  (lambda (g args env te)
    (if (null? args)
        nil
        (let* ((s (begin (r-exp g (car args) env te #f) (r-keep-in-slot g)))
               (rest (r-spec-temps g (cdr args) env te)))
          (cons s rest)))))

;;; ------------------------------------------------------------ the entry

;; The register environment of a lambda's body, from its cellular one: its
;; parameters in registers in a leaf, else in the frame.
(define r-env-of (subr (maxeff emits spin) (cenv bool) renv)
  (lambda (inner leaf)
    (if (null? inner)
        nil
        (let ((rest (r-env-of (cdr inner) leaf)) (n (car (car inner))))
          (tagcase (cdr (car inner))
            (at-slot (i) (r-bind n (if leaf (rl-reg (+ i 1)) (rl-slot i)) rest))
            (at-free (i) (r-bind n (rl-free i) rest))
            (at-loop (z) (r-bind n (rl-loop) rest))
            (at-global (g) (r-bind n (rl-global g) rest))
            (at-pending (s) (begin (r-decline) rest))
            (at-lifted (k) (r-bind n (rl-lifted k) rest)))))))

;; The car or cdr (`op`) of the list in the last register, into RESULT.
(define r-last-list-op (subr emits (rgen int) unit)
  (lambda (g op) (begin (r-opn g rop-reg register-regs) (r-opn g rop-op1 op))))
;; The first of the parameters past the registers, in a list in the last,
;; into frame slot `s`; the list then its rest, if there are `more`.
(define r-store-rest (subr emits (rgen int bool) unit)
  (lambda (g s more)
    (begin
      (r-last-list-op g routine-pair-car)
      (r-opn g rop-setstk s)
      (if more (begin (r-last-list-op g routine-pair-cdr) (r-opn g rop-setreg register-regs)) #u))))
;; Parameters `i` on, of `n`, each into a frame slot of its own.
(define r-store-params (subr (maxeff emits spin) (rgen int int) unit)
  (lambda (g i n)
    (if (= i n)
        #u
        (let ((s (r-slot g)))
          (begin
            (if (or (<= n register-regs) (< (+ i 1) register-regs))
                (r-opnn g rop-store (+ i 1) s)
                (r-store-rest g s (< (+ i 1) n)))
            (r-store-params g (+ i 1) n))))))

;; The name of the definition `own` (in a list), and `n`, its procedure's
;; arity, in a list.
(define r-own-name-of (subr (maxeff rreads (alloc @k)) (rowner int) (listof rown-name @k))
  (lambda (own n)
    (if (null? own) nil (cons (the rown-name (cons (extract (car own) 1) n)) nil))))

;; Whether a fast version may be worth compiling, asked before it is, as the
;; Rust compiler's `r_fast_may_pay` says: whether, with inlined calls no
;; calls, the body would be a leaf; or it mentions its own name, and so may
;; loop.
(define r-fast-may-pay? (subr rcompiles (exp-params exp cenv rthis rowner) bool)
  (lambda (ps body inner this own)
    (or (and (not (null? own)) (c-mentions? body (extract (car own) 1)))
        (let ((outer-assuming (get r-assuming)) (outer-name (get r-own-name)))
          (begin
            (set r-assuming #t)
            (set r-own-name (r-own-name-of own (c-count-params ps)))
            (let ((leaf (not (r-collects body inner this #t))))
              (begin (set r-assuming outer-assuming) (set r-own-name outer-name) leaf)))))))
;; A new maker of register code: no items yet; a leaf or not; `nreg`
;; registers taken, `labels` labels; for procedure `this` (one or none).
(define r-new-gen (subr (maxeff rreads (alloc @k)) (bool int int rthis) rgen)
  (lambda (leaf nreg labels this)
    (the rgen
      (product (items (new (the ritems nil))) (leaf leaf) (nreg (new nreg)) (nslot (new 0))
               (mslot (new 0)) (labels (new labels)) (this this) (start 0)))))
;; The labels at a body's start, the frame made: the procedure's own (0),
;; for its loops, if it knows itself; one where a procedure specialized at
;; a lambda starts (`spec-at`), and where the parameter the lambda is; and
;; one where a top-level definition's procedure starts (`own-at`), for its
;; calls of itself.
(define r-starts (subr rcompiles (rgen renv rthis rowner int int int) unit)
  (lambda (g env this own n spec-at own-at)
    (begin
      (if (null? this) #u (r-emit g (r-label 0)))
      (if (null? (get c-spec-now))
          #u
          (let ((l (r-where env (extract (car (get c-spec-now)) 5))))
            (if (null? l)
                (r-decline)
                (begin (set r-spec-at (the rlocs (cons (car l) nil)))
                       (set r-spec-start spec-at)
                       (r-emit g (r-label spec-at))))))
      (if (null? own)
          #u
          (let* ((o (car own))
                 (me (product (1 (extract o 1)) (2 (extract o 2)) (3 n) (4 own-at))))
            (begin (set r-own-now (cons me nil)) (r-emit g (r-label own-at))))))))
;; What a body's register code starts from, made afresh for each try.
(define r-body-reset! (subr rcompiles (rowner int) unit)
  (lambda (own n)
    (begin
      (set r-declined #f)
      (set r-looped #f)
      (set r-spec-at (the rlocs nil))
      (set r-own-now (the (listof rown @k) nil))
      (set r-own-name (r-own-name-of own n)))))
;; The body as a leaf, or not, as `leaf` says (`r-register-body`).
(define r-register-body-as (subr rcompiles (exp-params exp cenv rthis rowner bool) rgens)
  (lambda (ps body inner this own leaf)
    (let ((n (c-count-params ps)))
      (begin
        (r-body-reset! own n)
        (let* ((spec-at (if (null? this) 0 1))
               (own-at (+ spec-at (if (null? (get c-spec-now)) 0 1)))
               (g (r-new-gen leaf 0 (+ own-at (if (null? own) 0 1)) this)))
          (begin
            (r-opn g rop-args n)
            (let ((env (r-env-of inner leaf)))
              (begin
                (if leaf
                    (set (extract g nreg) n)
                    (begin (r-op0 g rop-save) (r-emit g (r-frame)) (r-store-params g 0 n)))
                (r-starts g env this own n spec-at own-at)
                (r-exp g body env inner #t)
                (if (get r-declined) (the rgens nil) (the rgens (cons g nil)))))))))))
;; Whether `body` is a leaf once plain tail calls count as no call.
(define r-leaves? (subr rcompiles (exp cenv rthis) bool)
  (lambda (body inner this)
    (begin
      (set r-tail-calls-leave #t)
      (let ((l (not (r-collects body inner this #t)))) (begin (set r-tail-calls-leave #f) l)))))
;; A lambda's body in register code, not yet assembled, in a list; none where
;; this compiler declines. In a fast version, where a call inlined or of
;; itself in tail position is no call, a leaf maybe where the plain one is
;; not. A leaf too where its only calls are plain tail calls: made so
;; first, and if that declines (out of registers), made as before. As the
;; Rust compiler's `register_body_in`.
(define r-register-body (subr rcompiles (exp-params exp cenv rthis rowner) rgens)
  (lambda (ps body inner this own)
    (let ((n (c-count-params ps)))
      (begin
        (r-body-reset! own n)
        ;; Past `register-regs` parameters, the rest come as a list in the
        ;; last register, taken apart into the frame.
        (let ((leaf (and (<= n register-regs) (not (r-collects body inner this #t)))))
          (if (or leaf (> n register-regs) (not (r-leaves? body inner this)))
              (r-register-body-as ps body inner this own leaf)
              (let ((gs (r-register-body-as ps body inner this own #t)))
                (if (null? gs) (r-register-body-as ps body inner this own #f) gs))))))))
;; The body compiled once, as ever.
(define r-plain-code (subr rcompiles (exp-params exp cenv rthis rowner) wcells)
  (lambda (ps body inner this own)
    (let ((g (r-register-body ps body inner this own)))
      (if (null? g) (the wcells nil) (r-assemble (car g))))))
;; The two versions as one: `args n`, the guards, the fast body, the plain
;; one; both with the larger frame.
(define r-versions (subr rcompiles (rgen rgen r-assumptions) wcells)
  (lambda (fast plain assumptions)
    (let* ((f (get (extract fast mslot))) (p (get (extract plain mslot)))
           (frame (if (> f p) f p)))
      (begin
        (set (extract fast mslot) frame)
        (set (extract plain mslot) frame)
        (let* ((fc (r-assemble fast)) (pc (r-assemble plain))
               (guards (* 4 (r-assumptions-length assumptions 0)))
               (plain-at (+ 2 (+ guards (- (r-cells-length fc 0) 2))))
               (bodies (r-rev-cells (r-rev-cells (cdr (cdr fc)) nil) (cdr (cdr pc)))))
          (cons (car fc) (cons (car (cdr fc)) (r-guard-cells assumptions 2 plain-at bodies))))))))
;; Register code for a standard operation as a value (`c-standard-value`),
;; as the Rust compiler's `r_standard_word`: its operands are its
;; parameters, in REG1…REGn already, and a call-out, if it is one, is made in
;; a frame. None for one done in several instructions, or that takes
;; control (the closure then has stack code only).
(define r-standard-word (subr rcompiles (string int) wcells)
  (lambda (name n)
    (let* ((std (r-standard name n))
           (callout (tagcase std (s-prim (p) #t) (s-cellular (r) (= r routine-cons)) (else y #f)))
           (g (r-new-gen (not callout) n 0 (the rthis nil)))
           (none (the wcells nil)))
      (begin
        (r-opn g rop-args n)
        (if callout (begin (r-op0 g rop-save) (r-emit g (r-frame))) #u)
        (let ((made
               (tagcase std
                 (s-op2 (r swap negate)
                   (begin (r-opn g rop-reg (if swap 2 1))
                          (r-opnn g rop-op2 r (if swap 1 2))
                          (if negate (r-negate g) #u)
                          #t))
                 (s-op1 (r) (begin (r-opn g rop-reg 1) (r-opn g rop-op1 r) #t))
                 (s-op2imm (r v) (begin (r-opn g rop-reg 1) (r-op2imm g r v) #t))
                 (s-field (k) (begin (r-opn g rop-reg 1) (r-opn g rop-field k) #t))
                 (s-identity () (begin (r-opn g rop-reg 1) #t))
                 (s-prim (p) (begin (r-opnn g rop-prim p n) #t))
                 (s-pure (p)
                   (begin (r-opn g rop-reg 1)
                          (if (= n 1) (r-opn g rop-prim1 p) (r-opnn g rop-prim2 p 2))
                          #t))
                 (s-cellular (r) (if callout (begin (r-opnn g rop-cellular r n) #t) #f))
                 (else y #f))))
          (if made (begin (r-done g #t) (r-assemble g)) none))))))
;; Whether a fast version of `body` is sound, as far as the body itself
;; says: no global can change during a run of it (its effect summary is
;; less than 3); and it makes no closure (`c-room`, a `with`'s body
;; counted, as it only loads fields).
(define r-fast-sound? (subr rcompiles (exp) bool)
  (lambda (body)
    (and (< (c-summary-at (exp-start body) (exp-end body)) 3)
         (>= (c-room body 1000000000 #t) 0))))
;; Whether the fast version made (`fast`, in a list) pays: it is a leaf, or
;; it loops.
(define r-pays? (subr rreads (rgens) bool)
  (lambda (fast) (and (not (null? fast)) (or (extract (car fast) leaf) (get r-looped)))))
;; A lambda's body compiled assuming every global it inlines, specializes
;; or calls itself through holds what it held when compiled, behind one
;; guard for each at its start; and, where a guard fails, compiled as ever.
;; Worth it where the fast version is a leaf, or loops where the plain one
;; calls: else its guards, all run on entry, cost more than the plain
;; version's, each run where its call is; and then the plain one alone.
(define r-fast-code (subr rcompiles (exp-params exp cenv rthis rowner) wcells)
  (lambda (ps body inner this own)
    (let* ((outer-assuming (get r-assuming)) (outer-assumed (get r-assumed))
           (outer-consts (get r-consts-now))
           ;; The constants it names folded, assumed first.
           (consts (r-consts-named body inner))
           (fast (begin (set r-assuming #t)
                        (set r-assumed (r-consts-assumed consts (the r-assumptions nil)))
                        (set r-consts-now consts)
                        (r-register-body ps body inner this own)))
           (assumptions (r-rev-assumptions (get r-assumed) (the r-assumptions nil))))
      (begin
        (set r-consts-now outer-consts)
        (set r-assuming outer-assuming)
        (set r-assumed outer-assumed)
        (if (or (null? assumptions) (not (r-pays? fast)))
            (r-plain-code ps body inner this own)
            (let* ((plain (r-register-body ps body inner this own))
                   (none (the wcells nil)))
              (if (null? plain) none (r-versions (car fast) (car plain) assumptions))))))))
;; A lambda's register code, whose closure captures what `inner` says, or
;; none where this compiler declines: in two versions where that is sound
;; and something is gained, as the Rust compiler's `register_code` says. Its
;; body compiled assuming every global it inlines, specializes or calls
;; itself through holds what it held when compiled, behind one guard for
;; each at its start; and, where a guard fails, compiled as ever. Sound where
;; no global can change during a run of the body: its effect summary is less
;; than 3. Only where the body makes no closure, so that compiling it twice
;; compiles nothing else twice.
(define r-register-code (subr rcompiles (exp-params exp cenv rthis) wcells)
  (lambda (ps body inner this)
    (let ((outer (get r-declined))
          (outer-at (get r-spec-at)) (outer-start (get r-spec-start))
          (outer-own (get r-own-now)) (outer-name (get r-own-name)) (own (get c-own-now)))
      (begin
        (set c-own-now (the rowner nil))
        (let ((cells (if (and (r-fast-sound? body) (r-fast-may-pay? ps body inner this own))
                         (r-fast-code ps body inner this own)
                         (r-plain-code ps body inner this own))))
          (begin (set r-declined outer) (set r-spec-at outer-at) (set r-spec-start outer-start)
                 (set r-own-now outer-own) (set r-own-name outer-name)
                 cells))))))


;; Whether the compiler makes register code from now on: for a driver.
(define compile-registers! (subr (maxeff (read @globals) (write @k)) (bool) unit)
  (lambda (on) (set c-registers on)))))

(define r-standard-word (with regcode-entry-module r-standard-word))
(define r-register-code (with regcode-entry-module r-register-code))
(define compile-registers! (with regcode-entry-module compile-registers!))
