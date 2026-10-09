;;; Register code, written in FX-26: where values live, in registers or
;;; frame slots; the environments of lambdas, fields and specialized copies;
;;; and the places of a `letrec`'s lambdas. After `regcode-exps.fx` (split
;;; from that file, `TODO.md` §68).

;; Its types (`regcode-exps-types.fx`, its file's before it), loaded before
;; the module so that they are not among its values; the module names what
;; it uses of them.
(define regcode-exps-types (load-module "fx26:regcode-exps-types.fx"))
;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define regcode-places-module (module
(define-type rscope (select regcode-exps-types rscope))
(define-type rarg-patches (select regcode-exps-types rarg-patches))
(define-type rplace (select regcode-exps-types rplace))
(define-type rplaces (select regcode-exps-types rplaces))

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
  (lambda (bs te) (if (null? bs) te (r-letrec-te (cdr bs) (r-local te (extract (car bs) 1))))))))

(define r-in-regs (with regcode-places-module r-in-regs))
(define r-place-value (with regcode-places-module r-place-value))
(define r-get (with regcode-places-module r-get))
(define r-reverse-env (with regcode-places-module r-reverse-env))
(define r-members (with regcode-places-module r-members))
(define r-local-all (with regcode-places-module r-local-all))
(define r-bind-all (with regcode-places-module r-bind-all))
(define r-spec-free (with regcode-places-module r-spec-free))
(define r-loop-move (with regcode-places-module r-loop-move))
(define r-field-args (with regcode-places-module r-field-args))
(define r-sibling-env (with regcode-places-module r-sibling-env))
(define r-append-arg (with regcode-places-module r-append-arg))
(define r-free-args (with regcode-places-module r-free-args))
(define r-free-regs (with regcode-places-module r-free-regs))
(define r-join-places (with regcode-places-module r-join-places))
(define r-letrec-te-j (with regcode-places-module r-letrec-te-j))
(define r-letrec-patch (with regcode-places-module r-letrec-patch))
(define r-letrec-env-j (with regcode-places-module r-letrec-env-j))
