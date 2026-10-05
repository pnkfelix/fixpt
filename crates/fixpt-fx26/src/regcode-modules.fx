;;; Register code, in FX-26: modules (`docs/research/first-class-modules.md`,
;;; stage M3), as the Rust compiler's `r_module` and `r_with` make them.
;;; After `regcode-core.fx`, which reaches them through `r-module-code`.

;; Where names are, to register code and to the cellular compiler.
(define-type r-scopes (pairof renv cenv @k))

;; `vals`, newest first, onto `acc` the oldest first: as operands.
(define r-slots-oldest (subr rbuilds (rints rargs) rargs)
  (lambda (vals acc)
    (if (null? vals) acc (r-slots-oldest (cdr vals) (the rargs (cons (a-slot (car vals)) acc))))))

;; A frame slot for each of `vs`, in order, by name.
(define r-module-slots (subr (maxeff emits spin) (rgen c-mvals) c-mslots)
  (lambda (g vs)
    (if (null? vs)
        nil
        (let ((s (r-slot g))) (cons (cons (extract (car vs) 1) s) (r-module-slots g (cdr vs)))))))
;; Item `n`'s lambda's scopes while it is made: each of `later` pending, and
;; itself a loop if it only calls itself in loops.
(define r-module-own (subr rcompiles (symbol r-scopes c-mslots exp int) r-scopes)
  (lambda (n sc later lbody nps)
    (if (null? later)
        sc
        (let* ((m (car (car later))) (s (cdr (car later)))
               (loops (and (symbol=? m n) (c-loops-only lbody n nps #t)))
               (env (r-bind m (if loops (rl-loop) (rl-pending s)) (car sc)))
               (te (the cenv (cons (cons m (if loops (at-loop 0) (at-pending s))) (cdr sc)))))
          (r-module-own n (the r-scopes (cons env te)) (cdr later) lbody nps)))))
;; Item `n`'s lambda `x`, naming items of `later` not made yet: those
;; captured as a `letrec`'s siblings are, to be given once made.
(define r-module-closure (subr rcompiles (rgen symbol exp r-scopes c-mslots) patches)
  (lambda (g n x sc later)
    (let ((self (the syms (cons n nil))))
      (tagcase (car (c-lambda-of x))
        (e-lambda (ps lbody a b)
          (let ((own (r-module-own n sc later lbody (c-count-params ps))))
            (r-lambda g ps lbody (car own) (cdr own) self (the maybe-exp nil) #f)))
        (e-rlambda (r l a b)
          (tagcase l
            (e-lambda (ps lbody la lb)
              (let ((own (r-module-own n sc later lbody (c-count-params ps))))
                (r-lambda g ps lbody (car own) (cdr own) self (r-just-exp r) #f)))
            (else y (begin (r-decline) (the patches nil)))))
        (else y (begin (r-decline) (the patches nil)))))))
;; Each closure of `ws` waiting for slot `s`, given it.
(define r-give-waiting (subr rcompiles (rgen c-waits int) unit)
  (lambda (g ws s)
    (if (null? ws)
        #u
        (let ((w (car ws)))
          (begin
            (if (= (extract w 3) s)
                (begin (r-opnn g rop-load 1 s)
                       (r-opn g rop-stack (extract w 1))
                       (r-opnn g rop-setfield (+ cellular-closure-free0 (extract w 2)) 1))
                #u)
            (r-give-waiting g (cdr ws) s))))))
;; Values `vs` made in their slots, `later`, in order, as a `letrec*`'s
;; (`DONE.md` §37): a typed lambda naming an item not made yet captures it
;; once it is made; `ws` the closures waiting, `vals` the values' slots so
;; far (newest first): all of them.
(define r-module-make (subr rcompiles (rgen c-mvals r-scopes c-mslots c-waits rints) rints)
  (lambda (g vs sc later ws vals)
    (if (null? vs)
        vals
        (let* ((v (car vs)) (n (extract v 1)) (x (extract v 2)) (s (cdr (car later)))
               (ps (if (and (extract v 4) (c-names-any? x later))
                       (r-module-closure g n x sc later)
                       (begin (r-exp g x (car sc) (cdr sc) #f) (the patches nil))))
               (kept (r-opn g rop-setstk s))
               (inner (the r-scopes (cons (r-bind n (rl-slot s) (car sc)) (r-local (cdr sc) n))))
               (waits (c-waits-onto ws s ps))
               (given (r-give-waiting g waits s)))
          (r-module-make g (cdr vs) inner (cdr later) waits
                         (if (= (extract v 3) 0) vals (the rints (cons s vals))))))))
;; A module: its items made in frame slots in order, as its stack code
;; makes them; then the product of its values. Declined in a leaf.
(define r-module (subr rcompiles (rgen mod-items renv cenv bool) unit)
  (lambda (g items env te tail)
    (if (extract g leaf)
        (r-decline)
        (let* ((slots (get (extract g nslot)))
               (vs (c-module-values items))
               (later (r-module-slots g vs))
               (vals (r-module-make g vs (the r-scopes (cons env te)) later nil nil)))
          (begin (r-make-frozen g 37 (r-slots-oldest vals nil) env te)
                 (set (extract g nslot) slots)
                 (r-done g tail))))))

;; Module `m`'s value into RESULT, from where `env` has it; declined if it
;; is not in a place.
(define r-module-value (subr rcompiles (rgen symbol renv) unit)
  (lambda (g m env)
    (let ((l (r-where env m)))
      (if (null? l)
          (r-decline)
          (tagcase (car l)
            (rl-reg (k) (r-opn g rop-reg k))
            (rl-slot (s) (r-opn g rop-stack s))
            (rl-free (i) (r-opn g rop-lexical i))
            (rl-global (c) (r-op1 g rop-global (wcell-global c)))
            (else y (r-decline)))))))
;; Module `m`'s values `ns`, by position from field `i`, each into its slot
;; of `at`: the scopes with them.
(define r-with-fields (subr rcompiles (rgen symbol syms rints int r-scopes) r-scopes)
  (lambda (g m ns at i sc)
    (if (null? ns)
        sc
        (begin
          (r-module-value g m (car sc))
          (r-opn g rop-field (+ i 2))
          (r-opn g rop-setstk (car at))
          (let ((inner (the r-scopes (cons (r-bind (car ns) (rl-slot (car at)) (car sc))
                                           (r-local (cdr sc) (car ns))))))
            (r-with-fields g m (cdr ns) (cdr at) (+ i 1) inner))))))
;; A frame slot for each of `ns`.
(define r-slots-for (subr (maxeff emits spin) (rgen syms) rints)
  (lambda (g ns)
    (if (null? ns) nil (let ((s (r-slot g))) (the rints (cons s (r-slots-for g (cdr ns))))))))
;; `with`: the module's values, by position, kept in frame slots; then the
;; body. Declined in a leaf.
(define r-with (subr rcompiles (rgen symbol exp int int renv cenv bool) unit)
  (lambda (g m body a b env te tail)
    (let ((ns (c-with-at a b)))
      (if (or (extract g leaf) (null? ns))
          (r-decline)
          (let* ((slots (get (extract g nslot)))
                 (at (r-slots-for g (car ns)))
                 (sc (r-with-fields g m (car ns) at 0 (the r-scopes (cons env te)))))
            (begin (r-exp g body (car sc) (cdr sc) tail) (set (extract g nslot) slots)))))))

(define r-module-or-with (subr rcompiles (rgen exp renv cenv bool) unit)
  (lambda (g x env te tail)
    (tagcase x
      (e-module (items a b) (r-module g items env te tail))
      (e-with (m body a b) (r-with g m body a b env te tail))
      (else y (r-decline)))))
(set r-module-code r-module-or-with)
;; `args` reversed, onto `acc`.
(define r-args-reversed (subr rbuilds (rargs rargs) rargs)
  (lambda (args acc)
    (if (null? args) acc (r-args-reversed (cdr args) (the rargs (cons (car args) acc))))))
;; A module reshaped (`k-reshape-at`): kept in a slot, its values the type
;; wanted has (by position `at`) into slots, and a product of them. Declined
;; in a leaf.
(define r-reshape-fields (subr rcompiles (rgen int k-ids rargs) rargs)
  (lambda (g m at args)
    (if (null? at)
        args
        (begin (r-opn g rop-stack m) (r-opn g rop-field (+ (car at) 2))
               (let ((s (r-keep-in-slot g)))
                 (r-reshape-fields g m (cdr at) (the rargs (cons (a-slot s) args))))))))
(define r-reshape (subr rcompiles (rgen exp k-ids renv cenv bool) unit)
  (lambda (g x at env te tail)
    (if (extract g leaf)
        (r-decline)
        (let* ((slots (get (extract g nslot)))
               (m (begin (r-exp-as-is g x env te #f) (r-keep-in-slot g)))
               (args (r-reshape-fields g m at nil)))
          (begin (r-make-frozen g 37 (r-args-reversed args nil) env te)
                 (set (extract g nslot) slots)
                 (r-done g tail))))))
(set r-reshape-code r-reshape)
