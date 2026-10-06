;;; Register code, in FX-26: modules' helpers (`docs/research/first-class-modules.md`,
;;; stage M3); the module code itself is in `regcode-core.fx`'s group, which
;;; it recurs with. After `regcode-helpers.fx`.

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
