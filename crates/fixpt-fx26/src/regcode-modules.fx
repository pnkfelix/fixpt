;;; Register code, in FX-26: modules' helpers (`docs/research/first-class-modules.md`,
;;; stage M3); the module code itself is in `regcode-core.fx`'s group, which
;;; it recurs with. After `regcode-helpers.fx`.

;; Its types (`regcode-modules-types.fx`), loaded before the module so that they are
;; not among its values; the module names what it uses of them.
(define regcode-modules-types (load-module "fx26:regcode-modules-types.fx"))
;; A module (`TODO.md` §34: the front end into modules, a file at a time);
;; what other files use re-exported after it.
(define regcode-modules-module (module
(define-type r-scopes (select regcode-modules-types r-scopes))


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
;; Module `m`'s values `ns`, at positions `ps`, each into its slot of `at`:
;; the scopes with them.
(define r-with-fields (subr rcompiles (rgen symbol renv syms k-ids r-scopes) r-scopes)
  (lambda (g m env ns ps sc)
    (if (or (null? ns) (null? ps))
        sc
        (let* ((k (r-with-folded m env (car ns)))
               (l (if (null? k)
                      (begin (r-module-value g m env)
                             (r-opn g rop-field (+ (car ps) 2))
                             (r-keep g (extract g leaf)))
                      (rl-const (car k))))
               (inner (the r-scopes
                        (cons (r-bind (car ns) l (car sc)) (r-local (cdr sc) (car ns))))))
          (r-with-fields g m env (cdr ns) (cdr ps) inner)))))
;; In a fast version, member `n` of module `m`, a global's whose literal
;; members were noted: its literal, in a list, the global assumed; else
;; none (`TODO.md` §42).
(define r-with-folded (subr rcompiles (symbol renv symbol) rconsts)
  (lambda (m env n)
    (let ((l (r-where env m)))
      (if (null? l)
          nil
          (tagcase (car l)
            (rl-global (c)
              (let ((k (r-member-const c n)))
                (if (and (not (null? k)) (r-assume c)) k nil)))
            (else y nil))))))

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
                 (r-reshape-fields g m (cdr at) (the rargs (cons (a-slot s) args))))))))))

(define-type r-scopes (select regcode-modules-module r-scopes))
(define r-slots-oldest (with regcode-modules-module r-slots-oldest))
(define r-module-slots (with regcode-modules-module r-module-slots))
(define r-module-own (with regcode-modules-module r-module-own))
(define r-give-waiting (with regcode-modules-module r-give-waiting))
(define r-with-fields (with regcode-modules-module r-with-fields))
(define r-args-reversed (with regcode-modules-module r-args-reversed))
(define r-reshape-fields (with regcode-modules-module r-reshape-fields))
