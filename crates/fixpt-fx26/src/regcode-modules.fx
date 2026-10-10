;;; Register code, in FX-26: modules' helpers (`docs/research/first-class-modules.md`,
;;; stage M3); the module code itself is in `regcode-core.fx`'s group, which
;;; it recurs with. After `regcode-helpers.fx`.

;; Its types, those it uses of the files before it, and the signatures of
;; what it is given.
(let* ((regcode-modules-types (load-module "fx26:regcode-modules-types.fx"))
       (regcode-types (load-module "fx26:regcode-types.fx"))
       (compile-types (load-module "fx26:compile-types.fx"))
       (compile-exps-types (load-module "fx26:compile-exps-types.fx"))
       (parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
       (check-types-types (load-module "fx26:check-types-types.fx"))
       (layout-types (load-module "fx26:layout-types.fx"))
       (regcode-exps-types (load-module "fx26:regcode-exps-types.fx")))
  ;; What it is given: the modules of the files before it that it uses.
  (lambda ((regcode (select regcode-types regcode-sig))
           (compile (select compile-types compile-sig))
           (layout (select layout-types layout-sig))
           (regcode-exps (select regcode-exps-types regcode-exps-sig)))
    (module
(define-type r-scopes (select regcode-modules-types r-scopes))
;; The types it uses of the files before it.
(define a-slot (with regcode-types a-slot))
(define-effect emits (select regcode-types emits))
(define-type r-member-const (select regcode-types r-member-const))
(define-type rargs (select regcode-types rargs))
(define-effect rbuilds (select regcode-types rbuilds))
(define-effect rcompiles (select regcode-types rcompiles))
(define-type rconsts (select regcode-types rconsts))
(define-type renv (select regcode-types renv))
(define-type rgen (select regcode-types rgen))
(define-type rints (select regcode-types rints))
(define rl-const (with regcode-types rl-const))
(define rl-free (with regcode-types rl-free))
(define rl-global (with regcode-types rl-global))
(define rl-loop (with regcode-types rl-loop))
(define rl-pending (with regcode-types rl-pending))
(define rl-reg (with regcode-types rl-reg))
(define rl-slot (with regcode-types rl-slot))
(define at-loop (with compile-types at-loop))
(define at-pending (with compile-types at-pending))
(define-type cenv (select compile-types cenv))
(define-type syms (select compile-types syms))
(define-type c-mslots (select compile-exps-types c-mslots))
(define-type c-mvals (select compile-exps-types c-mvals))
(define-type c-waits (select compile-exps-types c-waits))
(define-type exp (select parser-types exp))
(define-type k-ids (select check-types-types k-ids))
;; What it uses of the modules it is given.
(define r-bind (with regcode r-bind))
(define r-decline (with regcode r-decline))
(define r-local (with regcode r-local))
(define r-member-const (with regcode r-member-const))
(define r-op1 (with regcode r-op1))
(define r-opn (with regcode r-opn))
(define r-opnn (with regcode r-opnn))
(define r-slot (with regcode r-slot))
(define r-where (with regcode r-where))
(define c-loops-only (with compile c-loops-only))
(define cellular-closure-free0 (with layout cellular-closure-free0))
(define rop-field (with layout rop-field))
(define rop-global (with layout rop-global))
(define rop-lexical (with layout rop-lexical))
(define rop-load (with layout rop-load))
(define rop-reg (with layout rop-reg))
(define rop-setfield (with layout rop-setfield))
(define rop-stack (with layout rop-stack))
(define r-assume (with regcode-exps r-assume))
(define r-keep (with regcode-exps r-keep))
(define r-keep-in-slot (with regcode-exps r-keep-in-slot))

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
;; Field `p` of the module in the accumulator: from 2^40 on, a path
;; (`k-reshape-path`), value `j` of the module that is its value `k`.
(define r-reshape-field (subr rcompiles (rgen int) unit)
  (lambda (g p)
    (if (< p 1099511627776)
        (r-opn g rop-field (+ p 2))
        (let ((q (- p 1099511627776)))
          (begin (r-opn g rop-field (+ (quotient q 1048576) 2))
                 (r-opn g rop-field (+ (remainder q 1048576) 2)))))))
(define r-reshape-fields (subr rcompiles (rgen int k-ids rargs) rargs)
  (lambda (g m at args)
    (if (null? at)
        args
        (begin (r-opn g rop-stack m) (r-reshape-field g (car at))
               (let ((s (r-keep-in-slot g)))
                 (r-reshape-fields g m (cdr at) (the rargs (cons (a-slot s) args)))))))))))
