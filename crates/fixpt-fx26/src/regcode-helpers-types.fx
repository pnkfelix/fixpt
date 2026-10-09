;;; The types of `regcode-helpers.fx`, its `regcode-helpers-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define regcode-types (load-module "fx26:regcode-types.fx"))
(define-type rconst (select regcode-types rconst))
(define-type wcells (select regcode-types wcells))
(define compile-types (load-module "fx26:compile-types.fx"))
(define-type syms (select compile-types syms))
;; An expression, or none: a call's procedure (`r-args`), a closure's
;; region (`r-lambda`).
(define-type maybe-exp (listof exp @k))
;; A call unrolled over a constant list (`r-unrolled`, as the Rust
;; compiler's `r_unroll`, `TODO.md` §44): its procedure's expression, each
;; argument that is a global holding a constant list, with it (one that is
;; a constant here `r-known` finds), and the globals to guard. `r-inline`
;; compiles it, reading these (`r-known-arg`,
;; `r-guards-for`); newest first, as a call's arguments may hold others.
(define-type r-unroll-known (listof (pairof exp rconst @k) @k))
(define-type r-wglobals (listof wglobal @k))
(define-type r-unroll-found (productof (1 r-unroll-known) (2 r-wglobals) (3 bool)))
(define-type r-unroll-hook (productof (1 exp) (2 r-unroll-known) (3 r-wglobals)))
;; The global `a` names and its constant, if it is one.
(define-type r-unroll-globals (listof (pairof wglobal rconst @k) @k))
;; An expression split as `core + k` (`r-split`), and such a split, if any.
(define-type rsplit (productof (1 (listof exp @k)) (2 int)))
(define-type rsplits (listof rsplit @k))
;; A lambda's word, and the names it captures.
(define-type rmade (productof (1 tword) (2 syms)))
;; What `r-operands` makes of its second operand: an immediate, or the
;; register it is in, in a list.
(define-type roperands (productof (1 wcells) (2 (listof int @k))))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-programs.fx`).
;; The types it names, from the files that define them.
(define-type rgen (select regcode-types rgen))
;; The types it names, from the files that define them.
(define compile-exps-types (load-module "fx26:compile-exps-types.fx"))
(define-type c-spec (select compile-exps-types c-spec))
(define-type c-spec-copies (select compile-types c-spec-copies))
(define compile-plan-types (load-module "fx26:compile-plan-types.fx"))
(define-type c-special (select compile-plan-types c-special))
(define-type cenv (select compile-types cenv))
(define check-subst-types (load-module "fx26:check-subst-types.fx"))
(define-type exp-params (select check-subst-types exp-params))
(define-type exps (select compile-types exps))
(define-type patches (select compile-types patches))
(define-type rarg (select regcode-types rarg))
(define-type rargs (select regcode-types rargs))
(define-type rconsts (select regcode-types rconsts))
(define-type renv (select regcode-types renv))
(define regcode-exps-types (load-module "fx26:regcode-exps-types.fx"))
(define-type rinline (select regcode-exps-types rinline))
(define-type rlocs (select regcode-types rlocs))
(define-type regcode-helpers-sig
  (moduleof (val r-const-list? (subr pure (rconst) bool))
            (val r-op2imm
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (rgen int wcell)
                       unit))
            (val r-negate
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k)) (rgen) unit))
            (val r-known-slow
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin) (exp rconst) rarg))
            (val r-known-arg
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (renv exp)
                       rconsts))
            (val r-guards-for
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (rgen wglobal exp int)
                       bool))
            (val r-identity-arg
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (renv string exps)
                       (listof exp @k)))
            (val r-lifted-call-args
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (renv exp exps)
                       rargs))
            (val r-knowing
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (renv exp bool)
                       renv))
            (val r-split-app
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (renv string exps)
                       rsplits))
            (val r-inline-or-unroll
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (int int renv exp exps int)
                       (listof rinline @k)))
            (val r-just-exp (subr (alloc @k) (exp) maybe-exp))
            (val r-args-2 (subr (alloc @k) (rarg rarg) rargs))
            (val r-args-3 (subr (alloc @k) (rarg rarg rarg) rargs))
            (val r-make-array-ops (subr (maxeff (alloc @k) (read @globals)) (exps) rargs))
            (val r-const-value
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (rgen wcell bool)
                       unit))
            (val r-unit
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k)) (rgen) unit))
            (val r-add-imm
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (rgen int)
                       unit))
            (val r-index-field
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k)) (rgen) unit))
            (val r-restore (subr (maxeff (read @k) (write @k)) (rgen int int) unit))
            (val r-var-value
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (rgen rlocs symbol bool)
                       unit))
            (val r-fx-value
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (rgen symbol exp bool)
                       unit))
            (val r-literal? (subr pure (exp) bool))
            (val r-free-operand?
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin) (renv exp) bool))
            (val r-deeper?
                 (subr (maxeff (read @globals) (read @k)) (maybe-exp exp exp) bool))
            (val r-lifted-closure
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin) (int) wcell))
            (val r-unknowing
                 (subr (maxeff (alloc @k) (read @globals) (read @k)) (rgen) rgen))
            (val r-spec-of
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (c-special wglobal exp-params exp cenv)
                       c-spec))
            (val r-spec-word
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (c-special c-spec exp)
                       c-spec-copies))
            (val r-free-into-regs
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (rgen syms renv)
                       patches))
            (val r-collects-here?
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (rgen exp cenv bool)
                       bool))
            (val r-spec-body-collects?
                 (subr (maxeff (alloc @k)
                               (goto @y)
                               (read @globals)
                               (read @k)
                               (read @t)
                               (write @k)
                               spin)
                       (rgen c-spec bool)
                       bool))
            (val r-imm-operand (subr (alloc @k) (wcells) roperands))
            (val r-reg-operand (subr (alloc @k) (int) roperands))
            (val r-known-cell
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin) (renv exp) wcells))))
